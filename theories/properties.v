From stbor Require Export lang notation.

(** Wellformedness *)
Class Wellformed A := Wf : A → Prop.
Existing Class Wf.

Definition wf_mem_bor (h: mem) (clk: ptr_id) :=
  ∀ l l' bor, h !! l = Some (LitV (LitLoc l' bor)) → bor <b clk.

Definition stack_item_included (stk: stack) (β: protectors) (clk: ptr_id) :=
  ∀ si, si ∈ stk → match si.(tg) with
                    | Tagged t => (t < clk)%nat
                    | _ => True
                   end ∧
                   match si.(protector) with
                    | Some c =>is_Some (β !! c)
                    | _ => True
                   end.
Definition wf_stack_item (α: stacks) (β: protectors) (clk: ptr_id) :=
  ∀ l stk, α !! l = Some stk → stack_item_included stk β clk.
Definition wf_non_empty (α: stacks) :=
   ∀ l stk, α !! l = Some stk → stk ≠ [].

Definition borrow_barrier_Some (β: protectors) kind : Prop :=
  match kind with FnEntry c => is_Some (β !! c) | _ => True end.

Record state_wf' σ := {
  state_wf_dom : dom (gset loc) σ.(cheap) ≡ dom (gset loc) σ.(cstk);
  state_wf_mem_bor : wf_mem_bor σ.(cheap) σ.(cclk);
  state_wf_stack_item : wf_stack_item σ.(cstk) σ.(cbar) σ.(cclk);
  state_wf_non_empty : wf_non_empty σ.(cstk);
}.

Instance state_wf : Wellformed state :=  state_wf'.

Implicit Type (ρ: cfg bor_lang).

(* TODO: this may need strengthening *)
Definition cfg_wf' ρ : Prop := Wf ρ.2.
Instance cfg_wf : Wellformed (cfg bor_lang) :=  cfg_wf'.

(** Terminal states *)
Class Terminal A := terminal : A → Prop.
Existing Class terminal.

Definition epxr_terminal' (e: expr) : Prop := is_Some (to_val e).
Instance expr_terminal : Terminal expr := epxr_terminal'.
Definition threads_terminal' (el: list expr) := ∀ e, e ∈ el → terminal e.
Instance threads_terminal : Terminal (list expr) := threads_terminal'.
Definition cfg_terminal' ρ : Prop := terminal ρ.1.
Instance cfg_terminal : Terminal (cfg bor_lang) := cfg_terminal'.

Definition external (ev: event) : option event :=
  match ev with
  | SysCallEvt id => Some (SysCallEvt id)
  | _ => None
  end.
Definition externally_equiv : relation event :=
  λ ev1 ev2, external ev1 = external ev2.

(** Thread steps *)
Definition thread_step (eσ1: expr * state) (ev: event) (eσ2: expr * state) efs
  : Prop := prim_step eσ1.1 eσ1.2 [ev] eσ2.1 eσ2.2 efs.
(* τ-step has no external observation. *)
Inductive thread_τstep (eσ1 eσ2: expr * state) : Prop :=
| ThreadTauStep ev efs
    (INTERNAL: external ev = None)
    (STEP: thread_step eσ1 ev eσ2 efs).
(* One step can be led by some τ-steps. ev can be either observable or not. *)
Inductive thread_1step eσ1 ev eσ2 : Prop :=
| Thread1Step eσ1' efs
    (TAU_STEP: rtc thread_τstep eσ1 eσ1')
    (ONE_STEP: thread_step eσ1' ev eσ2 efs).

(** Configuration (threadpool) steps *)
(* This duplicates iris.program_logic.language in order to expose a thread id *)
Inductive step ρ1 tid ev ρ2 : Prop :=
| StepAtomic e1 σ1 e2 σ2 efs t1 t2 :
   ρ1 = (t1 ++ e1 :: t2, σ1) →
   ρ2 = (t1 ++ e2 :: t2 ++ efs, σ2) →
   thread_step (e1, σ1) ev (e2, σ2) efs →
   tid = length t1 →
   step ρ1 tid ev ρ2.

(* τ-step has no external observation and ignore tid. *)
Inductive τstep ρ1 ρ2 : Prop :=
| CfgTauStep tid ev
    (INTERNAL: external ev = None)
    (STEP: step ρ1 tid ev ρ2).
(* One step can be led by some τ-steps. ev can be either observable or not. *)
Inductive one_step ρ1 tid ev ρ2 : Prop :=
| CfgOneStep ρ1'
    (TAU_STEP: rtc τstep ρ1 ρ1')
    (ONE_STEP: step ρ1' tid ev ρ2).

(** Future states,  by interference *)
(* TODO: fix this *)
Definition future_state : relation state := λ σ1 σ2, σ1 = σ2.
(** State simulation *)
(* TODO: fix this *)

Definition sim_immediate (v1 v2: immediate) :=
  match v1, v2 with
  | RecV _ _ _, RecV _ _ _ => v1 = v2
  | LitV LitPoison, LitV LitPoison => True
  | LitV (LitInt n1), LitV (LitInt n2) => n1 = n2
  | LitV (LitLoc l1 bor1), LitV (LitLoc l2 bor2) => l1 = l2
  | _,_ => False
  end.

Record sim_state (σ_src σ_tgt: state) := {
  sim_state_mem_dom : dom (gset loc) σ_src.(cheap) ≡ dom (gset loc) σ_tgt.(cheap);
  sim_state_stack_dom : dom (gset loc) σ_src.(cstk) ≡ dom (gset loc) σ_tgt.(cstk);
  sim_state_protectors : σ_src.(cbar) = σ_tgt.(cbar);
  sim_state_mem : ∀ l v1 v2,
    σ_src.(cheap) !! l = Some v1 → σ_tgt.(cheap) !! l = Some v2 → sim_immediate v1 v2;
}.
