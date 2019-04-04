From stbor Require Export lang notation.

(** Wellformedness *)
Class Wellformed A := Wf : A → Prop.
Existing Class Wf.

Definition wf_mem_bor (h: mem) (clock: time) :=
  ∀ l l' bor, h !! l = Some (LitV (LitLoc l' bor)) → bor <b clock.

Definition frozen_lt (stk: bstack) (clk: time) :=
  match frozen_since stk with
  | Some t => (t < clk)%nat
  | None => True
  end.
Definition wf_stack_frozen (α: bstacks) (clock: time) :=
  ∀ l stack, α !! l = Some stack → frozen_lt stack clock.

Definition stack_item_included (stk: bstack) (β: barriers) (clock: time) :=
  ∀ si, si ∈ stk.(borrows) → match si with
                              | Uniq t => (t < clock)%nat
                              | FnBarrier c => is_Some (β !! c)
                              | _ => True
                              end.
Definition wf_stack_item (α: bstacks) (β: barriers) (clock: time) :=
  ∀ l stack, α !! l = Some stack → stack_item_included stack β clock.
Definition borrow_barrier_Some (β: barriers) kind : Prop :=
  match kind with FnEntry c => is_Some (β !! c) | _ => True end.
Definition wf_non_empty (α: bstacks) :=
   ∀ l stack, α !! l = Some stack → stack.(borrows) ≠ [].

Record state_wf' σ := {
  state_wf_dom : dom (gset loc) σ.(cheap) ≡ dom (gset loc) σ.(cstk);
  state_wf_mem_bor : wf_mem_bor σ.(cheap) σ.(cclk);
  state_wf_stack_frozen : wf_stack_frozen σ.(cstk) σ.(cclk);
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

(** Thread steps *)
(* TODO: we are ignoring fork *)
(* τ-step has no observation. *)
Inductive thread_τstep (eσ1 eσ2: expr * state) : Prop :=
| ThreadTauStep (STEP: prim_step eσ1.1 eσ1.2 [] eσ2.1 eσ2.2 []).
(* One true step can be led by some τ-steps. *)
Inductive thread_onestep eσ1 o eσ2 : Prop :=
| ThreadOneStep eσ1'
    (TAU_STEP: rtc thread_τstep eσ1 eσ1')
    (ONE_STEP: prim_step eσ1'.1 eσ1'.2 [o] eσ2.1 eσ2.2 []).

(** Configuration (threadpool) steps *)
(* This duplicates iris.program_logic.language in order to expose a thread id *)
Inductive step ρ1 tid κ ρ2 : Prop :=
| StepAtomic e1 σ1 e2 σ2 efs t1 t2 :
   ρ1 = (t1 ++ e1 :: t2, σ1) →
   ρ2 = (t1 ++ e2 :: t2 ++ efs, σ2) →
   prim_step e1 σ1 κ e2 σ2 efs →
   tid = length t1 →
   step ρ1 tid κ ρ2.

(* τ-step has no observation and ignore tid. *)
Inductive τstep ρ1 ρ2 : Prop :=
| CfgTauStep tid (STEP: step ρ1 tid [] ρ2).
(* One true step can be led by some τ-steps. *)
Inductive one_step ρ1 tid o ρ2 : Prop :=
| CfgOneStep ρ1' (TAU_STEP: rtc τstep ρ1 ρ1') (ONE_STEP: step ρ1' tid [o] ρ2).

(** Future states,  by interference *)
(* TODO: fix this *)
Definition future_state : relation state := λ σ1 σ2, σ1 = σ2.
(** State simulation *)
(* TODO: fix this *)
Definition sim_state : relation state := λ σ1 σ2, σ1 = σ2.
