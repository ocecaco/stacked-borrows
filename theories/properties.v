From stbor Require Export lang.

Set Default Proof Using "Type".

(** Wellformedness *)
Class Wellformed A := Wf : A → Prop.
Existing Class Wf.

Definition wf_mem_tag (h: mem) (clk: ptr_id) :=
  ∀ l l' bor, h !! l = Some (LitLoc l' bor) → bor <b clk.

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
Definition wf_no_dup (α: stacks) :=
  ∀ l stk, α !! l = Some stk → NoDup stk.

Definition borrow_barrier_Some (β: protectors) kind : Prop :=
  match kind with FnEntry c => is_Some (β !! c) | _ => True end.

Record state_wf' (s: state) := {
  state_wf_dom : dom (gset loc) s.(shp) ≡ dom (gset loc) s.(sst);
  state_wf_mem_tag : wf_mem_tag s.(shp) s.(scn);
  state_wf_stack_item : wf_stack_item s.(sst) s.(spr) s.(scn);
  state_wf_non_empty : wf_non_empty s.(sst);
  (* state_wf_no_dup : wf_no_dup σ.(cst).(sst); *)
}.

Instance state_wf : Wellformed state :=  state_wf'.
Instance config_wf : Wellformed config := λ cfg, Wf cfg.(cst).
Notation terminal e := (is_Some (to_val e)).

Lemma expr_terminal_False (e: expr) : ¬ terminal e ↔ to_val e = None.
Proof.
  split.
  - destruct (to_val e) eqn:Eqv; [|done].
    intros TERM. exfalso. apply TERM. by eexists.
  - intros Eq1 [? Eq2]. by rewrite Eq1 in Eq2.
Qed.

(** Thread steps *)
Inductive tstep (eσ1 eσ2 : expr * config) : Prop :=
| ThreadStep ev efs
    (PRIM: prim_step eσ1.1 eσ1.2 ev eσ2.1 eσ2.2 efs)
.

Infix "~t~>" := tstep (at level 70).
Infix "~t~>*" := (rtc tstep) (at level 70).

(*=================================== UNUSED =================================*)
(* Implicit Type (ρ: cfg bor_lang). *)

(* TODO: this may need strengthening *)
(* Definition cfg_wf' ρ : Prop := Wf ρ.2. *)
(* Instance cfg_wf : Wellformed (cfg bor_lang) :=  cfg_wf'. *)

(* Definition threads_terminal' (el: list expr) := ∀ e, e ∈ el → terminal e. *)
(* Instance threads_terminal : Terminal (list expr) := threads_terminal'. *)
(* Definition cfg_terminal' ρ : Prop := terminal ρ.1. *)
(* Instance cfg_terminal : Terminal (cfg bor_lang) := cfg_terminal'. *)
