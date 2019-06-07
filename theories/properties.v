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

Record state_wf' σ := {
  state_wf_dom : dom (gset loc) σ.(cheap) ≡ dom (gset loc) σ.(cstk);
  state_wf_mem_tag : wf_mem_tag σ.(cheap) σ.(cclk);
  state_wf_stack_item : wf_stack_item σ.(cstk) σ.(cpro) σ.(cclk);
  state_wf_non_empty : wf_non_empty σ.(cstk);
  (* state_wf_no_dup : wf_no_dup σ.(cstk); *)
}.

Instance state_wf : Wellformed state :=  state_wf'.

Notation terminal e := (is_Some (to_val e)).

Lemma expr_terminal_False (e: expr) : ¬ terminal e ↔ to_val e = None.
Proof.
  split.
  - destruct (to_val e) eqn:Eqv; [|done].
    intros TERM. exfalso. apply TERM. by eexists.
  - intros Eq1 [? Eq2]. by rewrite Eq1 in Eq2.
Qed.

(** Thread steps *)
Inductive tstep (eσ1 eσ2 : expr * state) : Prop :=
| ThreadStep ev efs
    (PRIM: prim_step eσ1.1 eσ1.2 ev eσ2.1 eσ2.2 efs)
.

Infix "~t~>" := tstep (at level 70).
Infix "~t~>*" := (rtc tstep) (at level 70).

(** Behaviors ----------------------------------------------------------------*)

CoInductive diverges
  (step: expr * state → expr * state → Prop)
  (cfg: expr * state) : Prop :=
| DivergeStep cfg' (STEP: step cfg cfg') (DIV: diverges step cfg') .

Inductive behavior := | Term (v: val) | Stuck | Diverges.

Inductive behaviors
  (step: expr * state → expr * state → Prop)
  (cfg: expr * state) : behavior → Prop :=
| behaviors_term v
    (TERMINAL: to_val cfg.1 = Some v) :
    behaviors step cfg (Term v)
| behaviors_stuck
    (NT: ¬ terminal cfg.1)
    (NS: ∀ cfg', ¬ step cfg cfg') :
    behaviors step cfg Stuck
| behaviors_diverges
    (DIV: diverges step cfg) :
    behaviors step cfg Diverges
| behaviors_step cfg' ov
    (STEP: step cfg cfg')
    (NEXT: behaviors step cfg' ov):
    behaviors step cfg ov
.

(*=================================== UNUSED =================================*)
Implicit Type (ρ: cfg bor_lang).

(* TODO: this may need strengthening *)
Definition cfg_wf' ρ : Prop := Wf ρ.2.
Instance cfg_wf : Wellformed (cfg bor_lang) :=  cfg_wf'.

Definition threads_terminal' (el: list expr) := ∀ e, e ∈ el → terminal e.
(* Instance threads_terminal : Terminal (list expr) := threads_terminal'. *)
(* Definition cfg_terminal' ρ : Prop := terminal ρ.1. *)
(* Instance cfg_terminal : Terminal (cfg bor_lang) := cfg_terminal'. *)
