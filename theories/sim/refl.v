From stbor.lang Require Import lang.
From stbor.sim Require Import refl_step.

Set Default Proof Using "Type".

(** Enable use of [Forall] in recursion. *)
Lemma Forall_id {A: Type} (P: A → Prop) (l: list A) :
  Forall P l ↔ Forall id (map P l).
Proof.
  induction l; simpl; first by eauto using Forall_nil.
  split; intros [??]%Forall_cons_1; apply Forall_cons; simpl; tauto.
Qed.

(** "Well-formed" code doen't contain literal
pointers, places or administrative operations (init_call/end_call).
Defined by recursion to make sure we don't miss a case. *)
Definition scalar_wf (a: scalar) : Prop :=
  match a with
  | ScPoison | ScInt _ | ScFnPtr _ => True
  | ScnPtr => False
  end.
Definition value_wf (v: value) : Prop := Forall scalar_wf v.
Fixpoint expr_wf (e: expr) : Prop :=
  match e with
  (* Structural cases. *)
  | Val v => value_wf v
  | Call f args => expr_wf f ∧ Forall id (map expr_wf args)
  | Case e branches => expr_wf e ∧ Forall id (map expr_wf branches)
  | Var _ | Alloc _ => True
  | Deref e _ | Ref e  | Copy e | Retag e _ =>
    expr_wf e
  | Proj e1 e2 | Conc e1 e2 | BinOp _ e1 e2 | Let _ e1 e2 | Write e1 e2 =>
    expr_wf e1 ∧ expr_wf e2
  (* Forbidden cases. *)
  | InitCall e | EndCall e => False
  | Place _ _ _ => False
  | Free _ => False (* TODO: We'd like to support deallocation! *)
  end.
Definition prog_wf (prog: fn_env) :=
  has_main prog ∧
  map_Forall (λ _ f, expr_wf f.(fun_body)) prog.

Theorem sim_mod_fun_refl f :
  expr_wf f.(fun_body) →
  ⊨ᶠ f ≥ f.
Proof.
Admitted.

Lemma sim_mod_funs_refl prog :
  prog_wf prog →
  sim_mod_funs prog prog.
Proof.
  intros [_ WF]. induction prog using map_ind.
  { intros ??. rewrite lookup_empty. done. }
  apply sim_mod_funs_insert; first done.
  - apply sim_mod_fun_refl. eapply WF. erewrite lookup_insert. done.
  - apply IHprog. eapply map_Forall_insert_12; done.
Qed.
