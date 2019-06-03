Require Import Coq.Program.Equality.
From stbor Require Export properties steps_wf.

Ltac inv_head_step :=
  repeat match goal with
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : _ = of_val ?v |- _ =>
     is_var v; destruct v; first[discriminate H|injection H as H]
  | H : head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H ; subst; clear H
  end.

(** BinOp *)

Lemma fill_bin_op_decompose K e op e1 e2:
  fill K e = BinOp op e1 e2 →
  K = [] ∧ e = BinOp op e1 e2 ∨
  (∃ K', K = K' ++ [BinOpLCtx op e2] ∧ fill K' e = e1) ∨
  (∃ v1 K', K = K' ++ [BinOpRCtx op v1] ∧ fill K' e = e2 ∧ to_val e1 = Some v1).
Proof.
  revert e e1 e2.
  induction K as [|Ki K IH]; [by left|]. simpl.
  intros e e1 e2 EqK. right.
  destruct (IH _ _ _ EqK) as [[? _]|[[K0 [? Eq0]]|[v1 [K' [? Eq']]]]].
  - subst. simpl in *. destruct Ki; try done.
    + simpl in EqK. simplify_eq. left. exists []. naive_solver.
    + right. simpl in EqK. inversion EqK; subst.
      exists v1, []. naive_solver eauto using to_of_val.
  - subst K. left. by exists (Ki :: K0).
  - subst K. right. by exists v1, (Ki :: K').
Qed.

Lemma thread_step_bin_op_left_non_terminal op e1 e2 e' σ σ'
  (STEP: (BinOp op e1 e2, σ) ~t~> (e', σ'))
  (NT: ¬ terminal e1):
  ∃ e1', (e1, σ) ~t~> (e1', σ') ∧ e' = BinOp op e1' e2.
Proof.
  inversion_clear STEP; simpl in PRIM.
  inversion_clear PRIM as [??? Eq1 ? HS]. subst.
  have Eq: BinOp op e1 e2 = ectx_language.fill [BinOpLCtx op e2] e1 by done.
  rewrite Eq in Eq1.
  apply expr_terminal_False in NT.
  destruct (step_by_val _ _ _ _ _ _ _ _ _ Eq1 NT HS) as [K'' Eq'].
  rewrite Eq' -fill_comp in Eq1.
  have Eq'' := fill_inj _ _ _ Eq1.
  eexists. split.
  - econstructor. econstructor; [exact Eq''|..|exact HS]. eauto.
  - by rewrite Eq' -fill_comp.
Qed.

Lemma thread_step_bin_op_right_non_terminal op e1 e2 e' σ σ'
  (STEP: (BinOp op e1 e2, σ) ~t~> (e', σ'))
  (TM: terminal e1) (NT: ¬ terminal e2):
  ∃ e2', (e2, σ) ~t~> (e2', σ') ∧ e' = BinOp op e1 e2'.
Proof.
  inversion_clear STEP; simpl in PRIM.
  inversion_clear PRIM as [??? Eq1 ? HS]. subst.
  move : TM => /expr_terminal_True [v1 Eqv1].
  have Eq: BinOp op e1 e2 = ectx_language.fill [BinOpRCtx op v1] e2.
  { by rewrite /= -(of_to_val _ _ Eqv1). }
  rewrite Eq in Eq1.
  apply expr_terminal_False in NT.
  destruct (step_by_val _ _ _ _ _ _ _ _ _ Eq1 NT HS) as [K'' Eq'].
  rewrite Eq' -fill_comp in Eq1.
  have Eq'' := fill_inj _ _ _ Eq1.
  eexists. split.
  - econstructor. econstructor; [exact Eq''|..|exact HS]. eauto.
  - by rewrite Eq' -fill_comp -(of_to_val _ _ Eqv1) /=.
Qed.

Lemma thread_step_bin_op_terminal op e1 e2 e' σ σ'
  (STEP: (BinOp op e1 e2, σ) ~t~> (e', σ'))
  (TM1: terminal e1) (TM2: terminal e2):
  σ' = σ ∧ ∃ l1 l2 l, bin_op_eval σ.(cheap) op l1 l2 l ∧ e' = (TVal [Lit l]).
Proof.
  inversion_clear STEP; simpl in PRIM.
  inversion_clear PRIM as [??? Eq1 ? HS]. subst.
  symmetry in Eq1.
  destruct (fill_bin_op_decompose _ _ _ _ _ Eq1)
    as [[]|[[K' [? Eq']]|[v1 [K' [? [Eq' VAL]]]]]]; subst.
  - clear Eq1. simpl in HS. inv_head_step.
    inversion BaseStep; subst. inversion InstrStep; subst.
    split; [by destruct σ|]. simpl. naive_solver.
  - apply fill_val in TM1. apply val_head_stuck in HS.
    rewrite /= HS in TM1. by destruct TM1.
  - apply fill_val in TM2. apply val_head_stuck in HS.
    rewrite /= HS in TM2. by destruct TM2.
Qed.

Lemma thread_step_bin_op_red_r e1 σ1 e2 e2' σ2 op:
  terminal e1 →
  (e2, σ1) ~t~>* (e2', σ2) →
  (BinOp op e1 e2, σ1) ~t~>* (BinOp op e1 e2', σ2).
Proof.
  intros T1 S2.
  dependent induction S2 generalizing e2 σ1; first by constructor.
  destruct y as [e0 σ0].
  etrans; last apply IHS2; [|eauto..]. apply rtc_once.
  clear -H T1.
  move : T1 => /expr_terminal_True [v1 Eqv1].
  rewrite (_: BinOp op e1 e2 = ectx_language.fill [BinOpRCtx op v1] e2);
    last by rewrite /= -(of_to_val _ _ Eqv1).
  rewrite (_: BinOp op e1 e0 = ectx_language.fill [BinOpRCtx op v1] e0);
    last by rewrite /= -(of_to_val _ _ Eqv1).
  inversion_clear H; simpl in PRIM.
  inversion_clear PRIM. subst.
  rewrite 2!fill_comp.
  econstructor. econstructor; eauto.
Qed.

Lemma thread_step_bin_op_red_l e1 σ1 e1' σ1' e2 op:
  (e1, σ1) ~t~>* (e1', σ1') →
  (BinOp op e1 e2, σ1) ~t~>* (BinOp op e1' e2, σ1').
Proof.
  intros S1.
  dependent induction S1 generalizing e1 σ1 e2; first by constructor.
  destruct y as [e0 σ0].
  etrans; last apply IHS1; [|eauto..]. apply rtc_once.
  clear -H.
  rewrite (_: BinOp op e1 e2 = ectx_language.fill [BinOpLCtx op e2] e1);
    last done.
  rewrite (_: BinOp op e0 e2 = ectx_language.fill [BinOpLCtx op e2] e0);
    last done.
  inversion_clear H; simpl in PRIM.
  inversion_clear PRIM. subst.
  rewrite 2!fill_comp.
  econstructor. econstructor; eauto.
Qed.

Lemma thread_step_bin_op_red e1 σ1 e1' σ1' e2 e2' σ2' op:
  (e1, σ1) ~t~>* (e1', σ1') → terminal e1' →
  (e2, σ1') ~t~>* (e2', σ2') →
  (BinOp op e1 e2, σ1) ~t~>* (BinOp op e1' e2', σ2').
Proof.
  intros S1 T1 S2. etrans.
  - clear S2 T1. by eapply thread_step_bin_op_red_l.
  - clear S1. by eapply thread_step_bin_op_red_r.
Qed.
