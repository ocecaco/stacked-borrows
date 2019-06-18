Require Import Coq.Program.Equality.

From stbor.lang Require Export defs steps_wf.

Set Default Proof Using "Type".

Ltac inv_head_step :=
  repeat match goal with
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : _ = of_val ?v |- _ =>
     is_var v; destruct v; first[discriminate H|injection H as H]
  | H : head_step _ ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H ; subst; clear H
  | H : mem_expr_step _ _ _ _ _ |- _ =>
      inversion H ; subst; clear H
  end.

Ltac inv_tstep :=
  repeat match goal with
  | H : tstep _ _ _ |- _ => inversion_clear H
  | H : prim_step _ _ _ _ _ _ |- _ =>
      simpl in H; inversion_clear H as [??? Eq ? HS]; subst
  end.

Section inv.
Variable (fns: fn_env).
Implicit Type (e: ectx_language.expr (bor_ectx_lang fns)).
(** InitCall *)

(** BinOp *)

Lemma fill_bin_op_decompose K e op e1 e2:
  fill K e = BinOp op e1 e2 →
  K = [] ∧ e = BinOp op e1 e2 ∨
  (∃ K', K = K' ++ [BinOpLCtx op e2] ∧ fill K' e = e1) ∨
  (∃ v1 K', K = K' ++ [BinOpRCtx op v1] ∧ fill K' e = e2 ∧ to_result e1 = Some v1).
Proof.
  revert e e1 e2.
  induction K as [|Ki K IH]; [by left|]. simpl.
  intros e e1 e2 EqK. right.
  destruct (IH _ _ _ EqK) as [[? _]|[[K0 [? Eq0]]|[r1 [K' [? Eq']]]]].
  - subst. simpl in *. destruct Ki; try done.
    + simpl in EqK. simplify_eq. left. exists []. naive_solver.
    + right. simpl in EqK. inversion EqK; subst.
      exists r1, []. naive_solver eauto using to_of_result.
  - subst K. left. by exists (Ki :: K0).
  - subst K. right. by exists r1, (Ki :: K').
Qed.

Lemma tstep_bin_op_left_non_terminal op e1 e2 e' σ σ'
  (STEP: (BinOp op e1 e2, σ) ~{fns}~> (e', σ'))
  (NT: ¬ terminal e1):
  ∃ e1', (e1, σ) ~{fns}~> (e1', σ') ∧ e' = BinOp op e1' e2.
Proof.
  inv_tstep.
  have Eq1: BinOp op e1 e2 = ectx_language.fill [BinOpLCtx op e2] e1 by done.
  rewrite Eq1 in Eq.
  apply expr_terminal_False in NT.
  destruct (step_by_val _ _ _ _ _ _ _ _ _ Eq NT HS) as [K'' Eq'].
  rewrite Eq' -fill_comp in Eq.
  have Eq'' := fill_inj _ _ _ Eq.
  eexists. split.
  - econstructor. econstructor; [exact Eq''|..|exact HS]. eauto.
  - by rewrite Eq' -fill_comp.
Qed.

Lemma tstep_bin_op_right_non_terminal op e1 e2 e' σ σ'
  (STEP: (BinOp op e1 e2, σ) ~{fns}~> (e', σ'))
  (TM: terminal e1) (NT: ¬ terminal e2):
  ∃ e2', (e2, σ) ~{fns}~> (e2', σ') ∧ e' = BinOp op e1 e2'.
Proof.
  inv_tstep.
  move : TM => [v1 Eqv1].
  have Eq1: BinOp op e1 e2 = ectx_language.fill [BinOpRCtx op v1] e2.
  { by rewrite /= -(of_to_result _ _ Eqv1). }
  rewrite Eq1 in Eq.
  apply expr_terminal_False in NT.
  destruct (step_by_val _ _ _ _ _ _ _ _ _ Eq NT HS) as [K'' Eq'].
  rewrite Eq' -fill_comp in Eq.
  have Eq'' := fill_inj _ _ _ Eq.
  eexists. split.
  - econstructor. econstructor; [exact Eq''|..|exact HS]. eauto.
  - by rewrite Eq' -fill_comp -(of_to_result _ _ Eqv1) /=.
Qed.

Lemma tstep_bin_op_terminal op e1 e2 e' σ σ'
  (STEP: (BinOp op e1 e2, σ) ~{fns}~> (e', σ'))
  (TM1: terminal e1) (TM2: terminal e2):
  σ' = σ ∧ ∃ l1 l2 l, bin_op_eval σ.(shp) op l1 l2 l ∧ e' = (#[l%S])%E.
Proof.
  inv_tstep. symmetry in Eq.
  destruct (fill_bin_op_decompose _ _ _ _ _ Eq)
    as [[]|[[K' [? Eq']]|[v1 [K' [? [Eq' VAL]]]]]]; subst.
  - clear Eq. simpl in HS. inv_head_step.
    inversion ExprStep; subst.
    split; [done|]. simpl. naive_solver.
  - apply fill_val in TM1. apply val_head_stuck in HS.
    rewrite /= HS in TM1. by destruct TM1.
  - apply fill_val in TM2. apply val_head_stuck in HS.
    rewrite /= HS in TM2. by destruct TM2.
Qed.

Lemma tstep_bin_op_red_r e1 σ1 e2 e2' σ2 op:
  terminal e1 →
  (e2, σ1) ~{fns}~>* (e2', σ2) →
  (BinOp op e1 e2, σ1) ~{fns}~>* (BinOp op e1 e2', σ2).
Proof.
  intros T1 S2.
  dependent induction S2 generalizing e2 σ1; first by constructor.
  destruct y as [e0 σ0].
  etrans; last apply IHS2; [|eauto..]. apply rtc_once.
  clear -H T1.
  move : T1 => [v1 Eqv1].
  rewrite (_: BinOp op e1 e2 = ectx_language.fill [BinOpRCtx op v1] e2);
    last by rewrite /= -(of_to_result _ _ Eqv1).
  inversion_clear H; simpl in PRIM.
  inversion_clear PRIM. subst.
  rewrite (_: BinOp op e1 (ectx_language.fill K e2') =
                ectx_language.fill [BinOpRCtx op v1] (ectx_language.fill K e2'));
    last by rewrite /= -(of_to_result _ _ Eqv1).
  rewrite 2!fill_comp.
  econstructor. econstructor; eauto.
Qed.

Lemma tstep_bin_op_red_l e1 σ1 e1' σ1' e2 op:
  (e1, σ1) ~{fns}~>* (e1', σ1') →
  (BinOp op e1 e2, σ1) ~{fns}~>* (BinOp op e1' e2, σ1').
Proof.
  intros S1.
  dependent induction S1 generalizing e1 σ1 e2; first by constructor.
  destruct y as [e0 σ0].
  etrans; last apply IHS1; [|eauto..]. apply rtc_once.
  clear -H.
  rewrite (_: BinOp op e1 e2 = ectx_language.fill [BinOpLCtx op e2] e1);
    last done.
  inversion_clear H; simpl in PRIM.
  inversion_clear PRIM. subst.
  rewrite (_: BinOp op (ectx_language.fill K e2') e2 =
    ectx_language.fill [BinOpLCtx op e2] (ectx_language.fill K e2'));
    last done.
  rewrite 2!fill_comp.
  econstructor. econstructor; eauto.
Qed.

Lemma tstep_bin_op_red e1 σ1 e1' σ1' e2 e2' σ2' op:
  (e1, σ1) ~{fns}~>* (e1', σ1') → terminal e1' →
  (e2, σ1') ~{fns}~>* (e2', σ2') →
  (BinOp op e1 e2, σ1) ~{fns}~>* (BinOp op e1' e2', σ2').
Proof.
  intros S1 T1 S2. etrans.
  - clear S2 T1. by eapply tstep_bin_op_red_l.
  - clear S1. by eapply tstep_bin_op_red_r.
Qed.

(** Copy *)

Lemma fill_copy_decompose K e e':
  fill K e = Copy e' →
  K = [] ∧ e = Copy e' ∨ (∃ K', K = K' ++ [CopyCtx] ∧ fill K' e = e').
Proof.
  revert e e'.
  induction K as [|Ki K IH]; [by left|]. simpl.
  intros e e' EqK. right.
  destruct (IH _ _ EqK) as [[? _]|[K0 [? Eq0]]].
  - subst. simpl in *. destruct Ki; try done.
    simpl in EqK. simplify_eq. exists []. naive_solver.
  - subst K. by exists (Ki :: K0).
Qed.

Lemma tstep_copy_terminal e e' σ σ'
  (STEP: (Copy e, σ) ~{fns}~> (e', σ')) (TM: terminal e) :
  ∃ l ltag T v , e = Place l ltag T ∧ e' = (Val v) ∧
    read_mem l (tsize T) σ.(shp) = Some v
    (* not true: the stacked borrows may change, ∧ σ' = σ *).
Proof.
  inv_tstep. symmetry in Eq.
  destruct (fill_copy_decompose _ _ _ Eq) as [[]|[K' [? Eq']]]; subst.
  - clear Eq. simpl in HS. inv_head_step; [by inversion ExprStep|].
    by exists l, lbor, T, v.
    (* TODO: about the state *)
  - apply fill_val in TM. apply val_head_stuck in HS.
    rewrite /= HS in TM. by destruct TM.
Qed.

Lemma tstep_copy_non_terminal e e' σ σ'
  (STEP: (Copy e, σ) ~{fns}~> (e', σ')) (NT: ¬ terminal e):
  ∃ e1, (e, σ) ~{fns}~> (e1, σ') ∧ e' = Copy e1.
Proof.
  inv_tstep.
  rewrite (_: Copy e = ectx_language.fill [CopyCtx] e) in Eq; [|done].
  apply expr_terminal_False in NT.
  destruct (step_by_val _ _ _ _ _ _ _ _ _ Eq NT HS) as [K'' Eq'].
  rewrite Eq' -fill_comp in Eq.
  have Eq'' := fill_inj _ _ _ Eq.
  eexists. split.
  - econstructor. econstructor; [exact Eq''|..|exact HS]. eauto.
  - by rewrite Eq' -fill_comp.
Qed.

End inv.
