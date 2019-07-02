(* Require Import Coq.Program.Equality. *)

From stbor.lang Require Import defs steps_wf.

Set Default Proof Using "Type".

Ltac inv_head_step :=
  repeat match goal with
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : _ = of_val ?v |- _ =>
     is_var v; destruct v; first[discriminate H|injection H as H]
  | H : head_step _ ?e _ _ _ _ _ |- _  =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H ; subst; clear H
  | H : ectx_language.head_step ?e _ _ _ _ _ |- _  =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H ; subst; clear H
  | H : mem_expr_step _ _ _ _ _ |- _ =>
      inversion H ; subst; clear H
  | H : pure_expr_step _ _ _ _ _ |- _ =>
      inversion H ; subst; clear H
  | H : bor_step _ _ _ _ _ _ _ _ _ _ _ |- _ =>
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
Implicit Type (e: ectx_language.expr (bor_ectx_lang fns))
              (K: list (ectxi_language.ectx_item (bor_ectxi_lang fns))).

Lemma tstep_reducible_not_result e σ :
  reducible fns e σ → to_result e = None.
Proof.
  intros (e' & σ' & STEP). inversion STEP. apply (reducible_not_val e σ).
  econstructor. by exists e', σ', efs.
Qed.

Lemma head_step_fill_tstep K
  e σ e' σ' ev efs :
  head_step fns e σ ev e' σ' efs →
  (fill K e, σ) ~{fns}~> (fill K e', σ').
Proof. intros ?. by econstructor; econstructor. Qed.

Lemma fill_tstep_once K e σ e' σ' :
  (e, σ) ~{fns}~> (e', σ') → (fill K e, σ) ~{fns}~> (fill K e', σ').
Proof. intros. inv_tstep. rewrite 2!fill_comp. by eapply head_step_fill_tstep. Qed.

Lemma fill_tstep_rtc' K eσ eσ' :
  eσ ~{fns}~>* eσ' → (fill K eσ.1, eσ.2) ~{fns}~>* (fill K eσ'.1, eσ'.2).
Proof.
  induction 1 as [[]|[][]??? IH]; [done|].
  intros. etrans; last apply IH. apply rtc_once. by eapply fill_tstep_once.
Qed.
Lemma fill_tstep_rtc K e σ e' σ' :
  (e, σ) ~{fns}~>* (e', σ') → (fill K e, σ) ~{fns}~>* (fill K e', σ').
Proof. by apply fill_tstep_rtc'. Qed.

Lemma fill_tstep_tc' K eσ eσ' :
  eσ ~{fns}~>+ eσ' → (fill K eσ.1, eσ.2) ~{fns}~>+ (fill K eσ'.1, eσ'.2).
Proof.
  induction 1 as [[][]|[][]??? IH].
  - by apply tc_once, fill_tstep_once.
  - etrans; last apply IH. by apply tc_once, fill_tstep_once.
Qed.
Lemma fill_tstep_tc K e σ e' σ' :
  (e, σ) ~{fns}~>+ (e', σ') → (fill K e, σ) ~{fns}~>+ (fill K e', σ').
Proof. by apply fill_tstep_tc'. Qed.

Lemma fill_tstep_inv K e1' σ1 e2 σ2 :
  to_result e1' = None →
  (fill K e1', σ1) ~{fns}~> (e2, σ2) →
  ∃ e2', e2 = fill K e2' ∧ (e1', σ1) ~{fns}~> (e2', σ2).
Proof.
  revert e1' e2 σ2.
  induction K as [|Ki K IH] ; [naive_solver|]; simpl; intros e1' e2 σ2 NT ST.
  destruct (IH _ _ _ (fill_item_no_result Ki _ NT) ST) as [e2' [Eq' ST']].
  inversion ST'; subst. simpl in PRIM.
  apply fill_step_inv in PRIM as [e3 [? PRIM]]; [|done]. subst.
  exists e3. split; [done|]. by econstructor.
Qed.

Lemma fill_tstep_inv' K e1 σ1 e2 σ2 :
  to_result e1 = None →
  (fill K e1, σ1) ~{fns}~> (fill K e2, σ2) →
  (e1, σ1) ~{fns}~> (e2, σ2).
Proof.
  intros EqN STEP. apply fill_tstep_inv in STEP as [? [? ?]]; [|done].
  by simplify_eq.
Qed.

Lemma result_tstep_stuck e σ e' σ' :
  (e, σ) ~{fns}~> (e', σ') → to_result e = None.
Proof. intros. inv_tstep. by eapply fill_not_result, (result_head_stuck fns). Qed.

Lemma result_tstep_tc_stuck e σ e' σ' :
  (e, σ) ~{fns}~>+ (e', σ') → to_result e = None.
Proof.
  inversion 1 as [?? ST|?[]? ST]; inv_tstep;
    by eapply fill_not_result, (result_head_stuck fns).
Qed.

Lemma tstep_reducible_fill_inv K e σ :
  to_result e = None →
  reducible fns (fill K e) σ → reducible fns e σ.
Proof.
  intros TN (Ke'&σ'&STEP). inversion STEP. simpl in *.
  have RED: language.reducible (Λ := bor_lang fns) (fill K e) σ by do 4 eexists.
  destruct (reducible_fill _ σ TN RED) as (?&?&?&?&?).
  do 2 eexists. by econstructor.
Qed.

Lemma tstep_reducible_fill K e σ :
  reducible fns e σ → reducible fns (fill K e) σ.
Proof. intros (e' & σ' & STEP). exists (fill K e'), σ'. by eapply fill_tstep_once. Qed.

Lemma tstep_reducible_step e1 σ1 e2 σ2 :
  (e1, σ1) ~{fns}~>* (e2, σ2) → reducible fns e2 σ2 → reducible fns e1 σ1.
Proof.
  intros STEP ?. inversion STEP as [|? [e3 σ3]]; simplify_eq; [done|].
  by do 2 eexists.
Qed.

Lemma never_stuck_fill_inv K e σ :
  never_stuck fns (fill K e) σ → never_stuck fns e σ.
Proof.
  intros NT e' σ' STEP. specialize (NT _ _ (fill_tstep_rtc K _ _ _ _ STEP)).
  destruct (to_result e') as [v'|] eqn:Eq'; [left; by eexists|right].
  destruct NT as [NT|RED].
  { exfalso. move : NT => [?]. apply (fill_not_result _ K) in Eq'. by rewrite Eq'. }
  move : RED. by apply tstep_reducible_fill_inv.
Qed.

Lemma never_stuck_tstep_once e σ e' σ':
  (e, σ) ~{fns}~> (e', σ') → never_stuck fns e σ → never_stuck fns e' σ'.
Proof.
  intros STEP1 NT e2 σ2 STEP. apply NT. etrans; [by apply rtc_once|exact STEP].
Qed.

Lemma never_stuck_tstep_rtc' eσ eσ':
  eσ ~{fns}~>* eσ' → never_stuck fns eσ.1 eσ.2 → never_stuck fns eσ'.1 eσ'.2.
Proof.
  induction 1 as [[]|[][]??? IH]; [done|].
  intros. apply IH. by eapply never_stuck_tstep_once.
Qed.

Lemma never_stuck_tstep_rtc e σ e' σ':
  (e, σ) ~{fns}~>* (e', σ') → never_stuck fns e σ → never_stuck fns e' σ'.
Proof. by apply never_stuck_tstep_rtc'. Qed.

Lemma never_stuck_tstep_tc' eσ eσ':
  eσ ~{fns}~>+ eσ' → never_stuck fns eσ.1 eσ.2 → never_stuck fns eσ'.1 eσ'.2.
Proof.
  induction 1 as [[] []|[][][]?? IH].
  - by eapply never_stuck_tstep_once.
  - intros. apply IH. by eapply never_stuck_tstep_once.
Qed.

Lemma never_stuck_tstep_tc e σ e' σ':
  (e, σ) ~{fns}~>+ (e', σ') → never_stuck fns e σ → never_stuck fns e' σ'.
Proof. apply never_stuck_tstep_tc'. Qed.

(** PURE STEP ----------------------------------------------------------------*)

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

Lemma tstep_bin_op_left_non_terminal_inv op e1 e2 e' σ σ'
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

Lemma tstep_bin_op_right_non_terminal_inv op e1 e2 e' σ σ'
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

Lemma tstep_bin_op_terminal_inv op e1 e2 e' σ σ'
  (STEP: (BinOp op e1 e2, σ) ~{fns}~> (e', σ'))
  (TM1: terminal e1) (TM2: terminal e2):
  σ' = σ ∧ ∃ l1 l2 l, bin_op_eval σ.(shp) op l1 l2 l ∧ e' = (#[l])%E.
Proof.
  inv_tstep. symmetry in Eq.
  destruct (fill_bin_op_decompose _ _ _ _ _ Eq)
    as [[]|[[K' [? Eq']]|[v1 [K' [? [Eq' VAL]]]]]]; subst.
  - clear Eq. simpl in HS. inv_head_step. naive_solver.
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
  intros T1 S2. remember (e2, σ1) as x. remember (e2', σ2) as y.
  revert x y S2 e2 σ1 Heqx Heqy.
  induction 1; intros; simplify_eq; first by constructor.
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
  intros S1. remember (e1, σ1) as x. remember (e1', σ1') as y.
  revert x y S1 e1 σ1 e2 Heqx Heqy.
  induction 1; intros; simplify_eq; first by constructor.
  destruct y as [e σ].
  etrans; last apply IHS1; [|eauto..]. apply rtc_once.
  clear -H.
  rewrite (_: BinOp op e1 e2 = ectx_language.fill [BinOpLCtx op e2] e1);
    last done.
  inv_tstep.
  rewrite (_: BinOp op (ectx_language.fill K e2') e2 =
    ectx_language.fill [BinOpLCtx op e2] (ectx_language.fill K e2'));
    last done.
  rewrite 2!fill_comp. econstructor. econstructor; eauto.
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

(** Let *)

Lemma fill_let_decompose K e (x: binder) e1 e2 :
  fill K e = (let: x := e1 in e2)%E →
  K = [] ∧ e = (let: x := e1 in e2)%E ∨
  (∃ K', K = K' ++ [LetCtx x e2] ∧ fill K' e = e1).
Proof.
  revert e e1. induction K as [|Ki K IH]; [naive_solver|].
  intros e e1 EqK. simpl in *. right.
  destruct (IH _ _ EqK) as [[? EqKi]|[K' [EqK' Eq]]]; subst; simpl in *.
  - exists []. simpl. destruct Ki; try done. simpl in EqK. by inversion EqK.
  - by exists (Ki :: K').
Qed.

Lemma tstep_let_inv (x: string) e1 e2 e' σ σ'
  (TERM: terminal e1)
  (STEP: ((let: x := e1 in e2)%E, σ) ~{fns}~> (e', σ')) :
  e' = subst x e1 e2  ∧ σ' = σ.
Proof.
  inv_tstep. symmetry in Eq.
  destruct (fill_let_decompose _ _ _ _ _ Eq)
    as [[]|[K' [? Eq']]]; subst.
  - clear Eq. simpl in HS. by inv_head_step.
  - apply result_head_stuck in HS. simpl in *. apply fill_val in TERM as [? EqT].
    by rewrite EqT in HS.
Qed.

(** Ref *)
Lemma fill_ref_decompose K e e' :
  fill K e = (& e')%E →
  K = [] ∧ e = (& e')%E ∨ (∃ K', K = K' ++ [RefCtx] ∧ fill K' e = e').
Proof.
  revert e. induction K as [|Ki K IH]; [naive_solver|].
  intros e EqK. right.
  destruct (IH _ EqK) as [[? EqKi]|[K' [EqK' Eq]]]; subst; simpl in *.
  - exists []. simpl. destruct Ki; try done. simpl in EqK. by inversion EqK.
  - by exists (Ki :: K').
Qed.

Lemma tstep_ref_inv l tg T e' σ σ'
  (STEP: ((& (Place l tg T))%E, σ) ~{fns}~> (e', σ')) :
  e' = #[ScPtr l tg]%E ∧ σ' = σ ∧ is_Some (σ.(shp) !! l).
Proof.
  inv_tstep. symmetry in Eq.
  destruct (fill_ref_decompose _ _ _ Eq)
    as [[]|[K' [? Eq']]]; subst.
  - clear Eq. simpl in HS. by inv_head_step.
  - apply result_head_stuck, (fill_not_result _ K') in HS.
    by rewrite Eq' in HS.
Qed.

(** Deref *)
Lemma fill_deref_decompose K e e' T :
  fill K e = ( *{T} e')%E →
  K = [] ∧ e = ( *{T} e')%E ∨ (∃ K', K = K' ++ [DerefCtx T] ∧ fill K' e = e').
Proof.
  revert e. induction K as [|Ki K IH]; [naive_solver|].
  intros e EqK. right.
  destruct (IH _ EqK) as [[? EqKi]|[K' [EqK' Eq]]]; subst; simpl in *.
  - exists []. simpl. destruct Ki; try done. simpl in EqK. by inversion EqK.
  - by exists (Ki :: K').
Qed.

Lemma tstep_deref_inv l tg T e' σ σ'
  (STEP: (( *{T} #[ScPtr l tg])%E, σ) ~{fns}~> (e', σ')) :
  e' = Place l tg T ∧ σ' = σ ∧
  (∀ (i: nat), (i < tsize T)%nat → l +ₗ i ∈ dom (gset loc) σ.(shp)).
Proof.
  inv_tstep. symmetry in Eq.
  destruct (fill_deref_decompose _ _ _ _ Eq)
    as [[]|[K' [? Eq']]]; subst.
  - clear Eq. simpl in HS. by inv_head_step.
  - apply result_head_stuck, (fill_not_result _ K') in HS.
    by rewrite Eq' in HS.
Qed.

(** Call *)
Lemma fill_call_decompose K e e1 el1:
  fill K e = Call e1 el1 →
  K = [] ∧ e = Call e1 el1 ∨
  (∃ K', K = K' ++ [CallLCtx el1] ∧ fill K' e = e1) ∨
  (∃ K' v1 vl e2 el, K = K' ++ [CallRCtx v1 vl el] ∧ fill K' e = e2 ∧
    el1 = (of_result <$> vl) ++ e2 :: el).
Proof.
  revert e e1 el1.
  induction K as [|Ki K IH]; [by left|]. simpl.
  intros e e1 el1 EqK. right.
  destruct (IH _ _ _ EqK) as [[? _]|[[K0 [? Eq0]]|[K' [v1 [vl [e2 [el [? Eq']]]]]]]].
  - subst. simpl in *. destruct Ki; try done.
    + simpl in EqK. simplify_eq. left. exists []. naive_solver.
    + right. simpl in EqK. inversion EqK; subst.
      exists []. naive_solver eauto using to_of_result.
  - subst K. left. by exists (Ki :: K0).
  - subst K. right. exists (Ki :: K'). naive_solver.
Qed.

Lemma tstep_call_inv (fid: fn_id) el e' σ σ'
  (TERM: Forall (λ ei, is_Some (to_value ei)) el)
  (STEP: (Call #[fid] el, σ) ~{fns}~> (e', σ')) :
  ∃ xl e HC es, fns !! fid = Some (@FunV xl e HC) ∧
    subst_l xl el e = Some es ∧ e' = (EndCall (InitCall es)) ∧ σ' = σ.
Proof.
  inv_tstep. symmetry in Eq.
  destruct (fill_call_decompose _ _ _ _ Eq)
    as [[]|[[K' [? Eq']]|[K' [v1 [vl [e2 [el2 [? Eq']]]]]]]]; subst.
  - simpl in *. inv_head_step. naive_solver.
  - exfalso. simpl in *. apply result_head_stuck in HS.
    destruct (fill_val (Λ:=bor_ectx_lang fns) K' e1') as [? Eqv].
    + rewrite /= Eq'. by eexists.
    + by rewrite /= HS in Eqv.
  - exfalso. simpl in *. destruct Eq' as [Eq1 Eq2].
    apply result_head_stuck in HS.
    destruct (fill_val (Λ:=bor_ectx_lang fns) K' e1') as [? Eqv].
    + rewrite /= Eq1. apply is_Some_to_value_result.
      apply (Forall_forall (λ ei, is_Some (to_value ei)) el); [exact TERM|].
      rewrite Eq2. set_solver.
    + by rewrite /= HS in Eqv.
Qed.

(** MEM STEP -----------------------------------------------------------------*)

(** InitCall *)
Lemma fill_init_call_decompose K e e' :
  fill K e = InitCall e' →
  K = [] ∧ e = InitCall e'.
Proof.
  revert e. induction K as [|Ki K IH]; [naive_solver|].
  intros e EqK. destruct (IH _ EqK) as [_ EqKi].
  by destruct Ki.
Qed.

Lemma tstep_init_call_inv e σ e' σ':
  (InitCall e, σ) ~{fns}~> (e', σ') →
  e' = e ∧ σ' = mkState σ.(shp) σ.(sst) (σ.(snc) :: σ.(scs)) σ.(snp) (S σ.(snc)).
Proof.
  intros ?. inv_tstep.
  symmetry in Eq. apply fill_init_call_decompose in Eq as [??]. subst.
  by inv_head_step.
Qed.

(** EndCall *)
Lemma fill_end_call_decompose K e e':
  fill K e = EndCall e' →
  K = [] ∧ e = EndCall e' ∨
  (∃ K', K = K' ++ [EndCallCtx] ∧ fill K' e = e').
Proof.
  revert e e'.
  induction K as [|Ki K IH]; [by left|]. simpl.
  intros e e' EqK. right.
  destruct (IH _ _ EqK) as [[? _]|[K0 [? Eq0]]].
  - subst. simpl in *. destruct Ki; try done.
    simpl in EqK. simplify_eq. exists []. naive_solver.
  - subst K. by exists (Ki :: K0).
Qed.

Lemma tstep_end_call_non_terminal_inv e e' σ σ'
  (STEP: (EndCall e, σ) ~{fns}~> (e', σ'))
  (NT: ¬ terminal e):
  ∃ e1', (e, σ) ~{fns}~> (e1', σ') ∧ e' = EndCall e1'.
Proof.
  inv_tstep.
  rewrite (_: EndCall e =  ectx_language.fill [EndCallCtx] e) in Eq; [|done].
  apply expr_terminal_False in NT.
  destruct (step_by_val _ _ _ _ _ _ _ _ _ Eq NT HS) as [K'' Eq'].
  rewrite Eq' -fill_comp in Eq.
  have Eq'' := fill_inj _ _ _ Eq.
  eexists. split.
  - econstructor. econstructor; [exact Eq''|..|exact HS]. eauto.
  - by rewrite Eq' -fill_comp.
Qed.

Lemma tstep_end_call_inv vr e' σ σ'
  (TERM: terminal vr)
  (STEP: (EndCall vr, σ) ~{fns}~> (e', σ')) :
  ∃ v, to_result vr = Some (ValR v) ∧ e' = Val v ∧
  ∃ c cids, σ.(scs) = c :: cids ∧
  σ' = mkState σ.(shp) σ.(sst) cids σ.(snp) σ.(snc).
Proof.
  destruct TERM as [v Eqvr].
  inv_tstep. symmetry in Eq.
  destruct (fill_end_call_decompose _ _ _ Eq)
    as [[]|[K' [? Eq']]]; subst.
  - clear Eq. simpl in HS. inv_head_step. naive_solver.
  - apply val_head_stuck in HS. destruct (fill_val K' e1') as [? Eq1'].
    + by eexists.
    + by rewrite /= HS in Eq1'.
Qed.

Lemma tstep_end_call_inv_tc vr e' σ σ'
  (TERM: terminal vr)
  (STEP: (EndCall vr, σ) ~{fns}~>+ (e', σ')) :
  ∃ v, to_result vr = Some (ValR v) ∧ e' = Val v ∧
  ∃ c cids, σ.(scs) = c :: cids ∧
  σ' = mkState σ.(shp) σ.(sst) cids σ.(snp) σ.(snc).
Proof.
  inversion STEP as [?? ST|?[]? ST STT]; simplify_eq.
  - apply tstep_end_call_inv in ST; done.
  - apply tstep_end_call_inv in ST as (?&?&?&?); [|done].
    simplify_eq.
    inversion STT as [?? STT2|?[]? STT2]; by apply result_tstep_stuck in STT2.
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

Lemma tstep_copy_inv l tg T e' σ σ'
  (STEP: (Copy (Place l tg T), σ) ~{fns}~> (e', σ')) :
  ∃ v α', e' = Val v ∧ read_mem l (tsize T) σ.(shp) = Some v ∧
    memory_read σ.(sst) σ.(scs) l tg (tsize T) = Some α' ∧
    σ' = mkState σ.(shp) α' σ.(scs) σ.(snp) σ.(snc).
Proof.
  inv_tstep. symmetry in Eq.
  destruct (fill_copy_decompose _ _ _ Eq) as [[]|[K' [? Eq']]]; subst.
  - clear Eq. simpl in HS. inv_head_step. naive_solver.
  - exfalso. apply val_head_stuck in HS. destruct (fill_val K' e1') as [? Eq1'].
    + rewrite /= Eq'. by eexists.
    + by rewrite Eq1' in HS.
Qed.

Lemma tstep_copy_non_terminal_inv e e' σ σ'
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

(** Write *)
Lemma fill_write_decompose K e e1 e2:
  fill K e = Write e1 e2 →
  K = [] ∧ e = Write e1 e2 ∨
  (∃ K', K = K' ++ [WriteLCtx e2] ∧ fill K' e = e1) ∨
  (∃ v1 K', K = K' ++ [WriteRCtx v1] ∧ fill K' e = e2 ∧ to_result e1 = Some v1).
Proof.
  revert e e1 e2.
  induction K as [|Ki K IH]; [by left|]. simpl.
  intros e e1 e2 EqK. right.
  destruct (IH _ _ _ EqK) as [[? _]|[[K0 [? Eq0]]|[r1 [K' [? Eq']]]]].
  - subst. simpl in *. destruct Ki; try done.
    + simpl in EqK. simplify_eq. left. exists []. naive_solver.
    + right. simpl in EqK. inversion EqK; subst.
      exists r, []. naive_solver eauto using to_of_result.
  - subst K. left. by exists (Ki :: K0).
  - subst K. right. by exists r1, (Ki :: K').
Qed.

Lemma tstep_write_inv l tg T v e' σ σ'
  (STEP: ((Place l tg T <- #v)%E, σ) ~{fns}~> (e', σ')) :
  ∃ α', e' = (#[☠]%V) ∧
    memory_written σ.(sst) σ.(scs) l tg (tsize T) = Some α' ∧
    (∀ (i: nat), (i < length v)%nat → l +ₗ i ∈ dom (gset loc) σ.(shp)) ∧
    (v <<t σ.(snp)) ∧ (length v = tsize T) ∧
    σ' = mkState (write_mem l v σ.(shp)) α' σ.(scs) σ.(snp) σ.(snc).
Proof.
  inv_tstep. symmetry in Eq.
  destruct (fill_write_decompose _ _ _ _ Eq)
    as [[]|[[K' [? Eq']]|[? [K' [? [Eq' ?]]]]]]; subst.
  - clear Eq. simpl in HS. inv_head_step. naive_solver.
  - exfalso. apply val_head_stuck in HS. destruct (fill_val K' e1') as [? Eq1'].
    + rewrite /= Eq'. by eexists.
    + by rewrite Eq1' in HS.
  - exfalso. apply val_head_stuck in HS. destruct (fill_val K' e1') as [? Eq1'].
    + rewrite /= Eq'. by eexists.
    + by rewrite Eq1' in HS.
Qed.

(** Retag *)

Lemma fill_retag_decompose K e kind e':
  fill K e = Retag e' kind →
  K = [] ∧ e = Retag e' kind ∨ (∃ K', K = K' ++ [RetagCtx kind] ∧ fill K' e = e').
Proof.
  revert e e'.
  induction K as [|Ki K IH]; [by left|]. simpl.
  intros e e' EqK. right.
  destruct (IH _ _ EqK) as [[? _]|[K0 [? Eq0]]].
  - subst. simpl in *. destruct Ki; try done.
    simpl in EqK. simplify_eq. exists []. naive_solver.
  - subst K. by exists (Ki :: K0).
Qed.

Lemma tstep_retag_inv x tg T pk rk e' σ σ'
  (STEP: (Retag (Place x tg (Reference pk T)) rk, σ) ~{fns}~> (e', σ')) :
  ∃ c cids h' α' nxtp',
  σ.(scs) = c :: cids ∧
  retag σ.(shp) σ.(sst) σ.(snp) σ.(scs) c x rk (Reference pk T)
    = Some (h', α', nxtp') ∧
  e' = #[☠]%V ∧
  σ' = mkState h' α' σ.(scs) nxtp' σ.(snc).
Proof.
  inv_tstep. symmetry in Eq.
  destruct (fill_retag_decompose _ _ _ _ Eq) as [[]|[K' [? Eq']]]; subst.
  - clear Eq. simpl in HS. inv_head_step. naive_solver.
  - exfalso. apply val_head_stuck in HS. destruct (fill_val K' e1') as [? Eq1'].
    + rewrite /= Eq'. by eexists.
    + by rewrite Eq1' in HS.
Qed.

End inv.
