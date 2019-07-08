From iris.algebra Require Import local_updates.

From stbor.lang Require Import steps_progress steps_inversion steps_retag.
From stbor.sim Require Export instance body.

Set Default Proof Using "Type".

(** PURE STEP ----------------------------------------------------------------*)

(** Call - step over *)
Lemma sim_body_step_over_call fs ft
  rc rv n fid rls rlt σs σt Φ
  (RREL: Forall2 (rrel rv) rls rlt)
  (FUNS: sim_local_funs_lookup fs ft) :
  (∀ r' vls vlt vs vt σs' σt' (VRET: vrel r' vs vt)
    (STACKS: σs.(scs) = σs'.(scs))
    (STACKT: σt.(scs) = σt'.(scs))
    (Eqvls: rls = ValR <$> vls)
    (Eqvlt: rlt = ValR <$> vlt), ∃ n',
    rc ⋅ r' ⊨{n',fs,ft} (Val vs, σs') ≥ (Val vt, σt') : Φ) →
  rc ⋅ rv ⊨{n,fs,ft}
    (Call #[ScFnPtr fid] (of_result <$> rls), σs) ≥ (Call #[ScFnPtr fid] (of_result <$> rlt), σt) : Φ.
Proof.
  intros CONT. pfold. intros NT r_f WSAT.
  edestruct NT as [[]|[e2 [σ2 RED]]]; [constructor 1|done|].
  apply tstep_call_inv_result in RED; last by apply list_Forall_to_of_result.
  destruct RED as (xls & ebs & HCs & ebss & Eqfs & Eqss & ? & ? & VALs).
  have VALs' := VALs. apply list_Forall_to_value in VALs' as [vls Eqvls].
  subst. rewrite Eqvls. rewrite Eqvls in VALs, Eqss.
  apply list_Forall_result_value in Eqvls. subst rls.
  destruct (list_Forall_rrel_vrel_3 _ _ _ RREL VALs) as (vlt & ? & VALt & VREL).
  subst rlt.
  destruct (FUNS _ _ Eqfs) as ([xlt ebt HCt] & Eqft & Eql).
  simpl in Eql.
  destruct (subst_l_is_Some xlt (Val <$> vlt) ebt) as [est Eqst].
  { rewrite fmap_length -(Forall2_length _ _ _ VREL) -Eql
            (subst_l_is_Some_length _ _ _ _ Eqss) fmap_length //. }
  split; [|done|].
  { right. exists (EndCall (InitCall est)), σt.
     eapply (head_step_fill_tstep _ []).
     econstructor. econstructor; try done; rewrite list_Forall_result_value_2 //. }
  eapply (sim_local_body_step_over_call _ _ _ _ _ _ _ _ _ _ _ _ _
            [] [] fid (ValR <$> vlt) (ValR <$> vls)); eauto.
  { by rewrite of_result_list_expr. }
  intros r' ? ? σs' σt' VR WSAT' STACK.
  destruct (CONT r' vls vlt v_src v_tgt σs' σt') as [n' ?];
    [by apply vrel_rrel| |done..|exists n'; by left].
  destruct WSAT as (?&?&?&?&?&SREL&?). destruct SREL as (?&?&?Eqcss&?).
  destruct WSAT' as (?&?&?&?&?&SREL'&?). destruct SREL' as (?&?&?Eqcss'&?).
  by rewrite Eqcss' Eqcss.
Qed.

(** Var *)
Lemma sim_body_var fs ft r n σs σt var Φ :
  r ⊨{n,fs,ft} (Var var, σs) ≥ (Var var, σt) : Φ.
Proof.
  pfold. intros NT r_f WSAT.
  destruct (NT (Var var) σs) as [[]|[? [? RED%tstep_var_inv]]];
    [constructor|done..].
Qed.

(** Proj *)
Lemma sim_body_proj fs ft r n (v i: result) σs σt Φ :
  (∀ vi vv iv, v = ValR vv → i = ValR [ScInt iv] →
    vv !! (Z.to_nat iv) = Some vi → 0 ≤ iv →
    Φ r n (ValR [vi]) σs (ValR [vi]) σt : Prop) →
  r ⊨{n,fs,ft} (Proj v i, σs) ≥ (Proj v i, σt) : Φ.
Proof.
  intros POST. pfold. intros NT r_f WSAT. split; [|done|].
  { right.
    edestruct NT as [[]|[es1 [σs1 RED]]]; [constructor 1|done|].
    destruct (tstep_proj_inv _ _ _ _ _ _ RED)
      as (vv & iv & vi & ? & ? & ? & ? & ? & ?). subst v i es1 σs1.
    do 2 eexists. eapply (head_step_fill_tstep _ []).
    econstructor. econstructor; eauto. }
  constructor 1. intros.
  destruct (tstep_proj_inv _ _ _ _ _ _ STEPT)
    as (vv & iv & vi & ? & ? & ? & ? & ? & ?). subst.
  exists (#[vi])%E, σs, r, n. split; last split; [|done|].
  { left. constructor 1. eapply (head_step_fill_tstep _ []).
    by econstructor; econstructor. }
  left. apply (sim_body_result _ _ _ _ (ValR _) (ValR _)). intros.
  eapply POST; eauto.
Qed.

(** Conc *)
Lemma sim_body_conc fs ft r n (r1 r2: result) σs σt Φ :
  (∀ v1 v2, r1 = ValR v1 → r2 = ValR v2 →
    Φ r n (ValR (v1 ++ v2)) σs (ValR (v1 ++ v2)) σt : Prop) →
  r ⊨{n,fs,ft} (Conc r1 r2, σs) ≥ (Conc r1 r2, σt) : Φ.
Proof.
  intros POST. pfold. intros NT r_f WSAT. split; [|done|].
  { right.
    edestruct NT as [[]|[es1 [σs1 RED]]]; [constructor 1|done|].
    destruct (tstep_conc_inv _ _ _ _ _ _ RED) as (v1 & v2 &?&?&?&?). subst.
    do 2 eexists. eapply (head_step_fill_tstep _ []).
    econstructor. econstructor; eauto. }
  constructor 1. intros.
  destruct (tstep_conc_inv _ _ _ _ _ _ STEPT) as (v1 & v2 &?&?&?&?). subst.
  exists (#(v1 ++ v2))%E, σs, r, n. split; last split; [|done|].
  { left. constructor 1. eapply (head_step_fill_tstep _ []).
    by econstructor; econstructor. }
  left. apply (sim_body_result _ _ _ _ (ValR _) (ValR _)). intros.
  eapply POST; eauto.
Qed.

(** BinOp *)
Lemma sim_body_bin_op fs ft r n op (r1 r2: result) σs σt Φ :
  (∀ s1 s2 s, r1 = ValR [s1] → r2 = ValR [s2] →
    bin_op_eval σt.(shp) op s1 s2 s →
    Φ r n (ValR [s]) σs (ValR [s]) σt : Prop) →
  r ⊨{n,fs,ft} (BinOp op r1 r2, σs) ≥ (BinOp op r1 r2, σt) : Φ.
Proof.
  intros POST. pfold. intros NT r_f WSAT. split; [|done|].
  { right.
    edestruct NT as [[]|[es1 [σs1 RED]]]; [constructor 1|done|].
    destruct (tstep_bin_op_inv _ _ _ _ _ _ _ RED) as (s1 & s2 & s &?&?& BO &?&?).
    subst. do 2 eexists. eapply (head_step_fill_tstep _ []).
    econstructor; econstructor; eauto.
    eapply bin_op_eval_dom; [|eauto]. by rewrite (wsat_heap_dom _ _ _ WSAT). }
  constructor 1. intros.
  destruct (tstep_bin_op_inv _ _ _ _ _ _ _ STEPT) as (s1 & s2 & s &?&?& BO &?&?).
  subst.
  exists (#[s])%E, σs, r, n. split; last split; [|done|].
  { left. constructor 1. eapply (head_step_fill_tstep _ []).
    econstructor; econstructor; eauto.
    eapply bin_op_eval_dom; [|eauto]. by rewrite (wsat_heap_dom _ _ _ WSAT). }
  left. apply (sim_body_result _ _ _ _ (ValR _) (ValR _)). intros.
  eapply POST; eauto.
Qed.

(** Case *)
Lemma sim_body_case fs ft r n (rc: result) els elt σs σt Φ :
  length els = length elt →
  (∀ (es et: expr) (i: Z), 0 ≤ i →
    els !! (Z.to_nat i) = Some es →
    elt !! (Z.to_nat i) = Some et →
    rc = ValR [ScInt i] →
    r ⊨{n,fs,ft} (es, σs) ≥ (et, σt) : Φ) →
  r ⊨{n,fs,ft} (Case rc els, σs) ≥ (Case rc elt, σt) : Φ.
Proof.
  intros EqL POST. pfold. intros NT r_f WSAT. split; [|done|].
  { right.
    edestruct NT as [[]|[es1 [σs1 RED]]]; [constructor 1|done|].
    destruct (tstep_case_inv _ _ _ _ _ _ RED) as (i & es & ? &Eqs&?&?&?). subst.
    assert (is_Some (elt !! (Z.to_nat i))) as [et ?].
    { rewrite lookup_lt_is_Some -EqL -lookup_lt_is_Some. by eexists. }
    do 2 eexists. eapply (head_step_fill_tstep _ []).
    econstructor; econstructor; eauto. }
  constructor 1. intros.
  destruct (tstep_case_inv _ _ _ _ _ _ STEPT)as (i & et & ? &Eqt&?&?&?). subst.
  assert (is_Some (els !! (Z.to_nat i))) as [es ?].
  { rewrite lookup_lt_is_Some EqL -lookup_lt_is_Some. by eexists. }
  exists es, σs, r, n. split; last split; [|done|].
  { left. constructor 1. eapply (head_step_fill_tstep _ []).
    econstructor; econstructor; eauto. }
  left. eapply POST; eauto.
Qed.

(** Let *)
Lemma sim_body_let fs ft r n x es1 es2 et1 et2 σs σt Φ :
  terminal es1 → terminal et1 →
  r ⊨{n,fs,ft} (subst' x es1 es2, σs) ≥ (subst' x et1 et2, σt) : Φ →
  r ⊨{n,fs,ft} (let: x := es1 in es2, σs) ≥ (let: x := et1 in et2, σt) : Φ.
Proof.
  intros TS TT SIM. pfold.
  intros NT r_f WSAT. split; [|done|].
  { right. do 2 eexists. eapply (head_step_fill_tstep _ []).
    econstructor 1. eapply LetBS; eauto. }
  constructor 1. intros.
  destruct (tstep_let_inv _ _ _ _ _ _ _ TT STEPT). subst et' σt'.
  exists (subst' x es1 es2), σs, r, n. split.
  { left. constructor 1. eapply (head_step_fill_tstep _ []).
    by econstructor; econstructor. }
  split; [done|]. by left.
Qed.

Lemma sim_body_let_val fs ft r n b (vs1 vt1: value) es2 et2 σs σt Φ :
  r ⊨{n,fs,ft} (subst' b vs1 es2, σs) ≥ (subst' b vt1 et2, σt) : Φ →
  r ⊨{n,fs,ft} (let: b := vs1 in es2, σs) ≥ (let: b := vt1 in et2, σt) : Φ.
Proof. apply sim_body_let; eauto. Qed.

Lemma sim_body_let_place fs ft r n x ls lt ts tt tys tyt es2 et2 σs σt Φ :
  r ⊨{n,fs,ft} (subst' x (Place ls ts tys) es2, σs) ≥ (subst' x (Place lt tt tyt) et2, σt) : Φ →
  r ⊨{n,fs,ft} (let: x := Place ls ts tys in es2, σs) ≥ ((let: x := Place lt tt tyt in et2), σt) : Φ.
Proof. apply sim_body_let; eauto. Qed.

(** Ref *)
Lemma sim_body_ref fs ft r n (pl: result) σs σt Φ :
  (∀ l t T, pl = PlaceR l t T →
    Φ r n (ValR [ScPtr l t]) σs (ValR [ScPtr l t]) σt : Prop) →
  r ⊨{n,fs,ft} ((& pl)%E, σs) ≥ ((& pl)%E, σt) : Φ.
Proof.
  intros POST. pfold.
  intros NT r_f WSAT. split; [|done|].
  { right.
    destruct (NT (& pl)%E σs) as [[]|[es' [σs' STEPS]]]; [done..|].
    destruct (tstep_ref_inv _ _ _ _ _ STEPS) as (l & tg & T & ? & ? & ? & IS).
    simplify_eq.
    have ?: is_Some (σt.(shp) !! l).
    { clear -WSAT IS. move : IS.
      by rewrite -2!(elem_of_dom (D:=gset loc)) -wsat_heap_dom. }
    exists #[ScPtr l tg]%E, σt.
    eapply (head_step_fill_tstep _ []). by econstructor; econstructor. }
  constructor 1. intros.
  destruct (tstep_ref_inv _ _ _ _ _ STEPT) as (l & tg & T & ? & ? & ? & IS).
  simplify_eq.
  have ?: is_Some (σs.(shp) !! l).
  { clear -WSAT IS. move : IS.
    by rewrite -2!(elem_of_dom (D:=gset loc)) wsat_heap_dom. }
  exists #[ScPtr l tg]%E, σs, r, n. split.
  { left. constructor 1. eapply (head_step_fill_tstep _ []).
    by econstructor; econstructor. }
  split; [done|]. left.
  apply (sim_body_result _ _ _ _ (ValR _) (ValR _)).
  intros. by eapply POST.
Qed.

(** Deref *)
Lemma sim_body_deref fs ft r n (rf: result) T σs σt Φ :
  (∀ l t, rf = ValR [ScPtr l t] →
    Φ r n (PlaceR l t T) σs (PlaceR l t T) σt : Prop ) →
  r ⊨{n,fs,ft} (Deref rf T, σs) ≥ (Deref rf T, σt) : Φ.
Proof.
  intros POST. pfold.
  intros NT r_f WSAT. split; [|done|].
  { right.
    destruct (NT (Deref rf T) σs) as [[]|[es' [σs' STEPS]]]; [done..|].
    destruct (tstep_deref_inv _ _ _ _ _ _ STEPS) as (l & t & ? & ? & ? & IS).
    subst.
    have ?: (∀ (i: nat), (i < tsize T)%nat → l +ₗ i ∈ dom (gset loc) σt.(shp)).
    { clear -WSAT IS. by setoid_rewrite wsat_heap_dom. }
    exists (Place l t T), σt.
    eapply (head_step_fill_tstep _ []). by econstructor; econstructor. }
  constructor 1. intros.
  destruct (tstep_deref_inv _ _ _ _ _ _ STEPT) as (l & t & ? & ? & ? & IS).
  subst.
  have ?: (∀ (i: nat), (i < tsize T)%nat → l +ₗ i ∈ dom (gset loc) σs.(shp)).
  { clear -WSAT IS. by setoid_rewrite <- wsat_heap_dom. }
  exists (Place l t T), σs, r, n. split.
  { left. constructor 1. eapply (head_step_fill_tstep _ []).
    by econstructor; econstructor. }
  split; [done|].
  left. apply (sim_body_result _ _ _ _ (PlaceR _ _ _) (PlaceR _ _ _)).
  intros. by eapply POST.
Qed.
