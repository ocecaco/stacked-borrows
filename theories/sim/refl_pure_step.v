From iris.algebra Require Import local_updates.

From stbor.lang Require Import steps_progress steps_inversion steps_retag.
From stbor.sim Require Export instance body.

Set Default Proof Using "Type".

(** PURE STEP ----------------------------------------------------------------*)

(** Call - step over *)
Lemma sim_body_step_over_call fs ft
  rc rv n fid vls vlt σs σt Φ
  (VREL: Forall2 (vrel rv) vls vlt)
  (FUNS: sim_local_funs_lookup fs ft) :
  (∀ r' vs vt σs' σt' (VRET: rrel vrel r' vs vt)
    (STACKS: σs.(scs) = σs'.(scs))
    (STACKT: σt.(scs) = σt'.(scs)), ∃ n',
    rc ⋅ r' ⊨{n',fs,ft} (of_result vs, σs') ≥ (of_result vt, σt') : Φ) →
  rc ⋅ rv ⊨{n,fs,ft}
    (Call #[ScFnPtr fid] (Val <$> vls), σs) ≥ (Call #[ScFnPtr fid] (Val <$> vlt), σt) : Φ.
Proof.
  intros CONT. pfold. intros NT r_f WSAT.
  edestruct NT as [[]|[e2 [σ2 RED]]]; [constructor 1|done|].
  apply tstep_call_inv in RED; last first.
  { apply list_Forall_to_value. eauto. }
  destruct RED as (xls & ebs & HCs & ebss & Eqfs & Eqss & ? & ?). subst e2 σ2.
  destruct (FUNS _ _ Eqfs) as ([xlt ebt HCt] & Eqft & Eql).
  simpl in Eql.
  destruct (subst_l_is_Some xlt (Val <$> vlt) ebt) as [est Eqst].
  { rewrite fmap_length -(Forall2_length _ _ _ VREL) -Eql
            (subst_l_is_Some_length _ _ _ _ Eqss) fmap_length //. }
  split; [|done|].
  { right. exists (EndCall (InitCall est)), σt.
     eapply (head_step_fill_tstep _ []). econstructor. econstructor; try done.
     apply list_Forall_to_value. eauto. }
  eapply (sim_local_body_step_over_call _ _ _ _ _ _ _ _ _ _ _ _ _
            [] [] fid (ValR <$> vlt) (ValR <$> vls)); eauto.
  { by rewrite of_result_list_expr. }
  { by rewrite of_result_list_expr. }
  { eapply Forall2_fmap, Forall2_impl; eauto. }
  intros r' ? ? σs' σt' VR WSAT' STACK.
  destruct (CONT _ _ _ σs' σt' VR) as [n' ?]; [|done|exists n'; by left].
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
    as (vv & iv & vi & ? & ? & ? & ? & ? & ?). subst v i et' σt'.
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
Admitted.

(** BinOp *)

(** Case *)

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
Lemma sim_body_ref fs ft r n l tgs tgt Ts Tt σs σt Φ :
  Φ r n (ValR [ScPtr l tgs]) σs (ValR [ScPtr l tgt]) σt : Prop →
  r ⊨{n,fs,ft} ((& (Place l tgs Ts))%E, σs) ≥ ((& (Place l tgt Tt))%E, σt) : Φ.
Proof.
  intros SIM. pfold.
  intros NT r_f WSAT. split; [|done|].
  { right.
    destruct (NT (& (Place l tgs Ts))%E σs) as [[]|[es' [σs' STEPS]]]; [done..|].
    destruct (tstep_ref_inv _ _ _ _ _ _ _ STEPS) as [? [? IS]]. subst es' σs'.
    have ?: is_Some (σt.(shp) !! l).
    { clear -WSAT IS. move : IS.
      by rewrite -2!(elem_of_dom (D:=gset loc)) -wsat_heap_dom. }
    exists #[ScPtr l tgt]%E, σt.
    eapply (head_step_fill_tstep _ []). by econstructor; econstructor. }
  constructor 1. intros.
  destruct (tstep_ref_inv _ _ _ _ _ _ _ STEPT) as [? [? IS]]. subst et' σt'.
  have ?: is_Some (σs.(shp) !! l).
  { clear -WSAT IS. move : IS.
    by rewrite -2!(elem_of_dom (D:=gset loc)) wsat_heap_dom. }
  exists #[ScPtr l tgs]%E, σs, r, n. split.
  { left. constructor 1. eapply (head_step_fill_tstep _ []).
    by econstructor; econstructor. }
  split; [done|]. left.
  by apply (sim_body_result _ _ _ _ (ValR _) (ValR _)).
Qed.

(** Deref *)
Lemma sim_body_deref fs ft r n l tgs tgt Ts Tt σs σt Φ
  (EQS: tsize Ts = tsize Tt) :
  Φ r n (PlaceR l tgs Ts) σs (PlaceR l tgt Tt) σt : Prop →
  r ⊨{n,fs,ft} (Deref #[ScPtr l tgs] Ts, σs) ≥ (Deref #[ScPtr l tgt] Tt, σt) : Φ.
Proof.
  intros SIM. pfold.
  intros NT r_f WSAT. split; [|done|].
  { right.
    destruct (NT (Deref #[ScPtr l tgs] Ts) σs) as [[]|[es' [σs' STEPS]]]; [done..|].
    destruct (tstep_deref_inv _ _ _ _ _ _ _ STEPS) as [? [? IS]]. subst es' σs'.
    have ?: (∀ (i: nat), (i < tsize Tt)%nat → l +ₗ i ∈ dom (gset loc) σt.(shp)).
    { clear -WSAT IS EQS. rewrite -EQS. move => i /IS. by rewrite -wsat_heap_dom. }
    exists (Place l tgt Tt), σt.
    eapply (head_step_fill_tstep _ []). by econstructor; econstructor. }
  constructor 1. intros.
  destruct (tstep_deref_inv _ _ _ _ _ _ _ STEPT) as [? [? IS]]. subst et' σt'.
  have ?: (∀ (i: nat), (i < tsize Ts)%nat → l +ₗ i ∈ dom (gset loc) σs.(shp)).
  { clear -WSAT IS EQS. rewrite EQS. move => i /IS. by rewrite wsat_heap_dom. }
  exists (Place l tgs Ts), σs, r, n. split.
  { left. constructor 1. eapply (head_step_fill_tstep _ []).
    by econstructor; econstructor. }
  split; [done|].
  left. by apply (sim_body_result _ _ _ _ (PlaceR _ _ _) (PlaceR _ _ _)).
Qed.
