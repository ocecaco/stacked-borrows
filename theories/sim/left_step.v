From iris.algebra Require Import local_updates.

From stbor.lang Require Import steps_progress steps_inversion steps_retag.
From stbor.sim Require Export instance invariant_access body.

Set Default Proof Using "Type".

Section left.
Implicit Types Φ: resUR → nat → result → state → result → state → Prop.

Lemma sim_body_let_l fs ft r n x et es1 es2 vs1 σs σt Φ :
  IntoResult es1 vs1 →
  r ⊨{n,fs,ft} (subst' x es1 es2, σs) ≥ (et, σt) : Φ →
  r ⊨{n,fs,ft} (let: x := es1 in es2, σs) ≥ (et, σt) : Φ.
Proof.
  intros TS%into_result_terminal CONT. pfold.
  intros NT r_f WSAT.
  have STEPS1: ((let: x := es1 in es2)%E, σs) ~{fs}~> (subst' x es1 es2, σs).
  { eapply (head_step_fill_tstep _ []). econstructor. by econstructor. }
  have STEPS: ((let: x := es1 in es2)%E, σs) ~{fs}~>* (subst' x es1 es2, σs).
  { by apply rtc_once. }
  have NT2 := never_stuck_tstep_rtc _ _ _ _ _ STEPS NT.
  have CONT2 := CONT. punfold CONT. specialize (CONT NT2 r_f WSAT) as [RE TE ST].
  split; [done|..].
  { intros. specialize (TE _ TERM) as (vs' & σs' & r' & STEPS' & ?).
    exists vs', σs', r'. split; [|done]. by etrans. }
  inversion ST.
  - constructor 1. intros.
    specialize (STEP _ _ STEPT) as (es' & σs' & r' & n' & SS' & ?).
    exists es', σs', r', n'. split ; [|done]. left.
    destruct SS' as [SS'|[]].
    + eapply tc_rtc_l; eauto.
    + simplify_eq. by apply tc_once.
  - econstructor 2; eauto. by etrans.
Qed.

Lemma sim_body_deref_l fs ft r n et (rt: result) l t T σs σt Φ :
  IntoResult et rt →
  (Φ r n (PlaceR l t T) σs rt σt) →
  r ⊨{n,fs,ft} (Deref #[ScPtr l t] T, σs) ≥ (et, σt) : Φ.
Proof.
  intros TT POST. pfold.
  intros NT r_f WSAT. split.
  { left. by apply into_result_terminal in TT. }
  { intros. exists (PlaceR l t T), σs, r. split; last split; [|done|].
    - apply rtc_once. eapply (head_step_fill_tstep _ []).
      econstructor. econstructor.
    - rewrite <-into_result in TERM. rewrite to_of_result in TERM.
      by simplify_eq. }
  constructor 1. intros.
  apply result_tstep_stuck in STEPT.
  move : STEPT. rewrite <-into_result. by rewrite to_of_result.
Qed.

Lemma sim_body_copy_unique_l
  fs ft (r r': resUR) (h: heaplet) n (l: loc) t T (s: scalar) et σs σt Φ :
  tsize T = 1%nat →
  r ≡ r' ⋅ res_tag t tkUnique h →
  h !! l = Some s →
  (r ⊨{n,fs,ft} (#[s], σs) ≥ (et, σt) : Φ : Prop) →
  r ⊨{n,fs,ft} (Copy (Place l (Tagged t) T), σs) ≥ (et, σt) : Φ.
Proof.
  intros LenT Eqr Eqs CONT. pfold. intros NT. intros.
  have WSAT1 := WSAT. (* backup *)

  (* making a step *)
  edestruct (NT (Copy (Place l (Tagged t) T)) σs) as [[]|[es' [σs' STEPS]]];
    [done..|].
  destruct (tstep_copy_inv _ (PlaceR _ _ _) _ _ _ STEPS)
      as (l'&t'&T'& vs & α' & EqH & ? & Eqvs & Eqα' & ?).
  symmetry in EqH. simplify_eq.

  rewrite LenT read_mem_equation_1 /= in Eqvs.
  destruct (σs.(shp) !! l) as [s'|] eqn:Eqs'; [|done].
  simpl in Eqvs. simplify_eq.

  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  (* some lookup properties *)
  have VALIDr := cmra_valid_op_r _ _ VALID. rewrite ->Eqr in VALIDr.
  have HLtr: r.(rtm) !! t ≡ Some (to_tagKindR tkUnique, to_agree <$> h).
  { rewrite Eqr.
    eapply tmap_lookup_op_unique_included;
      [apply VALIDr|apply cmra_included_r|].
    rewrite res_tag_lookup //. }
  have HLtrf: (r_f ⋅ r).(rtm) !! t ≡ Some (to_tagKindR tkUnique, to_agree <$> h).
  { apply tmap_lookup_op_r_unique_equiv; [apply VALID|done]. }

  (* Unique: stack unchanged *)
  destruct (for_each_lookup_case_2 _ _ _ _ _ Eqα') as [EQ1 _].
  specialize (EQ1 O) as (stk & stk' & Eqstk & Eqstk' & ACC1); [rewrite LenT; lia|].
  rewrite shift_loc_0_nat in Eqstk, Eqstk'.
  move : ACC1. case access1 as [[n1 stk1]|] eqn:ACC1; [|done].
  simpl. intros Eqs1. symmetry in Eqs1. simplify_eq.

  destruct SREL as (Eqst&Eqnp&Eqcs&Eqnc&AREL).
  rewrite Eqst in Eqstk. rewrite Eqcs in ACC1.

  destruct (unique_access_head _ _ _ _ _ _ _ _ _ s _ Eqstk ACC1 PINV HLtrf)
    as (it & Eqpit & Eqti & HDi & Eqhp); [by rewrite lookup_fmap Eqs |].

  have ?: α' = σt.(sst).
  { move : Eqα'.
    rewrite LenT /= /memory_read /= /= shift_loc_0_nat Eqst Eqstk /= Eqcs ACC1 /=.
    destruct (tag_unique_head_access σt.(scs) stk (Tagged t) it.(protector) AccessRead)
      as [ns Eqss].
    - destruct HDi as [stk' Eq']. exists stk'. rewrite Eq'. f_equal.
      rewrite -Eqpit -Eqti. by destruct it.
    - rewrite ACC1 in Eqss. simplify_eq. rewrite insert_id //. by inversion 1. }
  subst α'. rewrite Eqstk in Eqstk'. symmetry in Eqstk'. simplify_eq.

  have TOT: tag_on_top σt.(sst) l t.
  { destruct HDi as [stk' Eqstk'].
    rewrite /tag_on_top Eqstk Eqstk' /= -Eqpit -Eqti. destruct it. by eexists. }

  rewrite (_: mkState σs.(shp) σt.(sst) σs.(scs) σs.(snp) σs.(snc) = σs) in STEPS;
    last first. { rewrite -Eqst. by destruct σs. }

  (* we read s' from σs(l), we know [s] is in σt(l), now we have to prove that
    s' = s *)
  (* FIXME: this is a hack *)
  assert (s' = s).
  { specialize (PINV _ _ _ HLtrf) as [? PINV].
    specialize (PINV l s). rewrite lookup_fmap Eqs in PINV.
    specialize (PINV ltac:(done) _ Eqstk Unique it.(protector))
      as (?&?&?&_); [|done|].
    - destruct HDi as [? HDi]. rewrite HDi. rewrite -Eqpit -Eqti.
      destruct it; by left.
    - by simplify_eq. }
  subst s'.

  have STEPSS: (Copy (Place l (Tagged t) T), σs) ~{fs}~>* (#[s]%E, σs)
    by apply rtc_once.
  have NT' := never_stuck_tstep_once _ _ _ _ _ STEPS NT.
  (* TODO: the following is the same in most proofs, generalize it *)
  punfold CONT. specialize (CONT NT' _ WSAT1) as [RE TE ST]. split; [done|..].
  - intros. specialize (TE _ TERM) as (vs' & σs' & r1 & STEPS' & POST).
    exists vs', σs', r1. split; [|done]. etrans; eauto.
  - inversion ST.
    + constructor 1. intros.
      destruct (STEP _ _ STEPT) as (es' & σs' & r1 & n' & STEPS' & POST).
      exists es', σs', r1, n'. split; [|done].
      left. destruct STEPS' as [?|[]].
      * eapply tc_rtc_l; eauto.
      * simplify_eq. by apply tc_once.
    + econstructor 2; eauto. by etrans.
Qed.

Lemma sim_body_copy_local_l fs ft r r' n l tg ty s et σs σt Φ :
  tsize ty = 1%nat →
  r ≡ r' ⋅ res_mapsto l [s] tg →
  (r ⊨{n,fs,ft} (#[s], σs) ≥ (et, σt) : Φ) →
  r ⊨{n,fs,ft}
    (Copy (Place l (Tagged tg) ty), σs) ≥ (et, σt)
  : Φ.
Proof.
  intros Hty Hr. rewrite Hr cmra_assoc. intros CONT.
  eapply sim_body_copy_unique_l; eauto.
  by rewrite lookup_insert.
Qed.

End left.
