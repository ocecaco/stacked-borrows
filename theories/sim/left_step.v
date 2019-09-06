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

(* Unique/Local copy *)
Lemma sim_body_copy_local_unique_l
  fs ft (r r': resUR) (h: heaplet) n (l: loc) t k T (ss st: scalar) et σs σt Φ
  (LU: k = tkLocal ∨ k = tkUnique) :
  tsize T = 1%nat →
  r ≡ r' ⋅ res_tag t k h →
  h !! l = Some (ss,st) →
  (r ⊨{n,fs,ft} (#[ss], σs) ≥ (et, σt) : Φ : Prop) →
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

  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL).
  (* some lookup properties *)
  have VALIDr := cmra_valid_op_r _ _ VALID. rewrite ->Eqr in VALIDr.
  have HLtr: r.(rtm) !! t ≡ Some (to_tgkR k, to_agree <$> h).
  { rewrite Eqr.
    destruct LU; subst k.
    - eapply tmap_lookup_op_local_included; [apply VALIDr|apply cmra_included_r|].
      rewrite res_tag_lookup //.
    - eapply tmap_lookup_op_uniq_included; [apply VALIDr|apply cmra_included_r|].
      rewrite res_tag_lookup //. }
  have HLtrf: (r_f ⋅ r).(rtm) !! t ≡ Some (to_tgkR k, to_agree <$> h).
  { destruct LU; subst k.
    - apply tmap_lookup_op_r_local_equiv; [apply VALID|done].
    - apply tmap_lookup_op_r_uniq_equiv; [apply VALID|done]. }

  (* Unique: stack unchanged *)
  destruct (for_each_lookup_case_2 _ _ _ _ _ Eqα') as [EQ1 _].
  specialize (EQ1 O) as (stk & stk' & Eqstk & Eqstk' & ACC1); [rewrite LenT; lia|].
  rewrite shift_loc_0_nat in Eqstk, Eqstk'.
  move : ACC1. case access1 as [[n1 stk1]|] eqn:ACC1; [|done].
  simpl. intros Eqs1. symmetry in Eqs1. simplify_eq.

  destruct SREL as (Eqst&Eqnp&Eqcs&Eqnc&AREL).
  rewrite Eqst in Eqstk. rewrite Eqcs in ACC1.

  destruct (local_unique_access_head _ _ _ _ _ _ _ _ _ ss st _ _ WFT LU Eqstk ACC1 PINV HLtrf)
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

  have TOT: tag_on_top σt.(sst) l t Unique.
  { destruct HDi as [stk' Eqstk'].
    rewrite /tag_on_top Eqstk Eqstk' /= -Eqpit -Eqti. destruct it. by eexists. }

  rewrite (_: mkState σs.(shp) σt.(sst) σs.(scs) σs.(snp) σs.(snc) = σs) in STEPS;
    last first. { rewrite -Eqst. by destruct σs. }

  (* we read s' from σs(l), we know [ss] is in σs(l), now we have to prove that
    s' = ss *)
  assert (s' = ss).
  { specialize (PINV _ _ _ HLtrf) as [? PINV].
    specialize (PINV l ss st). rewrite lookup_fmap Eqs in PINV.
    specialize (PINV ltac:(done)) as (?&?&?).
    - destruct LU; subst k; [done|].
      exists stk, Unique, it.(protector). split; last split; [done| |done].
      destruct HDi as [? HDi]. rewrite HDi. rewrite -Eqpit -Eqti.
      destruct it; by left.
    - by simplify_eq. }
  subst s'.

  have STEPSS: (Copy (Place l (Tagged t) T), σs) ~{fs}~>* (#[ss]%E, σs)
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

Lemma sim_body_copy_unique_l
  fs ft (r r': resUR) (h: heaplet) n (l: loc) t T (ss st: scalar) et σs σt Φ :
  tsize T = 1%nat →
  r ≡ r' ⋅ res_tag t tkUnique h →
  h !! l = Some (ss,st) →
  (r ⊨{n,fs,ft} (#[ss], σs) ≥ (et, σt) : Φ : Prop) →
  r ⊨{n,fs,ft} (Copy (Place l (Tagged t) T), σs) ≥ (et, σt) : Φ.
Proof. apply sim_body_copy_local_unique_l. by right. Qed.

Lemma sim_body_copy_local_l fs ft r r' n l tg ty ss st et σs σt Φ :
  tsize ty = 1%nat →
  r ≡ r' ⋅ res_loc l [(ss,st)] tg →
  (r ⊨{n,fs,ft} (#[ss], σs) ≥ (et, σt) : Φ) →
  r ⊨{n,fs,ft}
    (Copy (Place l (Tagged tg) ty), σs) ≥ (et, σt)
  : Φ.
Proof.
  intros Hty Hr. eapply sim_body_copy_local_unique_l; [by left|..]; eauto.
  by rewrite lookup_insert.
Qed.

(* Public SRO copy *)
Lemma sim_body_copy_public_l
  fs ft (r r': resUR) (h: heaplet) n (l: loc) t T (ss st: scalar) et σs σt Φ :
  tsize T = 1%nat →
  r ≡ r' ⋅ res_tag t tkPub h →
  h !! l = Some (ss,st) →
  (∀ r', arel r' ss st → r ⋅ r' ⊨{n,fs,ft} (#[ss], σs) ≥ (et, σt) : Φ : Prop) →
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

  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL).
  (* some lookup properties *)
  have [h' HLtrf]: ∃ h', (r_f ⋅ r).(rtm) !! t ≡
    Some (to_tgkR tkPub, h' ⋅ (to_agree <$> h)).
  { setoid_rewrite Eqr. setoid_rewrite cmra_assoc.
    apply tmap_lookup_op_r_equiv_pub.
    - move : VALID. rewrite Eqr cmra_assoc => VALID. apply VALID.
    - rewrite res_tag_lookup //. }
  have HLl : (h' ⋅ (to_agree <$> h)) !! l ≡ Some (to_agree (ss, st)).
  { move : (proj1 VALID t). rewrite HLtrf. move => [_ /= /(_ l)].
    rewrite lookup_op lookup_fmap Eqs /=.
    destruct (h' !! l) as [sst|] eqn:Eql; rewrite Eql; [|by rewrite left_id].
    rewrite -Some_op => /agree_op_inv ->. by rewrite agree_idemp. }

  (* Public: stack unchanged *)
  destruct (for_each_lookup_case_2 _ _ _ _ _ Eqα') as [EQ1 _].
  specialize (EQ1 O) as (stk & stk' & Eqstk & Eqstk' & ACC1); [rewrite LenT; lia|].
  rewrite shift_loc_0_nat in Eqstk, Eqstk'.
  move : ACC1. case access1 as [[n1 stk1]|] eqn:ACC1; [|done].
  simpl. intros Eqs1. symmetry in Eqs1. simplify_eq.

  destruct SREL as (Eqst&Eqnp&Eqcs&Eqnc&AREL).
  rewrite Eqst in Eqstk. rewrite Eqcs in ACC1.

  destruct (public_read_head _ _ _ _ _ _ _ _ _ _ _ Eqstk ACC1 WSAT1 HLtrf HLl)
    as (it & Init & Eqti & NDIS & HDi & Eqhpt & Eqhps & AREL').
  apply arel_persistent in AREL'.
  rewrite Eqs' in Eqhps. simplify_eq.

  have ?: α' = σt.(sst).
  { move : Eqα'.
    rewrite LenT /= /memory_read /= /= shift_loc_0_nat Eqst Eqstk /= Eqcs ACC1 /=.
    destruct (tag_SRO_top_access σt.(scs) stk t HDi) as [ns Eqss].
    rewrite ACC1 in Eqss. simplify_eq. rewrite insert_id //. by inversion 1. }
  subst α'. rewrite Eqstk in Eqstk'. symmetry in Eqstk'. simplify_eq.
  rewrite (_: mkState σs.(shp) σt.(sst) σs.(scs) σs.(snp) σs.(snc) = σs) in STEPS;
    last first. { rewrite -Eqst. by destruct σs. }

  have STEPSS: (Copy (Place l (Tagged t) T), σs) ~{fs}~>* (#[ss]%E, σs)
    by apply rtc_once.
  have NT' := never_stuck_tstep_once _ _ _ _ _ STEPS NT.
  (* TODO: the following is the same in most proofs, generalize it *)
  specialize (CONT _ AREL').
  punfold CONT.
  move : WSAT1. rewrite -(cmra_core_r (r_f ⋅ r)) -cmra_assoc. intros WSAT.
  specialize (CONT NT' _ WSAT) as [RE TE ST]. split; [done|..].
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

End left.
