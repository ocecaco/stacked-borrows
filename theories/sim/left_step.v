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

(* Protected write *)
Lemma sim_body_write_non_ptr_protected_l
  fs ft (r r' r'': resUR) (h: heaplet) n (l: loc) t T (ss st ss': scalar)
  c Ts L et σs σt Φ :
  (if ss' is ScPtr l' t' then False else True) →
  let tk := tkUnique in
  tsize T = 1%nat →
  r ≡ r' ⋅ res_tag t tk h →
  r' ≡ r'' ⋅ res_cs c Ts →
  h !! l = Some (ss, st) →
  Ts !! t = Some L →
  l ∈ L →
  (σt.(shp) !! l = Some st →
    let σs' := mkState (<[l := ss']> σs.(shp)) σs.(sst) σs.(scs) σs.(snp) σs.(snc) in
    let rt' := res_tag t tk (<[l := (ss', st)]> h) in
    r' ⋅ rt' ⊨{n,fs,ft} (#[☠], σs') ≥ (et, σt) : Φ : Prop) →
  r ⊨{n,fs,ft} (Place l (Tagged t) T <- #[ss'], σs) ≥ (et, σt) : Φ.
Proof.
  intros NL tk LenT Eqr Eqr' Eqs EqTs InL CONT. pfold.
  intros NT r_f WSAT. have WSAT1 := WSAT.

  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL).

  have HLc: (r_f ⋅ r).(rcm) !! c ≡ Excl' Ts.
  { rewrite Eqr Eqr' 2!cmra_assoc lookup_op right_id.
    apply (cmap_lookup_op_unique_included (res_cs c Ts).(rcm)).
    - move : (proj2 VALID). rewrite Eqr Eqr' 2!cmra_assoc => VALID2.
      by apply (cmra_valid_included _ _ VALID2), cmra_included_l.
    - by apply cmra_included_r.
    - by rewrite res_cs_lookup. }
  destruct (CINV _ _ HLc) as [INc CINVc].
  specialize (CINVc _ _ EqTs) as [Ltc CINVc].
  specialize (CINVc _ InL) as (stk & pm & Eqstk & Instk & NDIS).

  have HLtrf : (r_f ⋅ r).(rtm) !! t ≡ Some (to_tgkR tk, to_agree <$> h).
  { rewrite ->Eqr in VALID. move : VALID. rewrite cmra_assoc => VALID.
    rewrite Eqr cmra_assoc.
    apply tmap_lookup_op_r_uniq_equiv; [apply VALID|].
    by rewrite res_tag_lookup. }
  have HLl : (to_agree <$> h) !! l ≡ Some (to_agree (ss, st))
    by rewrite lookup_fmap Eqs.

  destruct (PINV _ _ _ HLtrf) as [Ltt Pt].
  specialize (Pt l ss st HLl) as (Eqst & Eqss & TPO).
  { by exists stk, pm, (Some c). }

  have [ns Eqstk']: ∃ n, access1 stk AccessWrite (Tagged t) σs.(scs) = Some (n, stk).
  { destruct TPO as (stk1 & Eqstk1 & pro & TPO).
    rewrite Eqstk1 in Eqstk. simplify_eq.
    by eapply tag_unique_head_access. }
  have Eqα : memory_written σs.(sst) σs.(scs) l (Tagged t) (tsize T) = Some σs.(sst).
  { destruct SREL as (EQss & _).
    rewrite LenT /memory_written /= shift_loc_0_nat EQss
            Eqstk /= Eqstk' /= insert_id //. }

  set σs' := mkState (<[l := ss']> σs.(shp)) σs.(sst) σs.(scs) σs.(snp) σs.(snc).
  have STEPS: ((Place l (Tagged t) T <- #[ss'])%E, σs) ~{fs}~> (#[☠]%E, σs').
  { eapply (head_step_fill_tstep _ []); eapply write_head_step'; eauto.
    - move => ?? /elem_of_list_singleton ?. by subst ss'.
    - clear -Eqss LenT.
      intros i. rewrite LenT=>?. destruct i; [|lia].
      rewrite shift_loc_0_nat. by eapply elem_of_dom_2. }
  have STEPSS: ((Place l (Tagged t) T <- #[ss'])%E, σs) ~{fs}~>* (#[☠]%E, σs')
    by apply rtc_once.

  set rt' := res_tag t tk (<[l := (ss', st)]> h).
  have EQrcm: (r_f ⋅ r).(rcm) ≡ (r_f ⋅ r' ⋅ rt').(rcm)
    by rewrite Eqr cmra_assoc.
  have HLNt: (r_f ⋅ r').(rtm) !! t = None.
  { destruct ((r_f ⋅ r').(rtm) !! t) as [ls|] eqn:Eqls; [|done].
    exfalso. move : HLtrf.
    rewrite Eqr cmra_assoc lookup_op Eqls res_tag_lookup.
    apply tagKindR_exclusive_heaplet. }
  have HLtrf' :
    (r_f ⋅ r' ⋅ rt').(rtm) !! t ≡ Some (to_tgkR tk, to_hplR (<[l:=(ss', st)]> h)).
  { by rewrite lookup_op HLNt res_tag_lookup left_id. }

  have VALIDr: ✓ (r_f ⋅ r' ⋅ rt').
  { move : VALID. rewrite Eqr cmra_assoc => VALID.
    apply (local_update_discrete_valid_frame _ _ _ VALID).
    apply res_tag_uniq_local_update; [by right|done]. }

  have WSAT': wsat (r_f ⋅ (r' ⋅ rt')) σs' σt.
  { rewrite cmra_assoc.
    split; last split; last split; last split; last split.
  - by apply (tstep_wf _ _ _ STEPS WFS).
  - done.
  - done.
  - intros t1 k1 h1 Eqh1.
    case (decide (t1 = t)) => ?; [subst t1|].
    + split; [done|].
      specialize (PINV _ _ _ HLtrf) as [? PINV].
      have [? Eqh]: k1 = tk ∧ h1 ≡ to_agree <$> (<[l:=(ss', st)]> h).
      { move : Eqh1. rewrite HLtrf'.
        by intros [?%leibniz_equiv_iff%to_tgkR_inj ?]%Some_equiv_inj. } subst k1.
      intros l1 ss1 st1. rewrite Eqh lookup_fmap.
      case (decide (l1 = l)) => ?; [subst l1|].
      * rewrite lookup_insert. intros Eq%Some_equiv_inj%to_agree_inj.
        symmetry in Eq. simplify_eq.
        rewrite /= lookup_insert. intros PRE. do 2 (split; [done|]).
        specialize (PINV l ss st). rewrite lookup_fmap Eqs in PINV.
        by specialize (PINV ltac:(done) PRE) as (Eqst1 & Eqss1 & HD).
      * rewrite lookup_insert_ne // -lookup_fmap.
        intros Eq. specialize (PINV _ _ _ Eq).
        by rewrite /σs' lookup_insert_ne.

    + have Eqh : (r_f ⋅ r).(rtm) !! t1 ≡ Some (to_tgkR k1, h1).
      { rewrite Eqr cmra_assoc lookup_op res_tag_lookup_ne; [|done].
        move : Eqh1. by rewrite lookup_op res_tag_lookup_ne. }
      specialize (PINV _ _ _ Eqh) as [Ltt1 PINV].
      split; [done|]. intros l1 ss1 st1 Eql1 PRE.
      specialize (PINV _ _ _ Eql1 PRE) as (Eqst1 & Eqss1 & HPO).
      rewrite /= lookup_insert_ne; [done|].
      intros ?. subst l1.
      (* t1 ≠ t, t is top of stack(l), t1 is top or SRO in stack (l).
            This cannot happen. *)
      exfalso.
      have ND := proj2 (state_wf_stack_item _ WFT _ _ Eqstk).
      destruct k1; simpl in *.
      { rewrite Eqstk in HPO. simplify_eq.
        eapply (access1_write_remove_incompatible_head _ (Tagged t) t1 _ _ _ ND);
          eauto.
        - by exists None, [].
        - by inversion 1.
        - by left. }
      { destruct HPO as (stk1 & Eqstk1 & opro & HD).
        rewrite Eqstk1 in Eqstk. simplify_eq.
        eapply (access1_write_remove_incompatible_head _ (Tagged t) t1 _ _ _ ND);
          eauto.
        - by inversion 1.
        - destruct HD as [? HD]. rewrite HD. by left. }
      { destruct HPO as (stk1 & Eqstk1 & HD).
        rewrite Eqstk1 in Eqstk. simplify_eq.
        destruct PRE as (stk1 & pm1 & opro & Eqstk & In1 & ?).
        rewrite Eqstk in Eqstk1. simplify_eq.
        eapply (access1_write_remove_incompatible_active_SRO _
                  (Tagged t) t1 _ _ _ ND); eauto. }
  - move => ??. rewrite -EQrcm. by apply CINV.
  - destruct SREL as (?&?&?&?& PB). do 4 (split; [done|]).
    move => l1 /= InD.
    case (decide (l1 = l)) => ?; [subst l1|].
    { right.
      exists t, tk, (to_hplR (<[l := (ss', st)]> h)). split; last split.
      - done.
      - rewrite /to_hplR lookup_fmap lookup_insert. by eexists.
      - right. split; [done|]. exists c, Ts, L.
        rewrite -EQrcm. by rewrite HLc. }
    specialize (PB _ InD) as [PB|[t1 PV]]; [left|right].
    { intros st1. rewrite /= lookup_insert_ne; [|done].
      move => /PB [ss1 [Eqss1 ARELs]].
      exists ss1. split; [done|].
      move : ARELs. rewrite Eqr cmra_assoc.
      apply arel_res_tag_overwrite. by right. }
    destruct PV as (k1 & h1 & Eqt1 & IS1 & CASE).
    case (decide (t1 = t)) => ?; [subst t1|].
    { have [? Eqh]: k1 = tk ∧ h1 ≡ to_agree <$> h.
      { move : Eqt1. rewrite HLtrf.
        by intros [?%leibniz_equiv_iff%to_tgkR_inj ?]%Some_equiv_inj. }
      subst k1.
      exists t, tk, (to_hplR (<[l := (ss', st)]> h)). split; last split.
      - done.
      - rewrite /to_hplR lookup_fmap lookup_insert_ne; [|done].
        move : (Eqh l1). destruct IS1 as [? Eq1].
        rewrite Eq1 lookup_fmap.
        destruct (h !! l1) eqn:Eqhl1; rewrite Eqhl1;
          [by eexists|by inversion 1].
      - by setoid_rewrite <- EQrcm. }
    exists t1, k1, h1. setoid_rewrite <- EQrcm. split; [|done].
    rewrite lookup_op res_tag_lookup_ne; [|done].
    move : Eqt1. by rewrite Eqr cmra_assoc lookup_op res_tag_lookup_ne. }

  have NT' := never_stuck_tstep_once _ _ _ _ _ STEPS NT.
  specialize (CONT Eqst). punfold CONT.
  specialize (CONT NT' _ WSAT') as [RE TE ST]. split; [done|..].
  - intros. specialize (TE _ TERM) as (vs' & σs1 & r1 & STEPS' & POST).
    exists vs', σs1, r1. split; [|done]. etrans; eauto.
  - inversion ST.
    + constructor 1. intros.
      destruct (STEP _ _ STEPT) as (es' & σs1 & r1 & n' & STEPS' & POST).
      exists es', σs1, r1, n'. split; [|done].
      left. destruct STEPS' as [?|[]].
      * eapply tc_rtc_l; eauto.
      * simplify_eq. by apply tc_once.
    + econstructor 2; eauto. by etrans.
Qed.

End left.
