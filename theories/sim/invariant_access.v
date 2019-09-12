From stbor.lang Require Import steps_retag steps_progress.
From stbor.sim Require Export instance.

Set Default Proof Using "Type".

Instance insert_gmap_proper `{Countable K} {A : cmraT} (i: K) :
  Proper ((≡) ==> (≡) ==> (≡)) (insert (M:=gmap K A) i).
Proof.
  intros m1 m2 Eq a1 a2 Eqa i'. case (decide (i = i')) => [->|?].
  - by rewrite 2!lookup_insert Eq.
  - do 2 (rewrite lookup_insert_ne //).
Qed.

Lemma priv_loc_not_public r l t t' :
  priv_loc r l t →
  (∃ (h: heapletR), r.(rtm) !! t' ≡ Some (to_tgkR tkPub, h)) →
  t ≠ t'.
Proof.
  intros [k1 [h1 [Eqh1 [Inl Eqk]]]] [h2 Eqh2] ?. subst t'. move : Eqh2. rewrite Eqh1.
  intros [Eq1 ?]%Some_equiv_inj. simpl in *.
  destruct Eqk as [|[]]; subst k1.
  - inversion Eq1.
  - apply Cinr_inj in Eq1. inversion Eq1.
Qed.

Lemma local_access_eq r l (h: heapletR) t t' stk n stk' kind σs σt :
  σt.(sst) !! l = Some stk →
  access1 stk kind t' σt.(scs) = Some (n, stk') →
  wsat r σs σt →
  r.(rtm) !! t ≡ Some (to_tgkR tkLocal, h) →
  is_Some (h !! l) →
  t' = Tagged t ∧ stk' = stk.
Proof.
  intros Eql Eqstk WSAT Eqt' Inl.
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL).
  specialize (PINV _ _ _ Eqt') as [? Eqs].
  destruct Inl as [sst' Eqsst'].
  have VLh: ✓ h.
  { apply (pair_valid (to_tgkR tkLocal) h).
    rewrite -pair_valid -Some_valid -Eqt'. apply VALID. }
  have VLsst: ✓ sst'.
  { change (✓ (Some sst')). rewrite -Eqsst'. apply VLh. }
  apply to_agree_uninj in VLsst as [[ss st] VLsst].
  specialize (Eqs l ss st). rewrite Eqsst' in Eqs.
  destruct Eqs as [Eqh1 [Eqh2 Eqs]]; [by rewrite VLsst|done|].
  rewrite /= Eql in Eqs. simplify_eq.
  destruct (access1_in_stack _ _ _ _ _ _ Eqstk)
    as [it [?%elem_of_list_singleton [Eqt ?]]].
  subst. split; [done|].
  destruct (tag_unique_head_access σt.(scs) (init_stack (Tagged t)) (Tagged t) None kind)
    as [stk1 Eq1]; [by exists []|].
  rewrite Eq1 in Eqstk. by simplify_eq.
Qed.

Lemma protector_access_eq r l (h: heapletR) t t' stk n stk' kind σs σt :
  σt.(sst) !! l = Some stk →
  access1 stk kind t' σt.(scs) = Some (n, stk') →
  wsat r σs σt →
  r.(rtm) !! t ≡ Some (to_tgkR tkUnique, h) →
  is_Some (h !! l) →
  (∃ (c: call_id) T L, r.(rcm) !! c ≡ Excl' T ∧ T !! t = Some L ∧ l ∈ L) →
  t' = Tagged t.
Proof.
  intros Eql Eqstk WSAT Eqh Inl PRO.
  destruct PRO as (c & T & tls & Eqc & EqT & Intls).
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL).

  destruct Inl as [sa Eqs].
  move : (proj1 VALID t). rewrite Eqh. intros [_ VALh].
  specialize (VALh l). rewrite Eqs in VALh.
  apply to_agree_uninj in VALh as [[ss st] Eqsa].
  have Eqss : h !! l ≡ Some (to_agree (ss, st)) by rewrite Eqsa Eqs.
  specialize (PINV _ _ _ Eqh) as [? PINV].
  specialize (PINV _ _ _ Eqss).

  specialize (CINV _ _ Eqc) as [Ltc CINV].
  specialize (CINV _ _ EqT) as [Ltt CINV].
  specialize (CINV _ Intls) as (stk1 & pm1 & Eqstk1 & In1 & NDIS1).
  rewrite Eqstk1 in Eql. simplify_eq.
  destruct PINV as [Eqs1 [Eqs2 HD]]; [by do 3 eexists|].
  destruct HD as (stk1 & Eq1 & opro & stk2 & Eq2).
  rewrite Eq1 in Eqstk1.
  simplify_eq.
  have ?: opro = Some c.
  { destruct (state_wf_stack_item _ WFT _ _ Eq1) as [_ ND].
    have Eq :=
      stack_item_tagged_NoDup_eq _ _ (mkItem Unique (Tagged t) opro) t ND In1
        ltac:(by left) eq_refl eq_refl.
    by inversion Eq. } subst opro.
  eapply (access1_incompatible_head_protector _ _ _ _ _ _ _ _ ltac:(by eexists) Ltc); eauto.
Qed.

Lemma priv_loc_UB_access_eq r l kind σs σt t t' stk :
  σt.(sst) !! l = Some stk →
  is_Some (access1 stk kind t' σt.(scs)) →
  wsat r σs σt →
  priv_loc r l t →
  t' = Tagged t.
Proof.
  intros Eql [[]] WSAT (k & h & Eqh & Inl & [|[? PRO]]); subst k.
  - eapply local_access_eq; eauto.
  - eapply protector_access_eq; eauto.
Qed.

Lemma priv_pub_access_UB (r: resUR) l kind σs σt t t' stk :
  σt.(sst) !! l = Some stk →
  is_Some (access1 stk kind t' σt.(scs)) →
  wsat r σs σt →
  priv_loc r l t →
  (if t' is (Tagged t2)
   then ∃ (h: heapletR), r.(rtm) !! t2 ≡ Some (to_tgkR tkPub, h)
   else True) →
  False.
Proof.
  intros Eql IS WSAT PV PB.
  have Eq := priv_loc_UB_access_eq _ _ _ _ _ _ _ _ Eql IS WSAT PV.
  rewrite Eq in PB.
  by apply (priv_loc_not_public _ _ _ _ PV PB).
Qed.

Lemma local_unique_access_head r σs (σt: state) l stk kind n' stk' t ss st k h
  (WFT: Wf σt) (LU: k = tkLocal ∨ k = tkUnique):
  σt.(sst) !! l = Some stk →
  access1 stk kind (Tagged t) σt.(scs) = Some (n', stk') →
  tmap_inv r σs σt →
  r.(rtm) !! t ≡ Some (to_tgkR k, h) →
  h !! l ≡ Some $ to_agree (ss,st) →
  ∃ it, it.(perm) = Unique ∧ it.(tg) = Tagged t ∧ is_stack_head it stk ∧
    σt.(shp) !! l = Some st ∧ σs.(shp) !! l = Some ss.
Proof.
  intros Eqstk ACC1 PINV HL Eqs.
  specialize (PINV _ _ _ HL) as [? PINV].
  specialize (PINV _ _ _ Eqs).
  destruct (access1_in_stack _ _ _ _ _ _ ACC1) as (it & Init & Eqti & NDIS).
  destruct PINV as [Eqss [? HD]].
  { destruct LU; subst k; [done|].
    rewrite /= -Eqti. exists stk, it.(perm), it.(protector).
    repeat split; [done| |done]. by destruct it. }
  exists (mkItem Unique (Tagged t) it.(protector)).
  repeat split; [|done..].
  destruct LU; subst k.
  - rewrite /= Eqstk in HD. simplify_eq. apply elem_of_list_singleton in Init.
    subst it. simpl. by eexists.
  - destruct HD as (stk1&Eq1&opro& stk2&HD).
    rewrite Eq1 in Eqstk. simplify_eq.
    have ?: opro = it.(protector).
    { destruct (state_wf_stack_item _ WFT _ _ Eq1) as [_ ND].
      have Eq :=
        stack_item_tagged_NoDup_eq _ _ (mkItem Unique (Tagged t) opro) t ND Init
          ltac:(by left) Eqti eq_refl.
      by inversion Eq. } subst opro.
    by eexists.
Qed.

Lemma public_read_head r σs (σt: state) l stk n' stk' t ss st h:
  σt.(sst) !! l = Some stk →
  access1 stk AccessRead (Tagged t) σt.(scs) = Some (n', stk') →
  wsat r σs σt →
  r.(rtm) !! t ≡ Some (to_tgkR tkPub, h) →
  h !! l ≡ Some $ to_agree (ss,st) →
  ∃ it, it ∈ stk ∧ it.(tg) = Tagged t ∧ it.(perm) ≠ Disabled ∧
    t ∈ active_SRO stk ∧
    σt.(shp) !! l = Some st ∧ σs.(shp) !! l = Some ss ∧ arel r ss st.
Proof.
  intros Eqstk ACC WSAT HL Eqs.
  have WSAT1 := WSAT.
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL).
  destruct SREL as (Eqst & Eqnp & Eqcs & Eqnc & PV).
  specialize (PINV _ _ _ HL) as [? PINV].
  specialize (PINV _ _ _ Eqs).
  destruct (access1_in_stack _ _ _ _ _ _ ACC) as (it & Init & Eqti & NDIS).
  destruct PINV as [Eqss [Eqss' HD]].
  { rewrite /= -Eqti. exists stk, it.(perm), it.(protector).
    repeat split; [done| |done]. by destruct it. }
  destruct HD as (stk1 & Eqstk1 & InSRO).
  rewrite Eqstk1 in Eqstk. simplify_eq.
  exists it. repeat split; [done..|].
  destruct (PV l) as [PB|[t' PR]]; cycle 2.
  { exfalso.
    have Eq :=
      priv_loc_UB_access_eq _ _ AccessRead σs σt t' (Tagged t) _ Eqstk1
        ltac:(by eexists) WSAT1 PR.
    simplify_eq.
    destruct PR as (k1 & h1 & Eqh1 & ? & CASE).
    move : Eqh1. rewrite HL.
    rewrite -(left_id None op (Some _)).
    destruct CASE as [|[]]; subst k1.
    - apply tagKindR_local_exclusive_r.
    - apply tagKindR_uniq_exclusive_r. }
  { rewrite (state_wf_dom _ WFT) elem_of_dom. by eexists. }
  destruct (PB _ Eqss) as (st' & Eqst' & AREL). rewrite Eqst' in Eqss'.
  by simplify_eq.
Qed.

Lemma priv_loc_UB_retag_access_eq r σs σt c l old new mut T kind α' nxtp'
  (FRZ: if mut is Immutable then is_freeze T else True)
  (N2P: kind ≠ TwoPhase) :
  retag σt.(sst) σt.(snp) σt.(scs) c l old kind (RefPtr mut) T = Some (new, α', nxtp') →
  wsat r σs σt →
  ∀ i t, (i < tsize T)%nat →
  priv_loc r (l +ₗ i) t →
  (if old is (Tagged t2)
   then ∃ (h: heapletR), r.(rtm) !! t2 ≡ Some (to_tgkR tkPub, h)
   else True) →
   False.
Proof.
  intros RT WSAT i t Lti.
  have NZST: (0 < tsize T)%nat by lia.
  destruct (retag_change_ref_NZST _ _ _ _ _ _ _ _ _ _ _ _ NZST RT);
    subst new nxtp'.
  destruct (retag_Some_Ref _ _ _ _ _ _ _ _ _ _ _ _ NZST FRZ N2P RT _ Lti)
    as (stk & stk' & Eqstk & Eqstk' & GR).
  apply grant_access1 in GR; [|by destruct mut].
  revert Eqstk GR WSAT. by apply priv_pub_access_UB.
Qed.
