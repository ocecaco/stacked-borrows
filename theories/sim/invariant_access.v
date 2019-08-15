From stbor.lang Require Import steps_retag.
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
  destruct HD as (stk1 & stk2 & opro & Eq1 & Eq2).
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

(** For writing to heaplet *)
Instance write_hpl_proper (l: loc) v :
  Proper ((≡) ==> (≡)) (write_hpl l v).
Proof.
  intros h1 h2 Eq. revert l h1 h2 Eq.
  induction v as [|s v IH]; intros l h1 h2 Eq; simpl; [done|].
  apply IH. intros l'.
  case (decide (l' = l)) => [->|?].
  - by rewrite 2!lookup_insert.
  - do 2 (rewrite lookup_insert_ne; [|done]). apply Eq.
Qed.

Lemma write_hpl_lookup (l: loc) v (h: heaplet) :
  (∀ (i: nat) s, (i < length v)%nat →
    write_hpl l v h !! (l +ₗ i) = Some s →
    v !! i = Some s) ∧
  (∀ (l': loc), (∀ (i: nat), (i < length v)%nat → l' ≠ l +ₗ i) →
    write_hpl l v h !! l' = h !! l').
Proof.
  revert l h. induction v as [|s v IH]; move => l h; simpl;
    [split; [intros; by lia|done]|].
  destruct (IH (l +ₗ 1) (<[l:=s]> h)) as [IH1 IH2].
  split.
  - intros i si Lt. destruct i as [|i].
    + rewrite shift_loc_0_nat /= IH2.
      * by rewrite lookup_insert.
      * move => ? _.
        rewrite shift_loc_assoc -{1}(shift_loc_0 l) => /shift_loc_inj ?. by lia.
    + intros Eq. rewrite /= (IH1 _ si) ; [eauto|lia|].
      by rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
  - intros l' Lt. rewrite IH2.
    + rewrite lookup_insert_ne; [done|].
      move => ?. subst l'. apply (Lt O); [lia|by rewrite shift_loc_0_nat].
    + move => i Lti. rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
      apply Lt. by lia.
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
  - destruct HD as (stk1&stk2&opro&Eq1& HD).
    rewrite Eq1 in Eqstk. simplify_eq.
    have ?: opro = it.(protector).
    { destruct (state_wf_stack_item _ WFT _ _ Eq1) as [_ ND].
      have Eq :=
        stack_item_tagged_NoDup_eq _ _ (mkItem Unique (Tagged t) opro) t ND Init
          ltac:(by left) Eqti eq_refl.
      by inversion Eq. } subst opro.
    by eexists.
Qed.
