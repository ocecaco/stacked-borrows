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
  intros [h1 [Eqh1 ?]] [h2 Eqh2] ?. subst t'. move : Eqh2. rewrite Eqh1.
  intros [Eq1 ?]%Some_equiv_inj. by inversion Eq1.
Qed.

Lemma local_access_eq r l tls t t' stk n stk' kind σs σt :
  σt.(sst) !! l = Some stk →
  access1 stk kind t' σt.(scs) = Some (n, stk') →
  wsat r σs σt →
  r.(rlm) !! t ≡ Some (Excl tls) →
  l ∈ tls →
  t' = Tagged t ∧ stk' = stk.
Proof.
  intros Eql Eqstk WSAT Eqt' Inl.
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  specialize (LINV _ _ Eqt') as [? Eqs]. specialize (Eqs _ Inl).
  rewrite Eql in Eqs. simplify_eq.
  destruct (access1_in_stack _ _ _ _ _ _ Eqstk)
    as [it [?%elem_of_list_singleton [Eqt ?]]].
  subst. split; [done|].
  destruct (tag_unique_head_access σt.(scs) (init_stack (Tagged t)) (Tagged t) None kind)
    as [stk1 Eq1]; [by exists []|].
  rewrite Eq1 in Eqstk. by simplify_eq.
Qed.

Lemma priv_loc_UB_access_eq r l kind σs σt t t' stk :
  σt.(sst) !! l = Some stk →
  is_Some (access1 stk kind t' σt.(scs)) →
  wsat r σs σt →
  priv_loc r l t →
  t' = Tagged t.
Proof.
  intros Eql ACC WSAT (h & Eqh & Inl & [[tls []]|PRO]).
  { destruct ACC as [[]]. eapply local_access_eq; eauto. }
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  specialize (PINV _ _ _ Eqh) as [Lt PINV].
  destruct PRO as (c & T & tls & Eqc & EqT & Intls). have Inl' := Inl.
  move : Inl'. rewrite elem_of_dom. intros [sa Eqs].
  move : (proj1 (proj1 VALID) t). rewrite Eqh. intros [_ VALh].
  specialize (VALh l). rewrite Eqs in VALh.
  apply to_agree_uninj in VALh as [[ss st] Eqsa].
  have Eqss : h !! l ≡ Some (to_agree (ss, st)) by rewrite Eqsa Eqs.
  specialize (PINV _ _ _ Eqss stk Eql).
  specialize (CINV _ _ Eqc) as [Ltc CINV].
  specialize (CINV _ _ EqT) as [Ltt CINV].
  specialize (CINV _ Intls) as (stk1 & pm1 & Eqstk1 & In1 & NDIS1).
  rewrite Eqstk1 in Eql. simplify_eq.
  specialize (PINV _ _ In1 NDIS1) as [Eqs1 [? HD]].

  destruct ACC as [[n stk'] ACC].
  apply (access1_incompatible_head_protector _ _ _ _ _ _ _ _ HD Ltc ACC).
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

Lemma unique_access_head r σs σt l stk kind n' stk' t ss st h :
  σt.(sst) !! l = Some stk →
  access1 stk kind (Tagged t) σt.(scs) = Some (n', stk') →
  tmap_inv r σs σt →
  r.(rtm) !! t ≡ Some (to_tgkR tkUnique, h) →
  h !! l ≡ Some $ to_agree (ss,st) →
  ∃ it, it.(perm) = Unique ∧ it.(tg) = Tagged t ∧ is_stack_head it stk ∧
    σt.(shp) !! l = Some st ∧ σs.(shp) !! l = Some ss.
Proof.
  intros Eqstk ACC1 PINV HL Eqs.
  specialize (PINV _ _ _ HL) as [? PINV].
  specialize (PINV _ _ _ Eqs _ Eqstk).
  destruct (access1_in_stack _ _ _ _ _ _ ACC1) as (it & Init & Eqti & NDIS).
  destruct (PINV it.(perm) it.(protector)) as [Eqss [? HD]]; [|done|].
  { rewrite -Eqti. by destruct it. }
  by exists (mkItem Unique (Tagged t) it.(protector)).
Qed.
