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
  (∃ (h: heapletR), r.(rtm) !! t' ≡ Some (to_tagKindR tkPub, h)) →
  t ≠ t'.
Proof.
  intros [h1 [Eqh1 ?]] [h2 Eqh2] ?. subst t'. move : Eqh2. rewrite Eqh1.
  intros [Eq1 ?]%Some_equiv_inj. by inversion Eq1.
Qed.

Lemma local_access_eq r l t t' stk n stk' kind σs σt :
  σt.(sst) !! l = Some stk →
  access1 stk kind t' σt.(scs) = Some (n, stk') →
  wsat r σs σt →
  (r.(rlm) !! l : optionR tagR) ≡ Some (to_tagR t) →
  t' = Tagged t ∧ stk' = stk.
Proof.
  intros Eql Eqstk WSAT Eqt'.
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  specialize (LINV _ _ Eqt') as [? [Eqs ?]]. rewrite Eql in Eqs. simplify_eq.
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
  intros Eql ACC WSAT (h & Eqh & [LOC|PRO]).
  { destruct ACC as [[]]. eapply local_access_eq; eauto. }
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  specialize (PINV _ _ _ Eqh) as [Lt PINV].
  destruct PRO as (c & T & Eqc & InT & Inl). have Inl' := Inl.
  move : Inl'. rewrite elem_of_dom. intros [sa Eqs].
  move : (proj1 (proj1 VALID) t). rewrite Eqh. intros [_ VALh].
  specialize (VALh l). rewrite Eqs in VALh.
  apply to_agree_uninj in VALh as [s Eqsa].
  have Eqss : h !! l ≡ Some (to_agree s) by rewrite Eqsa Eqs.
  specialize (PINV _ _ Eqss stk Eql).
  specialize (CINV _ _ Eqc). simpl in CINV. destruct CINV as [Ltc CINV].
  specialize (CINV _ InT) as [Ltt CIN].
  specialize (CIN _ _ Eqh _ Inl) as (stk1 & pm1 & Eqstk1 & In1 & NDIS1).
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
   then ∃ (h: heapletR), r.(rtm) !! t2 ≡ Some (to_tagKindR tkPub, h)
   else True) →
  False.
Proof.
  intros Eql IS WSAT PV PB.
  have Eq := priv_loc_UB_access_eq _ _ _ _ _ _ _ _ Eql IS WSAT PV.
  rewrite Eq in PB.
  by apply (priv_loc_not_public _ _ _ _ PV PB).
Qed.

(** For writing to heaplet *)
Fixpoint write_heaplet (l: loc) (v: value) (h: heaplet) :=
  match v with
  | [] => h
  | s :: v =>
      write_heaplet (l +ₗ 1) v (if h !! l then <[l := s]> h else h)
  end.

Instance write_heaplet_proper (l: loc) (v: value) :
  Proper ((≡) ==> (≡)) (write_heaplet l v).
Proof.
  intros h1 h2 Eq. revert l h1 h2 Eq.
  induction v as [|s v IH]; intros l h1 h2 Eq; simpl; [done|].
  apply IH. move : (Eq l).
  destruct (h1 !! l) as [s1|] eqn:Eq1, (h2 !! l) as [s2|] eqn:Eq2; [..|done];
    rewrite Eq1 Eq2; intros Eql; [by rewrite Eq|by inversion Eql..].
Qed.

Lemma write_heaplet_dom (l: loc) (v: value) h :
  dom (gset loc) (write_heaplet l v h) ≡ dom (gset loc) h.
Proof.
  revert l h.
  induction v as [|s v IH]; intros l h; simpl; [done|].
  rewrite IH. destruct (h !! l) eqn:Eq; [|done].
  rewrite dom_map_insert_is_Some //. by eexists.
Qed.

Lemma write_heaplet_empty l v : write_heaplet l v ∅ ≡ ∅.
Proof. revert l. induction v as [|?? IH]; [done|]; intros l. apply IH. Qed.

Lemma write_heaplet_lookup (l: loc) (vl: value) (h: heaplet) :
  (∀ (i: nat) s, (i < length vl)%nat →
    write_heaplet l vl h !! (l +ₗ i) = Some s →
    vl !! i = Some s) ∧
  (∀ (l': loc), (∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i) →
    write_heaplet l vl h !! l' = h !! l').
Proof.
  revert l h. induction vl as [|v vl IH]; move => l h; simpl;
    [split; [intros; by lia|done]|].
  destruct (IH (l +ₗ 1) (if h !! l then <[l:=v]> h else h)) as [IH1 IH2].
  split.
  - intros i s Lt. destruct i as [|i].
    + rewrite shift_loc_0_nat /=. rewrite IH2; [|].
      * destruct (h !! l) eqn:Eql; [by rewrite lookup_insert|].
        rewrite Eql; by inversion 1.
      * move => ? _.
        rewrite shift_loc_assoc -{1}(shift_loc_0 l) => /shift_loc_inj ?. by lia.
    + intros Eq. rewrite /= (IH1 _ s) ; [eauto|lia|].
      by rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
  - intros l' Lt. rewrite IH2.
    + destruct (h !! l) eqn:Eql; [|done].
      rewrite lookup_insert_ne; [done|].
      move => ?. subst l'. apply (Lt O); [lia|by rewrite shift_loc_0_nat].
    + move => i Lti. rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
      apply Lt. by lia.
Qed.

Lemma unique_access_head r σs σ l stk kind n' stk' t s h :
  σ.(sst) !! l = Some stk →
  access1 stk kind (Tagged t) σ.(scs) = Some (n', stk') →
  tmap_inv r σs σ →
  r.(rtm) !! t ≡ Some (to_tagKindR tkUnique, h) →
  h !! l ≡ Some $ to_agree s →
  ∃ it, it.(perm) = Unique ∧ it.(tg) = Tagged t ∧ is_stack_head it stk ∧
    σ.(shp) !! l = Some s.
Proof.
  intros Eqstk ACC1 PINV HL Eqs.
  specialize (PINV _ _ _ HL) as [? PINV].
  specialize (PINV _ _ Eqs _ Eqstk).
  destruct (access1_in_stack _ _ _ _ _ _ ACC1) as (it & Init & Eqti & NDIS).
  destruct (PINV it.(perm) it.(protector)) as [Eqss [? HD]]; [|done|].
  { rewrite -Eqti. by destruct it. }
  by exists (mkItem Unique (Tagged t) it.(protector)).
Qed.
