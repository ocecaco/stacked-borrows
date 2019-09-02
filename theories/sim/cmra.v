From iris.algebra Require Export local_updates.
From iris.algebra Require Export cmra gmap gset csum agree excl big_op.

From stbor.lang Require Export lang.

Set Default Proof Using "Type".

(** Tag map that connect tags to the heaplet that they govern *)
Inductive tag_kind := tkLocal | tkUnique | tkPub.
(* Ex() + Ex() + () *)
Definition tagKindR := csumR (exclR unitO) (csumR (exclR unitO) unitR).

Definition to_tgkR (tk: tag_kind) : tagKindR :=
  match tk with
  | tkLocal => Cinl (Excl ())
  | tkUnique => Cinr (Cinl (Excl ()))
  | tkPub => Cinr (Cinr ())
  end.

Definition heaplet := gmap loc (scalar * scalar).
Definition tmap := gmap ptr_id (tag_kind * heaplet).
Definition heapletR := gmapR loc (agreeR (prodO scalarO scalarO)).
(* ptr_id ⇀ TagKind * (loc ⇀ Ag(Scalar * Scalar)) *)
Definition tmapUR := gmapUR ptr_id (prodR tagKindR heapletR).

Definition to_hplR (h: heaplet) : heapletR := fmap to_agree h.
Definition to_tmUR (tm: tmap) : tmapUR :=
  fmap (λ kh, (to_tgkR kh.1, to_hplR kh.2)) tm.


Definition tag_locs := gmap ptr_id (gset loc).

(** CallId map that protects tags and their associated heaplet *)
(* Ex(tag ⇀ gset loc) *)
Definition callStateR := exclR (gmapO ptr_id (gsetO loc)).
Definition cmap := gmap call_id tag_locs.
(* call_id ⇀ CallState *)
Definition cmapUR := gmapUR call_id callStateR.
Definition to_cmUR (cm: cmap) : cmapUR := fmap Excl cm.

Definition res := (tmap * cmap)%type.
Definition resUR := prodUR tmapUR cmapUR.

Definition rtm (r: resUR) : tmapUR := r.1.
Definition rcm (r: resUR) : cmapUR := r.2.

Instance rtm_proper : Proper ((≡) ==> (≡)) rtm.
Proof. solve_proper. Qed.
Instance rcm_proper : Proper ((≡) ==> (≡)) rcm.
Proof. solve_proper. Qed.

Lemma local_update_discrete_valid_frame `{CmraDiscrete A} (r_f r r' : A) :
  ✓ (r_f ⋅ r) → (r_f ⋅ r, r) ~l~> (r_f ⋅ r', r') → ✓ (r_f ⋅ r').
Proof.
  intros VALID UPD. apply cmra_discrete_valid.
  apply (UPD O (Some r_f)); [by apply cmra_discrete_valid_iff|by rewrite /= comm].
Qed.

(** tag_kind properties *)
Lemma to_tgkR_valid k : valid (to_tgkR k).
Proof. by destruct k. Qed.

Lemma tagKindR_incl_eq (k1 k2: tagKindR):
  ✓ k2 → k1 ≼ k2 → k1 ≡ k2.
Proof.
  move => VAL /csum_included
    [?|[[? [? [? [? INCL]]]]|[x1 [x2 [? [? INCL]]]]]]; subst; [done|..].
  - exfalso. eapply exclusive_included; [..|apply INCL|apply VAL]; apply _.
  - move : INCL => /csum_included
      [? |[[? [? [? [? INCL]]]]|[[] [[] [? [? LE]]]]]]; subst; [done|..|done].
    exfalso. eapply exclusive_included; [..|apply INCL|apply VAL]; apply _.
Qed.

Lemma tagKindR_uniq_exclusive_l (h0 h: heapletR) mb :
  mb ⋅ Some (to_tgkR tkUnique, h0) ≡ Some (to_tgkR tkPub, h) → False.
Proof.
  destruct mb as [[k ?]|]; [rewrite -Some_op pair_op|rewrite left_id];
    intros [Eq _]%Some_equiv_inj.
  - destruct k as [[]|[]|]; simplify_eq.
  - simplify_eq.
Qed.

Lemma tagKindR_uniq_exclusive_r (h0 h: heapletR) mb :
  mb ⋅ Some (to_tgkR tkPub, h0) ≡ Some (to_tgkR tkUnique, h) → False.
Proof.
  destruct mb as [[k ?]|]; [rewrite -Some_op pair_op|rewrite left_id];
    intros [Eq _]%Some_equiv_inj.
  - destruct k as [[]|[]|]; simplify_eq.
  - simplify_eq.
Qed.

Lemma tagKindR_local_exclusive_l (h0 h: heapletR) mb :
  mb ⋅ Some (to_tgkR tkLocal, h0) ≡ Some (to_tgkR tkPub, h) → False.
Proof.
  destruct mb as [[k ?]|]; [rewrite -Some_op pair_op|rewrite left_id];
    intros [Eq _]%Some_equiv_inj.
  - destruct k as [[]|[]|]; simplify_eq.
  - simplify_eq.
Qed.

Lemma tagKindR_local_exclusive_r (h0 h: heapletR) mb :
  mb ⋅ Some (to_tgkR tkPub, h0) ≡ Some (to_tgkR tkLocal, h) → False.
Proof.
  destruct mb as [[k ?]|]; [rewrite -Some_op pair_op|rewrite left_id];
    intros [Eq _]%Some_equiv_inj.
  - destruct k as [[]|[]|]; simplify_eq.
  - simplify_eq.
Qed.

Lemma tagKindR_exclusive_heaplet' (h0 h: heapletR) mb k1 :
  mb ⋅ Some (to_tgkR tkUnique, h0) ≡ Some (to_tgkR k1, h) →
  h0 ≡ h ∧ k1 = tkUnique.
Proof.
  destruct mb as [[k ?]|]; [rewrite -Some_op pair_op|rewrite left_id];
    intros [Eq1 Eq2]%Some_equiv_inj.
  - destruct k as [[]|[]|], k1; simplify_eq.
  - by destruct k1; simplify_eq.
Qed.

Lemma tagKindR_exclusive_heaplet (h0 h: heapletR) mb :
  Some mb ⋅ Some (to_tgkR tkUnique, h0) ≡ Some (to_tgkR tkUnique, h) → False.
Proof.
  destruct mb as [c ]. rewrite -Some_op pair_op. intros [Eq _]%Some_equiv_inj.
  destruct c as [[]|[]|]; inversion Eq; simpl in *; simplify_eq.
Qed.

Lemma tagKindR_exclusive_local_heaplet (h0 h: heapletR) mb :
  Some mb ⋅ Some (to_tgkR tkLocal, h0) ≡ Some (to_tgkR tkLocal, h) → False.
Proof.
  destruct mb as [c ]. rewrite -Some_op pair_op. intros [Eq _]%Some_equiv_inj.
  destruct c as [[]|[]|]; inversion Eq; simpl in *; simplify_eq.
Qed.

Instance to_tgkR_inj : Inj (=) (=) to_tgkR.
Proof. intros [] [] ?; by simplify_eq. Qed.

Lemma tagKindR_valid (k: tagKindR) :
  valid k → ∃ k', k = to_tgkR k'.
Proof.
  destruct k as [[[]|]|[[[]|]|[]|]|]; [|done|..|done| |done|done]; intros VAL.
  - by exists tkLocal.
  - by exists tkUnique.
  - by exists tkPub.
Qed.

(** cmap properties *)
Lemma cmap_lookup_op_r (cm1 cm2: cmapUR) c (Tls: tag_locs)
  (VALID: ✓ (cm1 ⋅ cm2)) :
  cm2 !! c = Some (Excl Tls) → (cm1 ⋅ cm2) !! c = Some (Excl Tls).
Proof.
  intros HL. move : (VALID c). rewrite lookup_op HL.
  destruct (cm1 !! c) as [cs'|] eqn:Eqc; rewrite Eqc; [|done].
  rewrite -Some_op Some_valid.
  destruct cs'; auto; try inversion 1.
Qed.

Lemma cmap_lookup_op_l (cm1 cm2: cmapUR) c (Tls: tag_locs)
  (VALID: ✓ (cm1 ⋅ cm2)) :
  cm1 !! c = Some (Excl Tls) → (cm1 ⋅ cm2) !! c = Some (Excl Tls).
Proof.
  intros HL. move : (VALID c). rewrite lookup_op HL.
  destruct (cm2 !! c) as [cs'|] eqn:Eqc; rewrite Eqc; [|done].
  rewrite -Some_op Some_valid.
  destruct cs'; auto; try inversion 1.
Qed.

Lemma cmap_lookup_op_l_equiv (cm1 cm2: cmapUR) c (Tls: tag_locs)
  (VALID: ✓ (cm1 ⋅ cm2)) :
  cm1 !! c ≡ Some (Excl Tls) → (cm1 ⋅ cm2) !! c ≡ Some (Excl Tls).
Proof.
  intros HL. move : (VALID c). rewrite lookup_op HL.
  destruct (cm2 !! c) as [cs'|] eqn:Eqc; rewrite Eqc; [|done].
  rewrite -Some_op Some_valid.
  destruct cs'; auto; try inversion 1.
Qed.

Lemma cmap_lookup_op_unique_included (cm1 cm2: cmapUR) c (Tls: tag_locs)
  (VALID: ✓ cm2) (INCL: cm1 ≼ cm2) :
  cm1 !! c ≡ Some (Excl Tls) → cm2 !! c ≡ Some (Excl Tls).
Proof.
  destruct INCL as [cm' Eq]. rewrite Eq. apply cmap_lookup_op_l_equiv.
  by rewrite -Eq.
Qed.

Lemma cmap_insert_op_r (cm1 cm2: cmapUR) c Tls cs
  (VALID: ✓ (cm1 ⋅ cm2)):
  cm2 !! c = Some (Excl Tls) →
  cm1 ⋅ <[c:=cs]> cm2 = <[c:=cs]> (cm1 ⋅ cm2).
Proof.
  intros HL. apply (map_eq (cm1 ⋅ <[c:=cs]> cm2)). intros c'.
  move : (VALID c). rewrite 2!lookup_op HL.
  destruct (cm1 !! c) eqn:Eqc; rewrite Eqc; [inversion 1..|].
  intros VL.
  case (decide (c' = c)) => [->|?].
  - by rewrite 2!lookup_insert Eqc.
  - do 2 (rewrite lookup_insert_ne //). by rewrite lookup_op.
Qed.

Lemma callStateR_exclusive_Some (Tls1 Tls2: tag_locs) (cs: callStateR) :
  Some cs ⋅ Some (Excl Tls1) ≡ Some (Excl Tls2) → False.
Proof.
  rewrite -Some_op. intros Eq%Some_equiv_inj.
  destruct cs; inversion Eq; simplify_eq.
Qed.

Lemma callStateR_exclusive_eq (Tls1 Tls2: tag_locs) mb :
  mb ⋅ Some (Excl Tls1) ≡ Some (Excl Tls2) → Tls1 = Tls2.
Proof.
  destruct mb. by intros ?%callStateR_exclusive_Some.
  rewrite left_id. intros Eq%Some_equiv_inj. by simplify_eq.
Qed.

(** tmap properties *)
Lemma tmap_insert_op_uniq_r (pm1 pm2: tmapUR) t h0 kh
  (VALID: ✓ (pm1 ⋅ pm2)) :
  pm2 !! t = Some (to_tgkR tkUnique, h0) →
  pm1 ⋅ <[t:=kh]> pm2 = <[t:=kh]> (pm1 ⋅ pm2).
Proof.
  intros HL. apply (map_eq (pm1 ⋅ <[t:=kh]> pm2)). intros t'.
  move : (VALID t). rewrite 2!lookup_op HL.
  destruct (pm1 !! t) as [[k1 h1]|] eqn:Eqt; rewrite Eqt.
  - rewrite -Some_op pair_op. intros [?%exclusive_r]; [done|apply _].
  - intros VL.
    case (decide (t' = t)) => [->|?].
    + by rewrite 2!lookup_insert Eqt.
    + do 2 (rewrite lookup_insert_ne //). by rewrite lookup_op.
Qed.

Lemma tmap_lookup_op_uniq_r (pm1 pm2: tmapUR) t h0
  (VALID: ✓ (pm1 ⋅ pm2)) :
  pm2 !! t = Some (to_tgkR tkUnique, h0) →
  (pm1 ⋅ pm2) !! t = Some (to_tgkR tkUnique, h0).
Proof.
  intros HL. move : (VALID t). rewrite lookup_op HL.
  destruct (pm1 !! t) as [[k1 h1]|] eqn:Eqt; rewrite Eqt; [|done].
  rewrite -Some_op pair_op. intros [?%exclusive_r]; [done|apply _].
Qed.

Lemma tmap_lookup_op_l_uniq_equiv (pm1 pm2: tmapUR) t h0
  (VALID: ✓ (pm1 ⋅ pm2)):
  pm1 !! t ≡ Some (to_tgkR tkUnique, h0) →
  (pm1 ⋅ pm2) !! t ≡ Some (to_tgkR tkUnique, h0).
Proof.
  intros HL. move : (VALID t). rewrite lookup_op HL.
  destruct (pm2 !! t) as [[k2 h2]|] eqn:Eqt; rewrite Eqt; [|done].
  rewrite -Some_op pair_op. intros [?%exclusive_l]; [done|apply _].
Qed.

Lemma tmap_lookup_op_uniq_included (pm1 pm2: tmapUR) t h0
  (VALID: ✓ pm2) (INCL: pm1 ≼ pm2):
  pm1 !! t ≡ Some (to_tgkR tkUnique, h0) →
  pm2 !! t ≡ Some (to_tgkR tkUnique, h0).
Proof.
  destruct INCL as [cm' Eq]. rewrite Eq. apply tmap_lookup_op_l_uniq_equiv.
  by rewrite -Eq.
Qed.

Lemma tmap_lookup_op_r_uniq_equiv (pm1 pm2: tmapUR) t h0
  (VALID: ✓ (pm1 ⋅ pm2)) :
  pm2 !! t ≡ Some (to_tgkR tkUnique, h0) →
  (pm1 ⋅ pm2) !! t ≡ Some (to_tgkR tkUnique, h0).
Proof.
  intros HL. eapply tmap_lookup_op_uniq_included; [done|..|exact HL].
  by apply cmra_included_r.
Qed.


Lemma tmap_lookup_op_l_local_equiv (pm1 pm2: tmapUR) t h0
  (VALID: ✓ (pm1 ⋅ pm2)):
  pm1 !! t ≡ Some (to_tgkR tkLocal, h0) →
  (pm1 ⋅ pm2) !! t ≡ Some (to_tgkR tkLocal, h0).
Proof.
  intros HL. move : (VALID t). rewrite lookup_op HL.
  destruct (pm2 !! t) as [[k2 h2]|] eqn:Eqt; rewrite Eqt; [|done].
  rewrite -Some_op pair_op. intros [?%exclusive_l]; [done|apply _].
Qed.

Lemma tmap_lookup_op_local_included (pm1 pm2: tmapUR) t h0
  (VALID: ✓ pm2) (INCL: pm1 ≼ pm2):
  pm1 !! t ≡ Some (to_tgkR tkLocal, h0) →
  pm2 !! t ≡ Some (to_tgkR tkLocal, h0).
Proof.
  destruct INCL as [cm' Eq]. rewrite Eq. apply tmap_lookup_op_l_local_equiv.
  by rewrite -Eq.
Qed.

Lemma tmap_lookup_op_r_local_equiv (pm1 pm2: tmapUR) t h0
  (VALID: ✓ (pm1 ⋅ pm2)) :
  pm2 !! t ≡ Some (to_tgkR tkLocal, h0) →
  (pm1 ⋅ pm2) !! t ≡ Some (to_tgkR tkLocal, h0).
Proof.
  intros HL. eapply tmap_lookup_op_local_included; [done|..|exact HL].
  by apply cmra_included_r.
Qed.

Lemma tmap_lookup_op_l_equiv_pub (pm1 pm2: tmapUR) t h1
  (VALID: ✓ (pm1 ⋅ pm2)):
  pm1 !! t ≡ Some (to_tgkR tkPub, h1) →
  ∃ h2, (pm1 ⋅ pm2) !! t ≡ Some (to_tgkR tkPub, h1 ⋅ h2).
Proof.
  intros HL. move : (VALID t). rewrite lookup_op.
  destruct (pm2 !! t) as [[k2 h2]|] eqn:Eqt; rewrite Eqt; rewrite -> HL.
  - rewrite -Some_op pair_op. move => [ VL1 ?]. exists h2. simpl in VL1.
    rewrite HL -Some_op pair_op.
    by rewrite -(tagKindR_incl_eq (to_tgkR tkPub) _ VL1 (cmra_included_r _ _)).
  - intros _. exists (∅: gmap loc _). by rewrite 2!right_id HL.
Qed.

Lemma tmap_lookup_op_r_equiv_pub (pm1 pm2: tmapUR) t h2
  (VALID: ✓ (pm1 ⋅ pm2)):
  pm2 !! t ≡ Some (to_tgkR tkPub, h2) →
  ∃ h1, (pm1 ⋅ pm2) !! t ≡ Some (to_tgkR tkPub, h1 ⋅ h2).
Proof.
  intros HL. move : (VALID t). rewrite lookup_op.
  destruct (pm1 !! t) as [[k1 h1]|] eqn:Eqt; rewrite Eqt; rewrite -> HL.
  - rewrite -Some_op pair_op. move => [ VL1 ?]. exists h1. simpl in VL1.
    rewrite HL -Some_op pair_op.
    by rewrite -(tagKindR_incl_eq (to_tgkR tkPub) _ VL1 (cmra_included_r _ _)).
  - intros _. exists (∅: gmap loc _). by rewrite 2!left_id HL.
Qed.

Lemma tmap_lookup_op_None_inv (pm1 pm2: tmapUR) t :
  (pm1 ⋅ pm2) !! t = None →
  pm1 !! t = None ∧ pm2 !! t = None.
Proof.
  rewrite lookup_op.
  destruct (pm1 !! t) eqn:Eq1, (pm2 !! t) eqn:Eq2;
    rewrite Eq1 Eq2; [inversion 1..|done].
Qed.

Lemma tmap_valid (r_f r: tmapUR) t h0 kh
  (Eqtg: r !! t = Some (to_tgkR tkUnique, h0)) (VN: ✓ kh) :
  ✓ (r_f ⋅ r) → ✓ (r_f ⋅ (<[t:= kh]> r)).
Proof.
  intros VALID.
  apply (local_update_discrete_valid_frame _ _ _ VALID).
  have EQ := (tmap_insert_op_uniq_r _ _ _ _ kh VALID Eqtg). rewrite EQ.
  eapply (insert_local_update _ _ _
          (to_tgkR tkUnique, h0) (to_tgkR tkUnique, h0));
          [|exact Eqtg|by apply exclusive_local_update].
  by rewrite (tmap_lookup_op_uniq_r _ _ _ _ VALID Eqtg).
Qed.

(** heaplet *)
Lemma to_hplR_valid h : ✓ (to_hplR h).
Proof.
  intros l. rewrite /to_hplR lookup_fmap.
  destruct (h !! l) eqn:Eq; rewrite Eq //.
Qed.

Lemma to_hplR_lookup h l s :
  to_hplR h !! l ≡ Some (to_agree s) → h !! l = Some s.
Proof.
  rewrite /to_hplR lookup_fmap.
  destruct (h !! l) as [s'|] eqn:Eqs; rewrite Eqs /=; [|by inversion 1].
  intros Eq%Some_equiv_inj%to_agree_inj%leibniz_equiv_iff. by subst s'.
Qed.

Lemma heapletR_elem_of_dom (h: heapletR) l (VALID: valid h) :
  l ∈ dom (gset loc) h → ∃ s, h !! l ≡ Some (to_agree s).
Proof.
  rewrite elem_of_dom. intros [sa Eqs]. move : (VALID l). rewrite Eqs.
  intros [s Eq]%to_agree_uninj. exists s. by rewrite Eq.
Qed.

(** The Core *)

Lemma heaplet_core (h: heapletR) : core h = h.
Proof.
  apply (map_eq (M:=gmap loc)).
  intros l. rewrite lookup_core.
  by destruct (h !! l) as [s|] eqn:Eql; rewrite Eql.
Qed.

Lemma tmap_lookup_core_pub (pm: tmapUR) t h:
  pm !! t ≡ Some (to_tgkR tkPub, h) →
  core pm !! t ≡ Some (to_tgkR tkPub, h).
Proof. intros Eq. rewrite lookup_core Eq /core /= core_id //. Qed.

(** Resources that we own. *)

Definition res_tag tg tk (h: heaplet) : resUR :=
  ({[tg := (to_tgkR tk, to_agree <$> h)]}, ε).

Definition res_cs (c: call_id) (cs: tag_locs) : resUR :=
  (ε, to_cmUR {[c := cs]}).

Fixpoint locs_seq (l:loc) (n:nat) : gset loc :=
  match n with
  | O => ∅
  | S n => {[l]} ∪ locs_seq (l +ₗ 1) n
  end.

Fixpoint write_hpl l (v: list (scalar * scalar)) (h: heaplet) : heaplet :=
  match v with
  | [] => h
  | sst :: v' => write_hpl (l +ₗ 1) v' (<[l:=sst]> h)
  end.

Definition res_loc l (v: list (scalar * scalar)) (t: ptr_id) : resUR :=
  res_tag t tkLocal (write_hpl l v ∅).

(* Definition res_mapsto (l:loc) (v: list (scalar * scalar)) (t: ptr_id) : resUR :=
  res_loc l (length v) t ⋅ res_tag t tkUnique (write_hpl l v ∅). *)

(** res_tag *)
Lemma locs_seq_elem_of_equiv l n i :
  (i < n)%nat ↔ l +ₗ i ∈ locs_seq l n.
Proof.
  revert l i. induction n as [|n IH]; intros l i.
  { simpl. split; intros. lia. exfalso. by eapply not_elem_of_empty. }
  rewrite /= elem_of_union elem_of_singleton.
  destruct i as [|i]; simpl.
  - rewrite shift_loc_0_nat. split; intros; [by left|lia].
  - rewrite (_: l +ₗ S i = (l +ₗ 1) +ₗ i).
    + rewrite -IH. split; intros CASE; [right; by lia|].
      destruct CASE as [CASE|?]; [|lia]. exfalso.
      move : CASE. rewrite shift_loc_assoc -{2}(shift_loc_0 l).
      intros ?%shift_loc_inj. lia.
    + rewrite shift_loc_assoc. f_equal. lia.
Qed.

Lemma locs_seq_elem_of l n i :
  (i < n)%nat → l +ₗ i ∈ locs_seq l n.
Proof. by intros; apply locs_seq_elem_of_equiv. Qed.

Lemma locs_seq_elem_of_2 l n l' :
  l' ∈ locs_seq l n → ∃ i : nat, l' = l +ₗ i ∧ (i < n)%nat.
Proof.
  revert l. induction n as [|n IH]; simpl; intros l.
  { by intros ?%not_elem_of_empty. }
  rewrite elem_of_union elem_of_singleton.
  intros [?|[i [Eqi Lt]]%IH].
  - subst l'. exists O. rewrite shift_loc_0_nat. split; [done|lia].
  - exists (S i). split; [|lia].
    rewrite (_: l +ₗ S i = l +ₗ 1 +ₗ i) //.
    rewrite shift_loc_assoc. f_equal. lia.
Qed.

Lemma write_hpl_lookup l vl h :
  (∀ (i: nat), (i < length vl)%nat → write_hpl l vl h !! (l +ₗ i) = vl !! i) ∧
  (∀ (l': loc), (∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i) →
    write_hpl l vl h !! l' = h !! l').
Proof.
  revert l h. induction vl as [|v vl IH]; move => l h; simpl;
    [split; [intros ?; by lia|done]|].
  destruct (IH (l +ₗ 1) (<[l:=v]> h)) as [IH1 IH2]. split.
  - intros i Lt. destruct i as [|i].
    + rewrite shift_loc_0_nat /=. rewrite IH2; [by rewrite lookup_insert|].
      move => ? _.
      rewrite shift_loc_assoc -{1}(shift_loc_0 l) => /shift_loc_inj ?. by lia.
    + rewrite /= -IH1; [|lia].  by rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
  - intros l' Lt. rewrite IH2.
    + rewrite lookup_insert_ne; [done|].
      move => ?. subst l'. apply (Lt O); [lia|by rewrite shift_loc_0_nat].
    + move => i Lti. rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
      apply Lt. by lia.
Qed.

Lemma write_hpl_lookup_case l vl h l' :
  (∃ (i: nat), (i < length vl)%nat ∧ l' = l +ₗ i ∧ write_hpl l vl h !! (l +ₗ i) = vl !! i)
  ∨ ((∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i) ∧ write_hpl l vl h !! l' = h !! l').
Proof.
  destruct (write_hpl_lookup l vl h) as [EQ1 EQ2].
  case (decide (l'.1 = l.1)) => [Eql|NEql];
    [case (decide (l.2 ≤ l'.2 < l.2 + length vl)) => [[Le Lt]|NIN]|].
  - have Eql2: l' = l +ₗ Z.of_nat (Z.to_nat (l'.2 - l.2)). {
      destruct l, l'. move : Eql Le => /= -> ?.
      rewrite /shift_loc /= Z2Nat.id; [|lia]. f_equal. lia. }
    have Lt1: (Z.to_nat (l'.2 - l.2) < length vl)%nat
      by rewrite -(Nat2Z.id (length _)) -Z2Nat.inj_lt; lia.
    specialize (EQ1 _ Lt1).
    rewrite -Eql2 in EQ1. left.
    exists (Z.to_nat (l'.2 - l.2)). repeat split; [done..|by rewrite -Eql2].
  - right.
    have ?: (∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i).
    { intros i Lt Eq3. apply NIN. rewrite Eq3 /=. lia. }
    split; [done|]. by apply EQ2.
  - right.
    have ?: (∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i).
    { intros i Lt Eq3. apply NEql. by rewrite Eq3. }
    split; [done|]. by apply EQ2.
Qed.

Lemma write_hpl_elem_of_dom l vl h i :
  (i < length vl)%nat → l +ₗ i ∈ dom (gset loc) (write_hpl l vl h).
Proof.
  intros Lt. destruct (write_hpl_lookup l vl h) as [EQ _].
  specialize (EQ _ Lt). by rewrite elem_of_dom EQ lookup_lt_is_Some.
Qed.

Lemma write_hpl_is_Some l vl h i :
  (i < length vl)%nat → is_Some (write_hpl l vl h !! (l +ₗ i)).
Proof.
  intros Lt. destruct (write_hpl_lookup l vl h) as [EQ _].
  specialize (EQ _ Lt). by rewrite EQ lookup_lt_is_Some.
Qed.

Lemma res_tag_alloc_local_update lsf t k h
  (FRESH: lsf.(rtm) !! t = None) :
  (lsf, ε) ~l~> (lsf ⋅ res_tag t k h, res_tag t k h).
Proof.
  destruct lsf as [[tm cm] lm]. rewrite pair_op right_id.
  apply prod_local_update_1.
  rewrite cmra_comm -insert_singleton_op //.
  apply alloc_singleton_local_update; [done|].
  split. by destruct k. apply to_hplR_valid.
Qed.

Lemma res_tag_uniq_insert_local_update_inner
  (tm: tmapUR) t k1 k2 (h1 h2: heaplet)
  (UNIQ: k1 = tkLocal ∨ k1 = tkUnique) :
  tm !! t = None →
  (tm ⋅ {[t := (to_tgkR k1, to_hplR h1)]}, {[t := (to_tgkR k1, to_hplR h1)]}) ~l~>
  (tm ⋅ {[t := (to_tgkR k2, to_hplR h2)]}, {[t := (to_tgkR k2, to_hplR h2)]}).
Proof.
  intros.
  do 2 rewrite (cmra_comm tm) -insert_singleton_op //.
  rewrite -(insert_insert tm t (_, to_agree <$> h2)
                               (to_tgkR k1, to_agree <$> h1)).
  eapply (singleton_local_update (<[t := _]> tm : tmapUR)).
  - by rewrite lookup_insert.
  - have ?: Exclusive (to_tgkR k1, to_hplR h1).
    { destruct UNIQ; subst k1; apply _. }
    apply exclusive_local_update.
    split; [apply to_tgkR_valid|apply to_hplR_valid].
Qed.

Lemma res_tag_uniq_local_update (r: resUR) t k h k' h'
  (UNIQ: k = tkLocal ∨ k = tkUnique)
  (NONE: r.(rtm) !! t = None) :
  (r ⋅ res_tag t k h, res_tag t k h) ~l~> (r ⋅ res_tag t k' h', res_tag t k' h').
Proof.
  destruct r as [tm cm].
  apply prod_local_update_1. rewrite /=.
  by apply res_tag_uniq_insert_local_update_inner.
Qed.

Lemma res_tag_1_insert_local_update (r: resUR) (l: loc) k s1 s2 (t: ptr_id)
  (UNIQ: k = tkLocal ∨ k = tkUnique)
  (NONE: r.(rtm) !! t = None) :
  (r ⋅ res_tag t k {[l := s1]}, res_tag t k {[l := s1]}) ~l~>
  (r ⋅ res_tag t k {[l := s2]}, res_tag t k {[l := s2]}).
Proof. by apply res_tag_uniq_local_update. Qed.

Lemma res_tag_lookup (k: tag_kind) (h: heaplet) (t: ptr_id) :
  (res_tag t k h).(rtm) !! t ≡ Some (to_tgkR k, to_agree <$> h).
Proof. by rewrite lookup_insert. Qed.

Lemma res_tag_lookup_ne (k: tag_kind) (h: heaplet) (t t': ptr_id) (NEQ: t' ≠ t) :
  (res_tag t k h).(rtm) !! t' ≡ None.
Proof. by rewrite lookup_insert_ne. Qed.


Lemma res_tag_uniq_dealloc_local_update_inner
  (tm: tmapUR) t k h
  (UNIQ: k = tkLocal ∨ k = tkUnique) :
  tm !! t = None →
  (tm ⋅ {[t := (to_tgkR k, h)]}, {[t := (to_tgkR k, h)]}) ~l~>
  (tm, ε).
Proof.
  intros.
  rewrite (cmra_comm tm) -insert_singleton_op //.
  rewrite -{2}(delete_insert tm t (to_tgkR k, h)) //.
  eapply (delete_singleton_local_update (<[t := _]> tm : tmapUR)).
  destruct UNIQ; subst k; apply _.
Qed.

Lemma res_tag_uniq_dealloc_local_update (r: resUR) t k h
  (UNIQ: k = tkLocal ∨ k = tkUnique)
  (NONE: r.(rtm) !! t = None) :
  (r ⋅ res_tag t k h, res_tag t k h) ~l~> (r, ε : resUR).
Proof.
  destruct r as [tm cm]. rewrite pair_op right_id.
  apply prod_local_update_1.
  by apply res_tag_uniq_dealloc_local_update_inner.
Qed.

Lemma res_tag_uniq_dealloc_local_update_r (r: resUR) r' t k h
  (UNIQ: k = tkLocal ∨ k = tkUnique)
  (NONE: (r ⋅ r').(rtm) !! t = None) :
  (r ⋅ r' ⋅ res_tag t k h, r' ⋅ res_tag t k h) ~l~>
  (r ⋅ r', r').
Proof.
  rewrite (cmra_comm r' (res_tag t k h)).
  rewrite -{4}(left_id ε _ r').
  by apply op_local_update_frame, res_tag_uniq_dealloc_local_update.
Qed.

