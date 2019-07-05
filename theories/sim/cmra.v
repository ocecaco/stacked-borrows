From iris.algebra Require Export local_updates.
From iris.algebra Require Export cmra gmap gset csum agree excl.

From stbor.lang Require Export lang.

Set Default Proof Using "Type".

Inductive tag_kind := tkUnique | tkPub.
(* Ex() + Ag() *)
Definition tagKindR := csumR (exclR unitO) (agreeR unitO).

Definition to_tagKindR (tk: tag_kind) : tagKindR :=
  match tk with tkUnique => Cinl (Excl ()) | tkPub => Cinr (to_agree ()) end.

Inductive call_state := csOwned (T: gset ptr_id) | csPub.
(* Ex(ptr_id) + Ag() *)
Definition callStateR := csumR (exclR (gsetO ptr_id)) (agreeR unitO).

Definition to_callStateR (cs: call_state) : callStateR :=
  match cs with csOwned T => Cinl (Excl T) | csPub => Cinr (to_agree ()) end.

Definition cmap := gmap call_id call_state.
(* call_id ⇀ CallState *)
Definition cmapUR := gmapUR call_id callStateR.

Definition to_cmapUR (cm: cmap) : cmapUR := fmap to_callStateR cm.

Definition ptrmap := gmap ptr_id (tag_kind * mem).
Definition heapletR := gmapR loc (agreeR scalarC).
(* ptr_id ⇀ TagKid x (loc ⇀ Ag(Scalar)) *)
Definition ptrmapUR := gmapUR ptr_id (prodR tagKindR heapletR).

Definition to_heapletR (h: mem) : heapletR := fmap to_agree h.
Definition to_ptrmapUR (pm: ptrmap) : ptrmapUR :=
  fmap (λ tm, (to_tagKindR tm.1, to_heapletR tm.2)) pm.

Definition res := (ptrmap * cmap)%type.
Definition resUR := prodUR ptrmapUR cmapUR.
Definition to_resUR (r: res) : resUR := (to_ptrmapUR r.1, to_cmapUR r.2).


Lemma local_update_discrete_valid_frame `{CmraDiscrete A} (r_f r r' : A) :
  ✓ (r_f ⋅ r) → (r_f ⋅ r, r) ~l~> (r_f ⋅ r', r') → ✓ (r_f ⋅ r').
Proof.
  intros VALID UPD. apply cmra_discrete_valid.
  apply (UPD O (Some r_f)); [by apply cmra_discrete_valid_iff|by rewrite /= comm].
Qed.

(** tag_kind properties *)
Lemma tag_kind_incl_eq (k1 k2: tagKindR):
  ✓ k2 → k1 ≼ k2 → k1 ≡ k2.
Proof.
  move => VAL /csum_included [? |[[? [? [? [? Eq]]]]|[? [? [? [? LE]]]]]];
    subst; [done|..].
  - exfalso. eapply exclusive_included; [..|apply Eq|apply VAL]. apply _.
  - apply Cinr_equiv, agree_op_inv. apply agree_included in LE.
    rewrite -LE. apply VAL.
Qed.

Lemma tagKindR_exclusive (h0 h: heapletR) mb :
  mb ⋅ Some (to_tagKindR tkUnique, h0) ≡ Some (to_tagKindR tkPub, h) → False.
Proof.
  destruct mb as [[k ?]|]; [rewrite -Some_op pair_op|rewrite left_id];
    intros [Eq _]%Some_equiv_inj.
  - destruct k as [[]| |]; inversion Eq.
  - inversion Eq.
Qed.

Lemma tagKindR_exclusive_2 (h0 h: heapletR) mb :
  mb ⋅ Some (to_tagKindR tkPub, h0) ≡ Some (to_tagKindR tkUnique, h) → False.
Proof.
  destruct mb as [[k ?]|]; [rewrite -Some_op pair_op|rewrite left_id];
    intros [Eq _]%Some_equiv_inj.
  - destruct k as [[]| |]; inversion Eq.
  - inversion Eq.
Qed.

Lemma tagKindR_exclusive_heaplet (h0 h: heapletR) mb :
  mb ⋅ Some (to_tagKindR tkUnique, h0) ≡ Some (to_tagKindR tkUnique, h) → h0 ≡ h.
Proof.
  destruct mb as [[k ?]|]; [rewrite -Some_op pair_op|rewrite left_id];
    intros [Eq1 Eq2]%Some_equiv_inj; [|done].
  destruct k as [[[]|]| |]; inversion Eq1; simplify_eq.
Qed.

Lemma tagKindR_valid (k: tagKindR) :
  valid k → ∃ k', k ≡ to_tagKindR k'.
Proof.
  destruct k as [[[]|]|a |]; [|done|..|done]; intros VAL.
  - by exists tkUnique.
  - exists tkPub. by apply to_agree_uninj in VAL as [[] <-].
Qed.

(** cmap properties *)
Lemma cmap_lookup_op_r (cm1 cm2: cmapUR) c T (VALID: ✓ (cm1 ⋅ cm2)):
  cm2 !! c = Some (to_callStateR (csOwned T)) →
  (cm1 ⋅ cm2) !! c = Some (to_callStateR (csOwned T)).
Proof.
  intros HL. move : (VALID c). rewrite lookup_op HL.
  destruct (cm1 !! c) as [cs'|] eqn:Eqc; rewrite Eqc; [|done].
  rewrite -Some_op Some_valid.
  destruct cs' as [[]|c2|]; auto; try inversion 1.
Qed.

Lemma cmap_lookup_op_l (cm1 cm2: cmapUR) c T (VALID: ✓ (cm1 ⋅ cm2)):
  cm1 !! c = Some (to_callStateR (csOwned T)) →
  (cm1 ⋅ cm2) !! c = Some (to_callStateR (csOwned T)).
Proof.
  intros HL. move : (VALID c). rewrite lookup_op HL.
  destruct (cm2 !! c) as [cs'|] eqn:Eqc; rewrite Eqc; [|done].
  rewrite -Some_op Some_valid.
  destruct cs' as [[]|c2|]; auto; try inversion 1.
Qed.

Lemma cmap_lookup_op_l_equiv (cm1 cm2: cmapUR) c T (VALID: ✓ (cm1 ⋅ cm2)):
  cm1 !! c ≡ Some (to_callStateR (csOwned T)) →
  (cm1 ⋅ cm2) !! c ≡ Some (to_callStateR (csOwned T)).
Proof.
  intros HL. move : (VALID c). rewrite lookup_op HL.
  destruct (cm2 !! c) as [cs'|] eqn:Eqc; rewrite Eqc; [|done].
  rewrite -Some_op Some_valid.
  destruct cs' as [[]|c2|]; auto; try inversion 1.
Qed.

Lemma cmap_lookup_op_unique_included (cm1 cm2: cmapUR)
  c T (VALID: ✓ cm2) (INCL: cm1 ≼ cm2):
  cm1 !! c ≡ Some (to_callStateR (csOwned T)) →
  cm2 !! c ≡ Some (to_callStateR (csOwned T)).
Proof.
  destruct INCL as [cm' Eq]. rewrite Eq. apply cmap_lookup_op_l_equiv.
  by rewrite -Eq.
Qed.

Lemma cmap_lookup_op_l_equiv_pub (cm1 cm2: cmapUR) c (VALID: ✓ (cm1 ⋅ cm2)):
  cm1 !! c ≡ Some (to_callStateR csPub) →
  (cm1 ⋅ cm2) !! c ≡ Some (to_callStateR csPub).
Proof.
  intros HL. move : (VALID c). rewrite lookup_op HL.
  destruct (cm2 !! c) as [cs'|] eqn:Eqc; rewrite Eqc; [|done].
  rewrite -Some_op Some_valid.
  destruct cs' as [[]|c2|]; auto; try inversion 1.
  rewrite /= Cinr_op. intros Eq2%agree_op_inv. by rewrite -Eq2 agree_idemp.
Qed.

Lemma cmap_insert_op_r (cm1 cm2: cmapUR) c T cs (VALID: ✓ (cm1 ⋅ cm2)):
  cm2 !! c = Some (to_callStateR (csOwned T)) →
  cm1 ⋅ <[c:=cs]> cm2 = <[c:=cs]> (cm1 ⋅ cm2).
Proof.
  intros HL. apply (map_eq (cm1 ⋅ <[c:=cs]> cm2)). intros c'.
  move : (VALID c). rewrite 2!lookup_op HL.
  destruct (cm1 !! c) as [[| |]|] eqn:Eqc; rewrite Eqc; [inversion 1..|].
  intros VL.
  case (decide (c' = c)) => [->|?].
  - by rewrite 2!lookup_insert Eqc.
  - do 2 (rewrite lookup_insert_ne //). by rewrite lookup_op.
Qed.

Lemma callStateR_exclusive_2 T mb :
  mb ⋅ Some (to_callStateR csPub) ≡ Some (to_callStateR (csOwned T)) → False.
Proof.
  destruct mb as [cs|]; [rewrite -Some_op|rewrite left_id];
    intros Eq%Some_equiv_inj.
  - destruct cs; inversion Eq.
  - inversion Eq.
Qed.

(** ptrmap properties *)
Lemma ptrmap_insert_op_r (pm1 pm2: ptrmapUR) t h0 kh (VALID: ✓ (pm1 ⋅ pm2)):
  pm2 !! t = Some (to_tagKindR tkUnique, h0) →
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

Lemma ptrmap_lookup_op_r (pm1 pm2: ptrmapUR) t h0 (VALID: ✓ (pm1 ⋅ pm2)):
  pm2 !! t = Some (to_tagKindR tkUnique, h0) →
  (pm1 ⋅ pm2) !! t = Some (to_tagKindR tkUnique, h0).
Proof.
  intros HL. move : (VALID t). rewrite lookup_op HL.
  destruct (pm1 !! t) as [[k1 h1]|] eqn:Eqt; rewrite Eqt; [|done].
  rewrite -Some_op pair_op. intros [?%exclusive_r]; [done|apply _].
Qed.

Lemma ptrmap_lookup_op_l_unique_equiv (pm1 pm2: ptrmapUR) t h0
  (VALID: ✓ (pm1 ⋅ pm2)):
  pm1 !! t ≡ Some (to_tagKindR tkUnique, h0) →
  (pm1 ⋅ pm2) !! t ≡ Some (to_tagKindR tkUnique, h0).
Proof.
  intros HL. move : (VALID t). rewrite lookup_op HL.
  destruct (pm2 !! t) as [[k2 h2]|] eqn:Eqt; rewrite Eqt; [|done].
  rewrite -Some_op pair_op. intros [?%exclusive_l]; [done|apply _].
Qed.

Lemma ptrmap_lookup_op_unique_included (pm1 pm2: ptrmapUR) t h0
  (VALID: ✓ pm2) (INCL: pm1 ≼ pm2):
  pm1 !! t ≡ Some (to_tagKindR tkUnique, h0) →
  pm2 !! t ≡ Some (to_tagKindR tkUnique, h0).
Proof.
  destruct INCL as [cm' Eq]. rewrite Eq. apply ptrmap_lookup_op_l_unique_equiv.
  by rewrite -Eq.
Qed.

Lemma ptrmap_lookup_op_r_equiv_pub (pm1 pm2: ptrmapUR) t h2 (VALID: ✓ (pm1 ⋅ pm2)):
  pm2 !! t ≡ Some (to_tagKindR tkPub, h2) →
  ∃ h1, (pm1 ⋅ pm2) !! t ≡ Some (to_tagKindR tkPub, h1 ⋅ h2).
Proof.
  intros HL. move : (VALID t). rewrite lookup_op.
  destruct (pm1 !! t) as [[k1 h1]|] eqn:Eqt; rewrite Eqt; rewrite -> HL.
  - rewrite -Some_op pair_op. move => [ VL1 ?]. exists h1. simpl in VL1.
    rewrite HL -Some_op pair_op.
    by rewrite -(tag_kind_incl_eq (to_tagKindR tkPub) _ VL1 (cmra_included_r _ _)).
  - intros _. exists (∅: gmap loc _). by rewrite 2!left_id HL.
Qed.

Lemma ptrmap_valid (r_f r: ptrmapUR) t h0 kh
  (Eqtg: r !! t = Some (to_tagKindR tkUnique, h0)) (VN: ✓ kh) :
  ✓ (r_f ⋅ r) → ✓ (r_f ⋅ (<[t:= kh]> r)).
Proof.
  intros VALID.
  apply (local_update_discrete_valid_frame _ _ _ VALID).
  have EQ := (ptrmap_insert_op_r _ _ _ _ kh VALID Eqtg). rewrite EQ.
  eapply (insert_local_update _ _ _
          (to_tagKindR tkUnique, h0) (to_tagKindR tkUnique, h0));
          [|exact Eqtg|by apply exclusive_local_update].
  by rewrite (ptrmap_lookup_op_r _ _ _ _ VALID Eqtg).
Qed.

Lemma to_heapletR_valid h : ✓ (to_heapletR h).
Proof.
  intros l. rewrite /to_heapletR lookup_fmap.
  destruct (h !! l) eqn:Eq; rewrite Eq //.
Qed.

Lemma to_heapletR_lookup h l s :
  to_heapletR h !! l ≡ Some (to_agree s) → h !! l = Some s.
Proof.
  rewrite /to_heapletR lookup_fmap.
  destruct (h !! l) as [s'|] eqn:Eqs; rewrite Eqs /=; [|by inversion 1].
  intros Eq%Some_equiv_inj%to_agree_inj. by inversion Eq.
Qed.

(** The Core *)

Lemma heaplet_core (h: heapletR) : core h = h.
Proof.
  apply (map_eq (M:=gmap loc)).
  intros l. rewrite lookup_core.
  by destruct (h !! l) as [s|] eqn:Eql; rewrite Eql.
Qed.

Lemma ptrmap_lookup_core_pub (pm: ptrmapUR) t h:
  pm !! t ≡ Some (to_tagKindR tkPub, h) →
  core pm !! t ≡ Some (to_tagKindR tkPub, h).
Proof. intros Eq. rewrite lookup_core Eq /core /= core_id //. Qed.
