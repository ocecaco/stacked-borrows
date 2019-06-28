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
(* ptr_id ⇀ TagKid x (loc ⇀ Ag(Scalar)) *)
Definition ptrmapUR := gmapUR ptr_id (prodR tagKindR (gmapR loc (agreeR scalarC))).

Definition to_heapUR (h: mem) : gmapR loc (agreeR scalarC) := fmap to_agree h.
Definition to_ptrmapUR (pm: ptrmap) : ptrmapUR :=
  fmap (λ tm, (to_tagKindR tm.1, to_heapUR tm.2)) pm.

Definition res := (ptrmap * cmap)%type.
Definition resUR := prodUR ptrmapUR cmapUR.
Definition to_resUR (r: res) : resUR := (to_ptrmapUR r.1, to_cmapUR r.2).

Lemma tag_kind_incl_eq (k1 k2: tagKindR):
  ✓ k2 → k1 ≼ k2 → k1 ≡ k2.
Proof.
  move => VAL /csum_included [? |[[? [? [? [? Eq]]]]|[? [? [? [? LE]]]]]];
    subst; [done|..].
  - exfalso. eapply exclusive_included; [..|apply Eq|apply VAL]. apply _.
  - apply Cinr_equiv, agree_op_inv. apply agree_included in LE.
    rewrite -LE. apply VAL.
Qed.

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
