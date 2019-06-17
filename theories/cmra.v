From iris.algebra Require Export cmra gmap gset csum agree excl.

From stbor Require Export lang.

Inductive tag_kind := tkUnique | tkPub.
(* Ex() + Ag() *)
Definition tagKindR := csumR (exclR unitC) (agreeR unitC).
Definition to_tagKindR (tk: tag_kind) : tagKindR :=
  match tk with tkUnique => Cinl (Excl ()) | tkPub => Cinr (to_agree ()) end.

Inductive call_state := csOwned (T: gset ptr_id) | csPub.
(* Ex(ptr_id) + Ag() *)
Definition callStateR := csumR (exclR (gsetC ptr_id)) (agreeR unitC).
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
