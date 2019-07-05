From iris.algebra Require Import local_updates.

From stbor.lang Require Import steps_progress steps_inversion steps_retag.
From stbor.sim Require Export instance.

Set Default Proof Using "Type".

Lemma sim_body_copy_right_1
  fs ft (r: resUR) k (h: heapletR) n l t s es σs σt Φ
  (* we know we're going to read s *)
  (UNIQUE: r.1 !! t ≡ Some (k, h))
  (InD: h !! l ≡ Some (to_agree s))
  (IN: tag_in_stack σt l t) :
  (σt.(shp) !! l = Some s → r ⊨{n,fs,ft} (es, σs) ≥ (#[s%S], σt) : Φ : Prop) →
  r ⊨{n,fs,ft} (es, σs) ≥ (Copy (Place l (Tagged t) int), σt) : Φ.
Proof.
Abort.
