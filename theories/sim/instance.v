From stbor.lang Require Import steps_inversion.
From stbor.sim Require Export local invariant.

Notation "r ⊨{ n , fs , ft } ( es , σs ) ≥ ( et , σt ) : Φ" :=
  (sim_local_body wsat vrel fs ft r n%nat es%E σs et%E σt Φ)
  (at level 70, format "'[hv' r  '/' ⊨{ n , fs , ft } '/  ' '[ ' ( es ,  '/' σs ) ']' '/' ≥  '/  ' '[ ' ( et ,  '/' σt ) ']'  '/' :  Φ ']'").

Notation "⊨{ fs , ft } f1 ≥ᶠ f2" :=
  (sim_local_fun wsat vrel fs ft end_call_sat f1 f2)
  (at level 70, format "⊨{ fs , ft }  f1  ≥ᶠ  f2").

Instance dom_proper `{Countable K} {A : cmraT} :
  Proper ((≡) ==> (≡)) (dom (M:=gmap K A) (gset K)).
Proof.
  intros m1 m2 Eq. apply elem_of_equiv. intros i.
  by rewrite !elem_of_dom Eq.
Qed.

Lemma sim_body_result fs ft r n es et σs σt Φ :
  (✓ r → Φ r n es σs et σt : Prop) →
  r ⊨{S n,fs,ft} (of_result es, σs) ≥ (of_result et, σt) : Φ.
Proof.
  intros POST. pfold.  split; last first.
  { constructor 1. intros vt' ? STEPT'. exfalso.
    apply result_tstep_stuck in STEPT'. by rewrite to_of_result in STEPT'. }
  { move => ? /= Eqvt'. symmetry in Eqvt'. simplify_eq.
    exists es, σs, r, n. split; last split.
    - right. split; [lia|]. eauto.
    - eauto.
    - rewrite to_of_result in Eqvt'. simplify_eq.
      apply POST. by destruct WSAT as (?&?&?%cmra_valid_op_r &?). }
  { left. rewrite to_of_result. by eexists. }
Qed.
