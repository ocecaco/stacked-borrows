From stbor.sim Require Import left_step right_step.

Lemma sim_body_copy_local fs ft r r' n l t ty ss st σs σt Φ :
  tsize ty = 1%nat →
  r ≡ r' ⋅ res_loc l [(ss, st)] t →
  (r ⊨{n,fs,ft} (#[ss], σs) ≥ (#[st], σt) : Φ) →
  r ⊨{S n,fs,ft}
    (Copy (Place l (Tagged t) ty), σs) ≥ (Copy (Place l (Tagged t) ty), σt)
  : Φ.
Proof.
  intros ?? Hcont.
  eapply sim_body_copy_local_l; [done..|].
  eapply sim_body_copy_local_r; done.
Qed.
