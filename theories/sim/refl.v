From stbor.lang Require Import lang.
From stbor.sim Require Import refl_step.

Set Default Proof Using "Type".

Theorem sim_mod_fun_refl f :
  ⊨ᶠ f ≥ f.
Proof.
Admitted.

Lemma sim_mod_funs_refl prog :
  sim_mod_funs prog prog.
Proof.
  induction prog using map_ind.
  { intros ??. rewrite lookup_empty. done. }
  apply sim_mod_funs_insert; try done.
  apply sim_mod_fun_refl.
Qed.
