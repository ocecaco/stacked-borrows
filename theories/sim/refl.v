From stbor.lang Require Import lang.
From stbor.sim Require Import refl_step.

Set Default Proof Using "Type".

Lemma sim_mod_funs_refl prog :
  sim_mod_funs prog prog.
Proof.
Admitted.
