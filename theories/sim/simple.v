(** A simpler simulation relation that hides the physical state.
Useful whenever the resources we own are strong enough to carry us from step to step.

When your goal is simple, to make it stateful just do [intros σs σt].
To go the other direction, [apply sim_simplify]. Then you will likely
want to clean some stuff from your context.
*)

From stbor.sim Require Export instance.

Definition sim_simple fs ft r n es et Φ : Prop :=
  ∀ σs σt, r ⊨{ n , fs , ft } ( es , σs ) ≥ ( et , σt ) : Φ.

Notation "r ⊨ˢ{ n , fs , ft } es '≥' et : Φ" :=
  (sim_simple fs ft r n%nat es%E et%E Φ)
  (at level 70, es, et at next level,
   format "'[hv' r  '/' ⊨ˢ{ n , fs , ft }  '/  ' '[ ' es ']'  '/' ≥  '/  ' '[ ' et ']'  '/' :  Φ ']'").

Lemma sim_fun_simple1 n fs ft (esf etf: function) Φ :
  length (esf.(fun_b)) = 1%nat →
  length (etf.(fun_b)) = 1%nat →
  (∀ es et vs vt r, vrel r vs vt →
   subst_l (esf.(fun_b)) [Val vs] (esf.(fun_e)) = Some es →
   subst_l (etf.(fun_b)) [Val vt] (etf.(fun_e)) = Some et →
   r ⊨ˢ{n,fs,ft} es ≥ et : Φ) →
  ⊨ᶠ{fs,ft} esf ≥ etf.
Abort.
