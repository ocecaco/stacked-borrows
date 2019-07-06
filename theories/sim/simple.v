(** A simpler simulation relation that hides most of the physical state,
except for the call ID stack.
Useful whenever the resources we own are strong enough to carry us from step to step.

When your goal is simple, to make it stateful just do [intros σs σt].
To go the other direction, [apply sim_simplify NEW_POST]. Then you will likely
want to clean some stuff from your context.
*)

From stbor.sim Require Export instance refl_step.

Section simple.
Implicit Types Φ: resUR → nat → result → call_id_stack → result → call_id_stack → Prop.

Definition fun_post_simple initial_call_id_stack (r: resUR) (n: nat) vs css vt cst :=
  (∃ c, cst = c::initial_call_id_stack) ∧
  end_call_sat r (mkState ∅ ∅ css 0 0) (mkState ∅ ∅ cst 0 0) ∧
  vrel_res r vs vt.

Definition sim_simple fs ft r n es css et cst
  (Φ : resUR → nat → result → call_id_stack → result → call_id_stack → Prop) : Prop :=
  ∀ σs σt, σs.(scs) = css → σt.(scs) = cst →
    r ⊨{ n , fs , ft } ( es , σs ) ≥ ( et , σt ) :
    (λ r n vs' σs' vt' σt', Φ r n vs' σs'.(scs) vt' σt'.(scs)).

Notation "r ⊨ˢ{ n , fs , ft } ( es , css ) '≥' ( et , cst ) : Φ" :=
  (sim_simple fs ft r n%nat es%E css et%E cst Φ)
  (at level 70, es, et at next level,
   format "'[hv' r  '/' ⊨ˢ{ n , fs , ft }  '/  ' '[ ' ( es ,  css ) ']'  '/' ≥  '/  ' '[ ' ( et ,  cst ) ']'  '/' :  Φ ']'").

(* FIXME: does this [apply]? *)
Lemma sim_simplify
  (Φnew: resUR → nat → result → call_id_stack → result → call_id_stack → Prop)
  (Φ: resUR → nat → result → state → result → state → Prop)
  r n fs ft es σs et σt :
  (∀ r n vs σs vt σt, Φnew r n vs σs.(scs) vt σt.(scs) → Φ r n vs σs vt σt) →
  r ⊨ˢ{ n , fs , ft } (es, σs.(scs)) ≥ (et, σt.(scs)) : Φnew →
  r ⊨{ n , fs , ft } (es, σs) ≥ (et, σt) : Φ.
Proof.
  intros HΦ HH. eapply sim_local_body_post_mono; last by apply HH.
  apply HΦ.
Qed.

(** Simple proof for a function taking one argument. *)
(* TODO: make the two call stacks the same. *)
Lemma sim_fun_simple1 n fs ft (esf etf: function) :
  length (esf.(fun_b)) = 1%nat →
  length (etf.(fun_b)) = 1%nat →
  (∀ rf es css et cst vs vt,
    vrel rf vs vt →
    subst_l (esf.(fun_b)) [Val vs] (esf.(fun_e)) = Some es →
    subst_l (etf.(fun_b)) [Val vt] (etf.(fun_e)) = Some et →
    rf ⊨ˢ{n,fs,ft} (InitCall es, css) ≥ (InitCall et, cst) : fun_post_simple cst) →
  ⊨ᶠ{fs,ft} esf ≥ etf.
Proof.
  intros Hls Hlt HH rf es et vls vlt σs σt FREL SUBSTs SUBSTt. exists n.
  move:(subst_l_is_Some_length _ _ _ _ SUBSTs) (subst_l_is_Some_length _ _ _ _ SUBSTt).
  rewrite Hls Hlt.
  destruct vls as [|vs []]; [done| |done].
  destruct vlt as [|vt []]; [done| |done].
  inversion FREL. intros _ _. simplify_eq.
  eapply sim_simplify; last by eapply HH.
  intros ?????? (Hhead & Hend & Hrel). split; first done.
  split; last done.
  (* Currently [end_call_sat] still looks at the state, but we should be able to fix that. *)
  admit.
Admitted.

Lemma sim_simple_init_call fs ft r n es css et cst Φ :
  (∀ c: call_id,
    let r' := res_callState c (csOwned ∅) in
    r ⋅ r' ⊨ˢ{n,fs,ft} (es, c::cst) ≥ (et, c::cst) : Φ) →
  r ⊨ˢ{n,fs,ft} (InitCall es, css) ≥ (InitCall et, cst) : Φ.
Proof.
  intros HH σs σt <-<-. apply sim_body_init_call=>/= ?.
  apply HH; done.
Qed.

Lemma sim_simple_alloc_local fs ft r n T css cst Φ :
  (∀ (l: loc) (t: tag),
    let r' := res_mapsto l ☠ (init_stack t) in
    Φ (r ⋅ r') n (PlaceR l t T) css (PlaceR l t T) cst) →
  r ⊨ˢ{n,fs,ft} (Alloc T, css) ≥ (Alloc T, cst) : Φ.
Proof.
  intros HH σs σt <-<-. apply sim_body_alloc_local=>/=. apply HH.
Qed.

End simple.
