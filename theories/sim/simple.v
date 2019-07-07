(** A simpler simulation relation that hides most of the physical state,
except for the call ID stack.
Useful whenever the resources we own are strong enough to carry us from step to step.

When your goal is simple, to make it stateful just do [intros σs σt].
To go the other direction, [apply sim_simplify NEW_POST]. Then you will likely
want to clean some stuff from your context.
*)

From stbor.sim Require Import body instance refl_step.

Definition fun_post_simple
  initial_call_id_stack (r: resUR) (n: nat) vs (css: call_id_stack) vt cst :=
  (∃ c, cst = c::initial_call_id_stack ∧ end_call_sat r c) ∧
  vrel_res r vs vt.

Definition sim_simple fs ft r n es css et cst
  (Φ : resUR → nat → result → call_id_stack → result → call_id_stack → Prop) : Prop :=
  ∀ σs σt, σs.(scs) = css → σt.(scs) = cst →
    r ⊨{ n , fs , ft } ( es , σs ) ≥ ( et , σt ) :
    (λ r n vs' σs' vt' σt', Φ r n vs' σs'.(scs) vt' σt'.(scs)).

Notation "r ⊨ˢ{ n , fs , ft } ( es , css ) ≥ ( et , cst ) : Φ" :=
  (sim_simple fs ft r n%nat es%E css et%E cst Φ)
  (at level 70, es, et at next level,
   format "'[hv' r  '/' ⊨ˢ{ n , fs , ft }  '/  ' '[ ' ( es ,  css ) ']'  '/' ≥  '/  ' '[ ' ( et ,  cst ) ']'  '/' :  Φ ']'").

Section simple.
Implicit Types Φ: resUR → nat → result → call_id_stack → result → call_id_stack → Prop.

(* FIXME: does this [apply]? *)
Lemma sim_simplify
  (Φnew: resUR → nat → result → call_id_stack → result → call_id_stack → Prop)
  (Φ: resUR → nat → result → state → result → state → Prop)
  r n fs ft es σs et σt :
  (∀ r n vs σs vt σt, Φnew r n vs σs.(scs) vt σt.(scs) → Φ r n vs σs vt σt) →
  r ⊨ˢ{ n , fs , ft } (es, σs.(scs)) ≥ (et, σt.(scs)) : Φnew →
  r ⊨{ n , fs , ft } (es, σs) ≥ (et, σt) : Φ.
Proof.
  intros HΦ HH. eapply sim_local_body_post_mono; last exact: HH.
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
  eapply sim_simplify; last by eapply HH. done.
Qed.

Lemma sim_simple_bind fs ft
  (Ks: list (ectxi_language.ectx_item (bor_ectxi_lang fs)))
  (Kt: list (ectxi_language.ectx_item (bor_ectxi_lang ft)))
  es et r n css cst Φ :
  r ⊨ˢ{n,fs,ft} (es, css) ≥ (et, cst)
    : (λ r' n' es' css' et' cst',
        r' ⊨ˢ{n',fs,ft} (fill Ks es', css') ≥ (fill Kt et', cst') : Φ) →
  r ⊨ˢ{n,fs,ft} (fill Ks es, css) ≥ (fill Kt et, cst) : Φ.
Proof.
  intros HH σs σt <-<-. apply sim_body_bind.
  eapply sim_local_body_post_mono; last exact: HH.
  clear. simpl. intros r n vs σs vt σt HH. exact: HH.
Qed.

Lemma sim_simple_val fs ft r n (vs vt: value) css cst Φ :
  Φ r n vs css vt cst →
  r ⊨ˢ{S n,fs,ft} (vs, css) ≥ (vt, cst) : Φ.
Proof.
  intros HH σs σt <-<-. eapply (sim_body_result _ _ _ _ vs vt). done.
Qed.

Lemma sim_simple_place fs ft r n ls lt ts tt tys tyt css cst Φ :
  Φ r n (PlaceR ls ts tys) css (PlaceR lt tt tyt) cst →
  r ⊨ˢ{S n,fs,ft} (Place ls ts tys, css) ≥ (Place lt tt tyt, cst) : Φ.
Proof.
  intros HH σs σt <-<-. eapply (sim_body_result _ _ _ _ (PlaceR _ _ _) (PlaceR _ _ _)). done.
Qed.

(** * Administrative *)
Lemma sim_simple_init_call fs ft r n es css et cst Φ :
  (∀ c: call_id,
    let r' := res_callState c (csOwned ∅) in
    r ⋅ r' ⊨ˢ{n,fs,ft} (es, c::cst) ≥ (et, c::cst) : Φ) →
  r ⊨ˢ{n,fs,ft} (InitCall es, css) ≥ (InitCall et, cst) : Φ.
Proof.
  intros HH σs σt <-<-. apply sim_body_init_call=>/= ?.
  apply HH; done.
Qed.

(* [Val <$> _] in the goal makes this not work with [apply], but
we'd need tactic support for anything better. *)
Lemma sim_simple_call n' vls vlt rv fs ft r r' n fid css cst Φ :
  sim_local_funs_lookup fs ft →
  Forall2 (vrel rv) vls vlt →
  r ≡ r' ⋅ rv →
  (∀ rret vs vt, vrel rret vs vt →
    r' ⋅ rret ⊨ˢ{n',fs,ft} (Val vs, css) ≥ (Val vt, cst) : Φ) →
  r ⊨ˢ{n,fs,ft}
    (Call #[ScFnPtr fid] (Val <$> vls), css) ≥ (Call #[ScFnPtr fid] (Val <$> vlt), cst) : Φ.
Proof.
  intros Hfns Hrel Hres HH σs σt <-<-.
  eapply sim_body_res_proper; last apply: sim_body_step_over_call.
  - symmetry. exact: Hres.
  - done.
  - done.
  - intros. exists n'. eapply sim_body_res_proper; last apply: HH; try done.
Qed.

(** * Memory *)
Lemma sim_simple_alloc_local fs ft r n T css cst Φ :
  (∀ (l: loc) (tg: nat),
    let r' := res_mapsto l (tsize T) ☠ (init_stack (Tagged tg)) in
    Φ (r ⋅ r') n (PlaceR l (Tagged tg) T) css (PlaceR l (Tagged tg) T) cst) →
  r ⊨ˢ{n,fs,ft} (Alloc T, css) ≥ (Alloc T, cst) : Φ.
Proof.
  intros HH σs σt <-<-. apply sim_body_alloc_local=>/=. exact: HH.
Qed.

Lemma sim_simple_write_local fs ft r r' n l tg ty v v' css cst Φ :
  tsize ty = 1%nat →
  r ≡ r' ⋅ res_mapsto l 1 v' (init_stack (Tagged tg)) →
  (∀ s, v = [s] → Φ (r' ⋅ res_mapsto l 1 s (init_stack (Tagged tg))) n (ValR [☠%S]) css (ValR [☠%S]) cst) →
  r ⊨ˢ{n,fs,ft}
    (Place l (Tagged tg) ty <- #v, css) ≥ (Place l (Tagged tg) ty <- #v, cst)
  : Φ.
Proof.
Admitted.

Lemma sim_simple_retag_local fs ft r r' r'' rs n l s' s tg m ty css cst Φ :
  r ≡ r' ⋅ res_mapsto l 1 s (init_stack (Tagged tg)) →
  arel rs s' s →
  r' ≡ r'' ⋅ rs →
  (∀ l_inner tg_inner hplt,
    let s_new := ScPtr l_inner (Tagged tg_inner) in
    let tk := match m with Mutable => tkUnique | Immutable => tkPub end in
    match m with 
    | Mutable => is_Some (hplt !! l_inner)
    | Immutable => if is_freeze ty then is_Some (hplt !! l_inner) else True
    end →
    Φ (r'' ⋅ rs ⋅ res_mapsto l 1 s_new (init_stack (Tagged tg)) ⋅ res_tag tg_inner tk hplt) n (ValR [☠%S]) css (ValR [☠%S]) cst) →
  r ⊨ˢ{n,fs,ft}
    (Retag (Place l (Tagged tg) (Reference (RefPtr m) ty)) Default, css)
  ≥
    (Retag (Place l (Tagged tg) (Reference (RefPtr m) ty)) Default, cst)
  : Φ.
Proof.
Admitted.

(** * Pure *)
Lemma sim_simple_let_val fs ft r n x (vs1 vt1: value) es2 et2 css cst Φ :
  r ⊨ˢ{n,fs,ft} (subst' x vs1 es2, css) ≥ (subst' x vt1 et2, cst) : Φ →
  r ⊨ˢ{n,fs,ft} (let: x := vs1 in es2, css) ≥ ((let: x := vt1 in et2), cst) : Φ.
Proof. intros HH σs σt <-<-. apply sim_body_let; eauto. Qed.

Lemma sim_simple_let_place fs ft r n x ls lt ts tt tys tyt es2 et2 css cst Φ :
  r ⊨ˢ{n,fs,ft} (subst' x (Place ls ts tys) es2, css) ≥ (subst' x (Place lt tt tyt) et2, cst) : Φ →
  r ⊨ˢ{n,fs,ft} (let: x := Place ls ts tys in es2, css) ≥ ((let: x := Place lt tt tyt in et2), cst) : Φ.
Proof. intros HH σs σt <-<-. apply sim_body_let; eauto. Qed.

End simple.
