(** A simpler simulation relation that hides most of the physical state,
except for the call ID stack.
Useful whenever the resources we own are strong enough to carry us from step to step.

When your goal is simple, to make it stateful just do [intros σs σt].
To go the other direction, [apply sim_simplify NEW_POST]. Then you will likely
want to clean some stuff from your context.
*)

From stbor.sim Require Export body instance.
From stbor.sim Require Import refl_step.

Definition fun_post_simple
  initial_call_id_stack (r: resUR) (n: nat) vs (css: call_id_stack) vt cst :=
  (∃ c, cst = c::initial_call_id_stack ∧ end_call_sat r c) ∧
  rrel r vs vt.

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

(* TODO: also allow rewriting the postcondition. *)
Global Instance sim_simple_proper fs ft :
  Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (↔))
    (sim_simple fs ft).
Proof.
  intros r1 r2 EQr n ? <- es ? <- css ? <- et ? <- cst ? <- Φ ? <-.
  split; intros HH σs σt ??.
  - rewrite -EQr. exact: HH.
  - rewrite EQr. exact: HH.
Qed.
Global Instance: Params sim_simple 2.

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
Lemma sim_simplify'
  (Φnew: resUR → nat → result → call_id_stack → result → call_id_stack → Prop)
  (Φ: resUR → nat → result → state → result → state → Prop)
  r n fs ft es σs et σt css cst :
  (∀ r n vs σs vt σt, Φnew r n vs σs.(scs) vt σt.(scs) → Φ r n vs σs vt σt) →
  σs.(scs) = css →
  σt.(scs) = cst →
  r ⊨ˢ{ n , fs , ft } (es, css) ≥ (et, cst) : Φnew →
  r ⊨{ n , fs , ft } (es, σs) ≥ (et, σt) : Φ.
Proof.
  intros HΦ <-<-. eapply sim_simplify. done.
Qed.

Lemma sim_simple_frame_l Φ r rf n fs ft es css et cst :
  r ⊨ˢ{ n , fs , ft }
    (es, css) ≥ (et, cst)
  : (λ r' n' es' css' et' cst', ✓ (rf ⋅ r') → Φ (rf ⋅ r') n' es' css' et' cst') →
  rf ⋅ r ⊨ˢ{ n , fs , ft } (es, css) ≥ (et, cst) : Φ.
Proof.
  intros Hold σs σt <-<-. eapply sim_body_frame_l. auto.
Qed.

Lemma sim_simple_frame_r Φ r rf n fs ft es css et cst :
  r ⊨ˢ{ n , fs , ft }
    (es, css) ≥ (et, cst)
  : (λ r' n' es' css' et' cst', ✓ (r' ⋅ rf) → Φ (r' ⋅ rf) n' es' css' et' cst') →
  r ⋅ rf ⊨ˢ{ n , fs , ft } (es, css) ≥ (et, cst) : Φ.
Proof.
  intros Hold σs σt <-<-. eapply sim_body_frame_r. auto.
Qed.

Lemma sim_simple_frame_core Φ r n fs ft es css et cst :
  r ⊨ˢ{ n , fs , ft }
    (es, css) ≥ (et, cst)
  : (λ r' n' es' css' et' cst', ✓ (core r ⋅ r') → Φ (core r ⋅ r') n' es' css' et' cst') →
  r ⊨ˢ{ n , fs , ft } (es, css) ≥ (et, cst) : Φ.
Proof.
  intros Hold σs σt <-<-. eapply sim_body_frame_core. auto.
Qed.

Lemma sim_simple_frame_more_core Φ r r' n fs ft es css et cst :
  core r ⋅ r' ⊨ˢ{ n , fs , ft }
    (es, css) ≥ (et, cst)
  : (λ r'' n' es' css' et' cst', ✓ ((core r ⋅ core r') ⋅ r'') → Φ ((core r ⋅ core r') ⋅ r'') n' es' css' et' cst') →
  core r ⋅ r' ⊨ˢ{ n , fs , ft } (es, css) ≥ (et, cst) : Φ.
Proof.
  intros HH. assert (core r ⋅ r' ≡ (core r ⋅ core r') ⋅ (core r ⋅ r')) as ->.
  { rewrite {1}cmra_core_dup. rewrite - !assoc. f_equiv.
    rewrite [core r' ⋅ _]comm - !assoc. f_equiv.
    rewrite cmra_core_r //. }
  eapply sim_simple_frame_l, HH.
Qed.

Lemma sim_simple_post_mono Φ1 Φ2 r n fs ft es css et cst :
  Φ1 <6= Φ2 →
  r ⊨ˢ{ n , fs , ft } (es, css) ≥ (et, cst) : Φ1 →
  r ⊨ˢ{ n , fs , ft } (es, css) ≥ (et, cst) : Φ2.
Proof.
  intros HΦ Hold σs σt <-<-.
  eapply sim_local_body_post_mono; last exact: Hold.
  auto.
Qed.

Lemma sim_simple_valid_pre fs ft r n es css et cst Φ :
  (valid r → r ⊨ˢ{n,fs,ft} (es, css) ≥ (et, cst) : Φ) →
  r ⊨ˢ{n,fs,ft} (es, css) ≥ (et, cst) : Φ.
Proof.
  intros Hold σs σt <-<-.
  eapply sim_body_valid=>Hval.
  eapply sim_local_body_post_mono, Hold; done.
Qed.

Lemma sim_simple_valid_post fs ft r n es css et cst Φ :
  (r ⊨ˢ{n,fs,ft}
    (es, css) ≥ (et, cst)
  : (λ r' n' es' css' et' cst', valid r' → Φ r' n' es' css' et' cst')) →
  r ⊨ˢ{n,fs,ft} (es, css) ≥ (et, cst) : Φ.
Proof.
  intros Hold σs σt <-<-.
  eapply sim_body_valid=>Hval.
  eapply sim_local_body_post_mono, Hold; done.
Qed.

Lemma sim_simple_viewshift r2 r1 fs ft n es css et cst Φ :
  r1 |==> r2 →
  r2 ⊨ˢ{n,fs,ft} (es, css) ≥ (et, cst) : Φ →
  r1 ⊨ˢ{n,fs,ft} (es, css) ≥ (et, cst) : Φ.
Proof.
  intros Hvs Hold σs σt <-<-. eapply viewshift_sim_local_body, Hold; done.
Qed.

(** Simple proof for a function taking one argument. *)
(* TODO: make the two call stacks the same? *)
Lemma sim_fun_simple1 n (esf etf: function) :
  length (esf.(fun_args)) = 1%nat →
  length (etf.(fun_args)) = 1%nat →
  (∀ fs ft rf es css et cst vs vt,
    sim_local_funs_lookup fs ft →
    vrel rf vs vt →
    subst_l (esf.(fun_args)) [Val vs] (esf.(fun_body)) = Some es →
    subst_l (etf.(fun_args)) [Val vt] (etf.(fun_body)) = Some et →
    rf ⊨ˢ{n,fs,ft} (InitCall es, css) ≥ (InitCall et, cst) : fun_post_simple cst) →
  ⊨ᶠ esf ≥ etf.
Proof.
  intros Hls Hlt HH fs ft Hlook rf es et vls vlt σs σt FREL SUBSTs SUBSTt. exists n.
  move:(subst_l_is_Some_length _ _ _ _ SUBSTs) (subst_l_is_Some_length _ _ _ _ SUBSTt).
  rewrite Hls Hlt.
  destruct vls as [|vs []]; [done| |done].
  destruct vlt as [|vt []]; [done| |done].
  inversion FREL as [|???? RREL]. intros _ _. simplify_eq.
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

Lemma sim_simple_bind_call r n fs ft es css et cst (fns fnt: result) (pres pret: list result) posts postt Φ :
  r ⊨ˢ{n,fs,ft} (es, css) ≥ (et, cst)
    : (λ r' n' rs' css' rt' cst',
        r' ⊨ˢ{n',fs,ft}
          (Call fns ((of_result <$> pres) ++ (of_result rs') :: posts), css')
        ≥
          (Call fnt ((of_result <$> pret) ++ (of_result rt') :: postt), cst')
        : Φ) →
  r ⊨ˢ{n,fs,ft}
    (Call fns ((of_result <$> pres) ++ es :: posts), css)
  ≥
    (Call fnt ((of_result <$> pret) ++ et :: postt), cst)
  : Φ.
Proof.
  intros HH σs σt <-<-. apply sim_body_bind_call.
  eapply sim_local_body_post_mono; last exact: HH.
  clear. simpl. intros r n vs σs vt σt HH. exact: HH.
Qed.

Lemma sim_simple_result fs ft r n (vs vt: result) es et css cst Φ :
  IntoResult es vs → IntoResult et vt →
  Φ r n vs css vt cst →
  r ⊨ˢ{n,fs,ft} (es, css) ≥ (et, cst) : Φ.
Proof.
  intros ?? HH σs σt <-<-. eapply sim_body_result; done.
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
Lemma sim_simple_call n' rls rlt rv fs ft r r' n fe (fi: result) css cst Φ :
  IntoResult fe fi →
  sim_local_funs_lookup fs ft →
  r ≡ r' ⋅ rv →
  Forall2 (rrel rv) rls rlt →
  (∀ rret vs vt vls vlt fid,
    fi = ValR [ScFnPtr fid] →
    rls = ValR <$> vls → rlt = ValR <$> vlt →
    vrel rret vs vt →
    r' ⋅ rret ⊨ˢ{n',fs,ft} (Val vs, css) ≥ (Val vt, cst) : Φ) →
  r ⊨ˢ{n,fs,ft}
    (Call fe (of_result <$> rls), css) ≥ (Call fe (of_result <$> rlt), cst) : Φ.
Proof.
  intros <- Hfns Hres Hrel HH σs σt <-<-. rewrite Hres.
  apply: sim_body_step_over_call.
  - done.
  - done.
  - intros. exists n'. eapply sim_body_res_proper; last apply: HH; try done.
Qed.

(** * Memory: local *)
Lemma sim_simple_alloc_local fs ft r n T css cst Φ :
  (∀ (l: loc) (tg: nat),
    let rt := res_tag tg tkUnique ∅ in
    let r' := res_mapsto l (tsize T) ☠ tg in
    Φ (r ⋅ rt ⋅ r') n (PlaceR l (Tagged tg) T) css (PlaceR l (Tagged tg) T) cst) →
  r ⊨ˢ{n,fs,ft} (Alloc T, css) ≥ (Alloc T, cst) : Φ.
Proof.
  intros HH σs σt <-<-. apply sim_body_alloc_local=>/=. exact: HH.
Qed.

Lemma sim_simple_write_local fs ft r r' n l tg ty v v' css cst Φ :
  tsize ty = 1%nat →
  r ≡ r' ⋅ res_mapsto l 1 v' tg →
  (∀ s, v = [s] → Φ (r' ⋅ res_mapsto l 1 s tg) n (ValR [☠%S]) css (ValR [☠%S]) cst) →
  r ⊨ˢ{n,fs,ft}
    (Place l (Tagged tg) ty <- #v, css) ≥ (Place l (Tagged tg) ty <- #v, cst)
  : Φ.
Proof. intros Hty Hres HH σs σt <-<-. eapply sim_body_write_local_1; eauto. Qed.

Lemma sim_simple_copy_local_l fs ft r r' n l tg ty s et css cst Φ :
  tsize ty = 1%nat →
  r ≡ r' ⋅ res_mapsto l 1 s tg →
  (r ⊨ˢ{n,fs,ft} (#[s], css) ≥ (et, cst) : Φ) →
  r ⊨ˢ{n,fs,ft}
    (Copy (Place l (Tagged tg) ty), css) ≥ (et, cst)
  : Φ.
Proof.
Admitted.

Lemma sim_simple_copy_local_r fs ft r r' n l tg ty s es css cst Φ :
  tsize ty = 1%nat →
  r ≡ r' ⋅ res_mapsto l 1 s tg →
  (r ⊨ˢ{n,fs,ft} (es, css) ≥ (#[s], cst) : Φ) →
  r ⊨ˢ{n,fs,ft}
    (es, css) ≥ (Copy (Place l (Tagged tg) ty), cst)
  : Φ.
Proof.
Admitted.

Lemma sim_simple_retag_local fs ft r r' r'' rs n l s' s tg ty css cst Φ :
  r ≡ r' ⋅ res_mapsto l 1 s tg →
  arel rs s' s →
  r' ≡ r'' ⋅ rs →
  (∀ l_inner tg_inner hplt,
    let s_new := ScPtr l_inner (Tagged tg_inner) in
(*    let tk := match m with Mutable => tkUnique | Immutable => tkPub end in
    match m with 
    | Mutable => is_Some (hplt !! l_inner)
    | Immutable => if is_freeze ty then is_Some (hplt !! l_inner) else True
    end → *)
    let tk := tkUnique in
    is_Some (hplt !! l_inner) →
    Φ (r'' ⋅ rs ⋅ res_mapsto l 1 s_new tg ⋅ res_tag tg_inner tk hplt) n (ValR [☠%S]) css (ValR [☠%S]) cst) →
  r ⊨ˢ{n,fs,ft}
    (Retag (Place l (Tagged tg) (Reference (RefPtr Mutable) ty)) Default, css)
  ≥
    (Retag (Place l (Tagged tg) (Reference (RefPtr Mutable) ty)) Default, cst)
  : Φ.
Proof.
Admitted.

(** * Memory: shared *)
Lemma sim_simple_alloc_shared fs ft r n T css cst Φ :
  (∀ (l: loc) (tg: nat),
    let rt := res_tag tg tkPub ∅ in
    Φ (r ⋅ rt) n (PlaceR l (Tagged tg) T) css (PlaceR l (Tagged tg) T) cst) →
  r ⊨ˢ{n,fs,ft} (Alloc T, css) ≥ (Alloc T, cst) : Φ.
Proof.
Admitted.

Lemma sim_simple_write_shared fs ft r n (rs1 rs2 rt1 rt2: result) css cst Φ :
  rrel r rs1 rt1 →
  rrel r rs2 rt2 →
  Φ r n (ValR [☠%S]) css (ValR [☠%S]) cst →
  r ⊨ˢ{n,fs,ft} (rs1 <- rs2, css) ≥ (rt1 <- rt2, cst) : Φ.
Proof.
  intros [Hrel1 ?]%rrel_with_eq [Hrel2 ?]%rrel_with_eq. simplify_eq.
Admitted.

Lemma sim_simple_copy_shared fs ft r n (rs rt: result) css cst Φ :
  rrel r rs rt →
  (∀ r' (v1 v2: result),
    rrel r' v1 v2 →
    Φ (r ⋅ r') n v1 css v2 cst) →
  r ⊨ˢ{n,fs,ft} (Copy rs, css) ≥ (Copy rt, cst) : Φ.
Proof.
  intros [Hrel ?]%rrel_with_eq. simplify_eq.
Admitted.

Lemma sim_simple_retag_shared fs ft r n (rs rt: result) k css cst Φ :
  rrel r rs rt →
  (Φ r n (ValR [☠%S]) css (ValR [☠%S]) cst) →
  r ⊨ˢ{n,fs,ft} (Retag rs k, css) ≥ (Retag rt k, cst) : Φ.
Proof.
  intros [Hrel ?]%rrel_with_eq. simplify_eq.
Admitted.

(** * Pure *)
Lemma sim_simple_let fs ft r n x (vs1 vt1: result) es1 et1 es2 et2 css cst Φ :
  IntoResult es1 vs1 → IntoResult et1 vt1 →
  r ⊨ˢ{n,fs,ft} (subst' x es1 es2, css) ≥ (subst' x et1 et2, cst) : Φ →
  r ⊨ˢ{n,fs,ft} (let: x := es1 in es2, css) ≥ ((let: x := et1 in et2), cst) : Φ.
Proof. intros ?? HH σs σt <-<-. apply: sim_body_let. eauto. Qed.

Lemma sim_simple_ref fs ft r n (pl: result) css cst Φ :
  (∀ l t T, pl = PlaceR l t T →
    Φ r n (ValR [ScPtr l t]) css (ValR [ScPtr l t]) cst) →
  r ⊨ˢ{n,fs,ft} ((& pl)%E, css) ≥ ((& pl)%E, cst) : Φ.
Proof. intros HH σs σt <-<-. apply sim_body_ref; eauto. Qed.

Lemma sim_simple_deref fs ft r n (rf: result) T css cst Φ :
  (∀ l t, rf = ValR [ScPtr l t] →
    Φ r n (PlaceR l t T) css (PlaceR l t T) cst) →
  r ⊨ˢ{n,fs,ft} (Deref rf T, css) ≥ (Deref rf T, cst) : Φ.
Proof. intros HH σs σt <-<-. apply sim_body_deref; eauto. Qed.

Lemma sim_simple_var fs ft r n css cst var Φ :
  r ⊨ˢ{n,fs,ft} (Var var, css) ≥ (Var var, cst) : Φ.
Proof. intros σs σt <-<-. apply sim_body_var; eauto. Qed.

Lemma sim_simple_proj fs ft r n (v i: expr) (vr ir: result) css cst Φ :
  IntoResult v vr → IntoResult i ir →
  (∀ vi vv iv, vr = ValR vv → ir = ValR [ScInt iv] →
    vv !! (Z.to_nat iv) = Some vi → 0 ≤ iv →
    Φ r n (ValR [vi]) css (ValR [vi]) cst) →
  r ⊨ˢ{n,fs,ft} (Proj vr ir, css) ≥ (Proj vr ir, cst) : Φ.
Proof.
  intros ?? HH σs σt <-<-. apply sim_body_proj; eauto.
Qed.

Lemma sim_simple_conc fs ft r n (r1 r2: result) css cst Φ :
  (∀ v1 v2, r1 = ValR v1 → r2 = ValR v2 →
    Φ r n (ValR (v1 ++ v2)) css (ValR (v1 ++ v2)) cst) →
  r ⊨ˢ{n,fs,ft} (Conc r1 r2, css) ≥ (Conc r1 r2, cst) : Φ.
Proof. intros HH σs σt <-<-. apply sim_body_conc; eauto. Qed.

Lemma sim_simple_bin_op fs ft r n op (r1 r2: result) css cst Φ :
  (∀ s1 s2 s mem, r1 = ValR [s1] → r2 = ValR [s2] →
    bin_op_eval mem op s1 s2 s →
    Φ r n (ValR [s]) css (ValR [s]) cst : Prop) →
  r ⊨ˢ{n,fs,ft} (BinOp op r1 r2, css) ≥ (BinOp op r1 r2, cst) : Φ.
Proof. intros HH σs σt <-<-. apply sim_body_bin_op; eauto. Qed.

Lemma sim_simple_case fs ft r n (rc: result) els elt css cst Φ :
  length els = length elt →
  (∀ (es et: expr) (i: Z), 0 ≤ i →
    els !! (Z.to_nat i) = Some es →
    elt !! (Z.to_nat i) = Some et →
    rc = ValR [ScInt i] →
    r ⊨ˢ{n,fs,ft} (es, css) ≥ (et, cst) : Φ) →
  r ⊨ˢ{n,fs,ft} (Case rc els, css) ≥ (Case rc elt, cst) : Φ.
Proof.
  intros ? HH σs σt <-<-. apply sim_body_case; first done.
  intros. eapply HH; eauto.
Qed.

End simple.
