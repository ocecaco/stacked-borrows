(** A simpler simulation relation that hides most of the physical state,
except for the call ID stack.
Useful whenever the resources we own are strong enough to carry us from step to step.

When your goal is simple, to make it stateful just do [intros σs σt].
To go the other direction, [apply sim_simplify NEW_POST]. Then you will likely
want to clean some stuff from your context.
*)

From stbor.sim Require Export body instance.
From stbor.sim Require Import refl_step right_step left_step viewshift.

Definition sim_simple fs ft r n es et
  (Φ : resUR → nat → result → result → Prop) : Prop :=
  ∀ σs σt, r ⊨{ n , fs , ft } ( es , σs ) ≥ ( et , σt ) :
    (λ r n vs' σs' vt' σt', σs'.(scs) = σs.(scs) ∧ σt'.(scs) = σt.(scs) ∧ Φ r n vs' vt').

Notation "r ⊨ˢ{ n , fs , ft } es ≥ et : Φ" :=
  (sim_simple fs ft r n%nat es%E et%E Φ)
  (at level 70, es, et at next level,
   format "'[hv' r  '/' ⊨ˢ{ n , fs , ft }  '/  ' '[ ' es ']'  '/' ≥  '/  ' '[ ' et ']'  '/' :  Φ ']'").

Section simple.
Implicit Types Φ: resUR → nat → result → result → Prop.

(* TODO: also allow rewriting the postcondition. *)
Global Instance sim_simple_proper fs ft :
  Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (↔))
    (sim_simple fs ft).
Proof.
  intros r1 r2 EQr n ? <- es ? <- et ? <- Φ ? <-.
  split; intros HH σs σt.
  - rewrite -EQr. exact: HH.
  - rewrite EQr. exact: HH.
Qed.
Global Instance: Params sim_simple 2.

Lemma sim_simplify
  (Φnew: resUR → nat → result → result → Prop)
  (Φ: resUR → nat → result → state → result → state → Prop)
  r n fs ft es σs et σt :
  (∀ r n vs σs' vt σt',
    σs'.(scs) = σs.(scs) →
    σt'.(scs) = σt.(scs) →
    Φnew r n vs vt →
    Φ r n vs σs' vt σt'
  ) →
  r ⊨ˢ{ n , fs , ft } es ≥ et : Φnew →
  r ⊨{ n , fs , ft } (es, σs) ≥ (et, σt) : Φ.
Proof.
  intros HΦ HH. eapply sim_local_body_post_mono; last exact: HH.
  naive_solver.
Qed.
(*Lemma sim_simplify'
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
Qed.*)

Lemma sim_simple_frame_l Φ r rf n fs ft es et :
  r ⊨ˢ{ n , fs , ft }
    es ≥ et
  : (λ r' n' es' et', ✓ (rf ⋅ r') → Φ (rf ⋅ r') n' es' et') →
  rf ⋅ r ⊨ˢ{ n , fs , ft } es ≥ et : Φ.
Proof.
  intros Hold σs σt. eapply sim_body_frame_l.
  eapply sim_local_body_post_mono, Hold. naive_solver.
Qed.

Lemma sim_simple_frame_r Φ r rf n fs ft es et :
  r ⊨ˢ{ n , fs , ft }
    es ≥ et
  : (λ r' n' es' et', ✓ (r' ⋅ rf) → Φ (r' ⋅ rf) n' es' et') →
  r ⋅ rf ⊨ˢ{ n , fs , ft } es ≥ et : Φ.
Proof.
  intros Hold σs σt. eapply sim_body_frame_r.
  eapply sim_local_body_post_mono, Hold. naive_solver.
Qed.

Lemma sim_simple_frame_core Φ r n fs ft es et :
  r ⊨ˢ{ n , fs , ft }
    es ≥ et
  : (λ r' n' es' et', ✓ (core r ⋅ r') → Φ (core r ⋅ r') n' es' et') →
  r ⊨ˢ{ n , fs , ft } es ≥ et : Φ.
Proof.
  intros Hold σs σt. eapply sim_body_frame_core.
  eapply sim_local_body_post_mono, Hold. naive_solver.
Qed.

Lemma sim_simple_frame_more_core Φ r r' n fs ft es et :
  core r ⋅ r' ⊨ˢ{ n , fs , ft }
    es ≥ et
  : (λ r'' n' es' et', ✓ ((core r ⋅ core r') ⋅ r'') → Φ ((core r ⋅ core r') ⋅ r'') n' es' et') →
  core r ⋅ r' ⊨ˢ{ n , fs , ft } es ≥ et : Φ.
Proof.
  intros HH. assert (core r ⋅ r' ≡ (core r ⋅ core r') ⋅ (core r ⋅ r')) as ->.
  { rewrite {1}cmra_core_dup. rewrite - !assoc. f_equiv.
    rewrite [core r' ⋅ _]comm - !assoc. f_equiv.
    rewrite cmra_core_r //. }
  eapply sim_simple_frame_l, HH.
Qed.

Lemma sim_simple_post_mono Φ1 Φ2 r n fs ft es et :
  Φ1 <4= Φ2 →
  r ⊨ˢ{ n , fs , ft } es ≥ et : Φ1 →
  r ⊨ˢ{ n , fs , ft } es ≥ et : Φ2.
Proof.
  intros HΦ Hold σs σt. eapply sim_local_body_post_mono, Hold. naive_solver.
Qed.

Lemma sim_simple_valid_pre fs ft r n es et Φ :
  (valid r → r ⊨ˢ{n,fs,ft} es ≥ et : Φ) →
  r ⊨ˢ{n,fs,ft} es ≥ et : Φ.
Proof.
  intros Hold σs σt. eapply sim_body_valid=>Hval.
  eapply sim_local_body_post_mono, Hold; naive_solver.
Qed.

Lemma sim_simple_valid_post fs ft r n es et Φ :
  (r ⊨ˢ{n,fs,ft}
    es ≥ et
  : (λ r' n' es' et', valid r' → Φ r' n' es' et')) →
  r ⊨ˢ{n,fs,ft} es ≥ et : Φ.
Proof.
  intros Hold σs σt. eapply sim_body_valid=>Hval.
  eapply sim_local_body_post_mono, Hold; naive_solver.
Qed.

Lemma sim_simple_viewshift r2 r1 fs ft n es et Φ :
  r1 |==> r2 →
  r2 ⊨ˢ{n,fs,ft} es ≥ et : Φ →
  r1 ⊨ˢ{n,fs,ft} es ≥ et : Φ.
Proof.
  intros Hvs Hold σs σt. eapply viewshift_sim_local_body, Hold; naive_solver.
Qed.

(** * Simple proof for a function body. *)
Definition fun_post_simple c (r: resUR) (n: nat) vs vt :=
  res_cs c ∅ ≼ r ∧ rrel r vs vt.

Lemma sim_fun_simple n (esf etf: function) :
  length (esf.(fun_args)) = length (etf.(fun_args)) →
  (∀ fs ft rf es et vls vlt c,
    sim_local_funs_lookup fs ft →
    Forall2 (vrel rf) vls vlt →
    subst_l (esf.(fun_args)) (Val <$> vls) (esf.(fun_body)) = Some es →
    subst_l (etf.(fun_args)) (Val <$> vlt) (etf.(fun_body)) = Some et →
    rf ⋅ res_cs c ∅ ⊨ˢ{n,fs,ft} es ≥ et : fun_post_simple c) →
  ⊨ᶠ esf ≥ etf.
Proof.
  intros Hl HH fs ft Hlook rf es et vls vlt σs σt FREL SUBSTs SUBSTt. exists n.
  apply sim_body_init_call=>/= ?.
  eapply sim_body_valid=>Hval.
  eapply sim_simplify; last exact: HH.
  move=>/= r ? vs' σs' vt' σt' ?? [??].
  split; last done.
  eexists. split; first done.
  eapply res_end_call_sat; done.
Qed.

Lemma sim_fun_simple1 n (esf etf: function) :
  length (esf.(fun_args)) = 1%nat →
  length (etf.(fun_args)) = 1%nat →
  (∀ fs ft rf es et v c,
    sim_local_funs_lookup fs ft →
    vrel rf v v →
    subst_l (esf.(fun_args)) [Val v] (esf.(fun_body)) = Some es →
    subst_l (etf.(fun_args)) [Val v] (etf.(fun_body)) = Some et →
    rf ⋅ res_cs c ∅ ⊨ˢ{n,fs,ft} es ≥ et : fun_post_simple c) →
  ⊨ᶠ esf ≥ etf.
Proof.
  intros Hls Hlt HH. eapply sim_fun_simple.
  { rewrite Hls Hlt //. }
  intros ?? rf ?? vls vlt c ? FREL SUBSTs SUBSTt.
  move:(subst_l_is_Some_length _ _ _ _ SUBSTs) (subst_l_is_Some_length _ _ _ _ SUBSTt).
  rewrite Hls Hlt=>??.
  destruct vls as [|vs []]; [done| |done].
  destruct vlt as [|vt []]; [done| |done].
  inversion FREL as [|???? RREL]. specialize (vrel_eq _ _ _ RREL)=>?.
  simplify_eq. eapply HH; done.
Qed.

Lemma sim_simple_bind fs ft
  (Ks: list (ectxi_language.ectx_item (bor_ectxi_lang fs))) es
  (Kt: list (ectxi_language.ectx_item (bor_ectxi_lang ft))) et
  r n Φ :
  r ⊨ˢ{n,fs,ft} es ≥ et
    : (λ r' n' es' et',
        r' ⊨ˢ{n',fs,ft} fill Ks es' ≥ fill Kt et' : Φ) →
  r ⊨ˢ{n,fs,ft} fill Ks es ≥ fill Kt et : Φ.
Proof.
  intros HH σs σt. apply sim_body_bind.
  eapply sim_local_body_post_mono; last exact: HH.
  clear. simpl. intros r n vs σs' vt σ't [<- [<- HH]]. exact: HH.
Qed.

Lemma sim_simple_bind_call r n fs ft es et (fns fnt: result) (pres pret: list result) posts postt Φ :
  r ⊨ˢ{n,fs,ft} es ≥ et
    : (λ r' n' rs' rt',
        r' ⊨ˢ{n',fs,ft}
          Call fns ((of_result <$> pres) ++ (of_result rs') :: posts)
        ≥
          Call fnt ((of_result <$> pret) ++ (of_result rt') :: postt)
        : Φ) →
  r ⊨ˢ{n,fs,ft}
    Call fns ((of_result <$> pres) ++ es :: posts)
  ≥
    Call fnt ((of_result <$> pret) ++ et :: postt)
  : Φ.
Proof.
  intros HH σs σt. apply sim_body_bind_call.
  eapply sim_local_body_post_mono; last exact: HH.
  clear. simpl. intros r n vs σs' vt σt' [<- [<- HH]]. exact: HH.
Qed.

Lemma sim_simple_result fs ft r n (vs vt: result) es et Φ :
  IntoResult es vs → IntoResult et vt →
  Φ r n vs vt →
  r ⊨ˢ{n,fs,ft} es ≥ et : Φ.
Proof.
  intros ?? HH σs σt. eapply sim_body_result; done.
Qed.

(** * Calls *)
(* [Val <$> _] in the goal makes this not work with [apply], but
we'd need tactic support for anything better. *)
Lemma sim_simple_call n' rls rlt rv fs ft r r' n fe (fi: result) Φ :
  IntoResult fe fi →
  sim_local_funs_lookup fs ft →
  r ≡ r' ⋅ rv →
  Forall2 (rrel rv) rls rlt →
  (∀ rret vs vt vls vlt fid,
    fi = ValR [ScFnPtr fid] →
    rls = ValR <$> vls → rlt = ValR <$> vlt →
    vrel rret vs vt →
    r' ⋅ rret ⊨ˢ{n',fs,ft} Val vs ≥ Val vt : Φ) →
  r ⊨ˢ{n,fs,ft}
    Call fe (of_result <$> rls) ≥ Call fe (of_result <$> rlt) : Φ.
Proof.
  intros <- Hfns Hres Hrel HH σs σt. rewrite Hres.
  apply: sim_body_step_over_call.
  - done.
  - done.
  - intros. exists n'. eapply sim_body_res_proper; last exact: HH; try done.
    rewrite STACKS STACKT. done.
Qed.

(** * Memory: local *)
Lemma sim_simple_alloc_local fs ft r n T Φ :
  (∀ (l: loc) (tg: nat),
    let r' := res_loc l (repeat (☠%S,☠%S) (tsize T)) tg in
    Φ (r ⋅ r') n (PlaceR l (Tagged tg) T) (PlaceR l (Tagged tg) T)) →
  r ⊨ˢ{n,fs,ft} Alloc T ≥ Alloc T : Φ.
Proof.
  intros HH σs σt. apply sim_body_alloc_local; eauto.
Qed.

Lemma sim_simple_free_local_1 fs ft r r' n l tg ty v Φ :
  tsize ty = 1%nat →
  r ≡ r' ⋅ res_loc l [v] tg →
  Φ r' n (ValR [☠%S]) (ValR [☠%S]) →
  r ⊨ˢ{n,fs,ft} Free (Place l (Tagged tg) ty) ≥ Free (Place l (Tagged tg) ty) : Φ.
Proof.
  intros Hty Hres HH σs σt. eapply sim_body_free_unique_local_1; eauto.
Qed.

Lemma sim_simple_write_local fs ft r r' n l tg ty v v' Φ :
  tsize ty = 1%nat →
  r ≡ r' ⋅ res_loc l [v'] tg →
  (∀ s, v = [s] → Φ (r' ⋅ res_loc l [(s,s)] tg) n (ValR [☠%S]) (ValR [☠%S])) →
  r ⊨ˢ{n,fs,ft}
    (Place l (Tagged tg) ty <- #v) ≥ (Place l (Tagged tg) ty <- #v)
  : Φ.
Proof. intros Hty Hres HH σs σt. eapply sim_body_write_local_1; eauto. Qed.

Lemma sim_simple_copy_local_l fs ft r r' n l tg ty ss st et Φ :
  tsize ty = 1%nat →
  r ≡ r' ⋅ res_loc l [(ss, st)] tg →
  (r ⊨ˢ{n,fs,ft} #[ss] ≥ et : Φ) →
  r ⊨ˢ{n,fs,ft}
    Copy (Place l (Tagged tg) ty) ≥ et
  : Φ.
Proof.
  intros ?? Hold σs σt.
  eapply sim_body_copy_local_l; eauto.
Qed.

Lemma sim_simple_copy_local_r fs ft r r' n l tg ty ss st es Φ :
  tsize ty = 1%nat →
  r ≡ r' ⋅ res_loc l [(ss,st)] tg →
  (r ⊨ˢ{n,fs,ft} es ≥ #[st] : Φ) →
  r ⊨ˢ{S n,fs,ft}
    es ≥ Copy (Place l (Tagged tg) ty)
  : Φ.
Proof.
  intros ?? Hold σs σt.
  eapply sim_body_copy_local_r; eauto.
Qed.

Lemma sim_simple_copy_local fs ft r r' n l tg ty ss st Φ :
  tsize ty = 1%nat →
  r ≡ r' ⋅ res_loc l [(ss,st)] tg →
  (r ⊨ˢ{n,fs,ft} #[ss] ≥ #[st] : Φ) →
  r ⊨ˢ{S n,fs,ft}
    Copy (Place l (Tagged tg) ty) ≥ Copy (Place l (Tagged tg) ty)
  : Φ.
Proof.
  intros ?? Hcont.
  eapply sim_simple_copy_local_l; [done..|].
  eapply sim_simple_copy_local_r; done.
Qed.

Lemma sim_simple_retag_ref fs ft r n (ptr: scalar) m ty Φ :
  (0 < tsize ty)%nat →
  (if m is Immutable then is_freeze ty else True) →
  arel r ptr ptr →
  (∀ l told tnew hplt,
    ptr = ScPtr l told →
    let s_new := ScPtr l (Tagged tnew) in
    let tk := match m with Mutable => tkUnique | Immutable => tkPub end in
    let s_new := ScPtr l (Tagged tnew) in
    (∀ i: nat, (i < tsize ty)%nat → is_Some $ hplt !! (l +ₗ i)) →
    Φ (r ⋅ res_tag tnew tk hplt) n (ValR [s_new]) (ValR [s_new])) →
  r ⊨ˢ{n,fs,ft}
    Retag #[ptr] (RefPtr m) ty Default
  ≥
    Retag #[ptr] (RefPtr m) ty Default
  : Φ.
Proof.
  intros ??? HH σs σt.
  apply sim_body_retag_ref_default; eauto.
  intros ??????????? HS. do 2 (split; [done|]). eapply HH; eauto.
  intros ??. by apply HS.
Qed.

(** * Memory: shared *)
Lemma sim_simple_alloc_public fs ft r n T Φ :
  (∀ (l: loc) (tg: nat),
    let rt := res_tag tg tkPub ∅ in
    Φ (r ⋅ rt) n (PlaceR l (Tagged tg) T) (PlaceR l (Tagged tg) T)) →
  r ⊨ˢ{n,fs,ft} Alloc T ≥ Alloc T : Φ.
Proof.
  intros HH σs σt. apply sim_body_alloc_public=>/=; eauto.
Qed.

Lemma sim_simple_free_public fs ft r es rs et rt n Φ :
  IntoResult es rs → IntoResult et rt →
  rrel r rs rt →
  Φ r n (ValR [☠%S]) (ValR [☠%S]) →
  r ⊨ˢ{n,fs,ft} Free es ≥ Free et : Φ.
Proof.
  intros <- <- [Hrel <-]%rrel_with_eq HH σs σt. eapply sim_body_free_public; eauto.
Qed.

Lemma sim_simple_write_public fs ft r n (rs1 rs2 rt1 rt2: result) Φ :
  rrel r rs1 rt1 →
  rrel r rs2 rt2 →
  Φ r n (ValR [☠%S]) (ValR [☠%S]) →
  r ⊨ˢ{n,fs,ft} (rs1 <- rs2) ≥ (rt1 <- rt2) : Φ.
Proof.
  intros [Hrel1 ?]%rrel_with_eq [Hrel2 ?]%rrel_with_eq. simplify_eq.
  intros HH σs σt. eapply sim_body_write_public; eauto.
Qed.

Lemma sim_simple_copy_public fs ft r n (rs rt: result) Φ :
  rrel r rs rt →
  (∀ r' (v1 v2: value),
    (* this post-condition is weak, we can return related values *)
    vrel r' v1 v2 →
    Φ (r ⋅ r') n v1 v2) →
  r ⊨ˢ{n,fs,ft} Copy rs ≥ Copy rt : Φ.
Proof.
  intros [Hrel <-]%rrel_with_eq HH σs σt.
  eapply sim_body_copy_public; eauto.
Qed.

Lemma sim_simple_retag_public fs ft r n (rs rt: result) pk T rk Φ :
  rrel r rs rt →
  (∀ l old new rt, rs = ValR [ScPtr l old] →
    vrel (r ⋅ rt) [ScPtr l new] [ScPtr l new] →
    Φ (r ⋅ rt) n (ValR [ScPtr l new]) (ValR [ScPtr l new])) →
  r ⊨ˢ{n,fs,ft} Retag rs pk T rk ≥ Retag rt pk T rk : Φ.
Proof.
  intros [Hrel ?]%rrel_with_eq HH σs σt. simplify_eq.
  eapply sim_body_retag_public; eauto.
Qed.

(** * Pure *)
Lemma sim_simple_let fs ft r n x (vs1 vt1: result) es1 et1 es2 et2 Φ :
  IntoResult es1 vs1 → IntoResult et1 vt1 →
  r ⊨ˢ{n,fs,ft} (subst' x es1 es2) ≥ (subst' x et1 et2) : Φ →
  r ⊨ˢ{n,fs,ft} (let: x := es1 in es2) ≥ (let: x := et1 in et2) : Φ.
Proof. intros ?? HH σs σt. apply: sim_body_let. eauto. Qed.

Lemma sim_simple_ref fs ft r n (pl: result) Φ :
  (∀ l t T, pl = PlaceR l t T →
    Φ r n (ValR [ScPtr l t]) (ValR [ScPtr l t])) →
  r ⊨ˢ{n,fs,ft} (& pl) ≥ (& pl) : Φ.
Proof. intros HH σs σt. apply sim_body_ref; eauto. Qed.

Lemma sim_simple_deref fs ft r n ef (rf: result) T Φ :
  IntoResult ef rf →
  (∀ l t, rf = ValR [ScPtr l t] →
    Φ r n (PlaceR l t T) (PlaceR l t T)) →
  r ⊨ˢ{n,fs,ft} Deref ef T ≥ Deref ef T : Φ.
Proof. intros <- HH σs σt. apply sim_body_deref; eauto. Qed.

Lemma sim_simple_var fs ft r n var Φ :
  r ⊨ˢ{n,fs,ft} Var var ≥ Var var : Φ.
Proof. intros σs σt. apply sim_body_var; eauto. Qed.

Lemma sim_simple_proj fs ft r n (v i: expr) (vr ir: result) Φ :
  IntoResult v vr → IntoResult i ir →
  (∀ vi vv iv, vr = ValR vv → ir = ValR [ScInt iv] →
    vv !! (Z.to_nat iv) = Some vi → 0 ≤ iv →
    Φ r n (ValR [vi]) (ValR [vi])) →
  r ⊨ˢ{n,fs,ft} Proj vr ir ≥ Proj vr ir : Φ.
Proof.
  intros ?? HH σs σt. apply sim_body_proj; eauto.
Qed.

Lemma sim_simple_conc fs ft r n (r1 r2: result) Φ :
  (∀ v1 v2, r1 = ValR v1 → r2 = ValR v2 →
    Φ r n (ValR (v1 ++ v2)) (ValR (v1 ++ v2))) →
  r ⊨ˢ{n,fs,ft} Conc r1 r2 ≥ Conc r1 r2 : Φ.
Proof. intros HH σs σt. apply sim_body_conc; eauto. Qed.

Lemma sim_simple_bin_op fs ft r n op (r1 r2: result) Φ :
  (∀ s1 s2 s mem, r1 = ValR [s1] → r2 = ValR [s2] →
    bin_op_eval mem op s1 s2 s →
    Φ r n (ValR [s]) (ValR [s])) →
  r ⊨ˢ{n,fs,ft} BinOp op r1 r2 ≥ BinOp op r1 r2 : Φ.
Proof. intros HH σs σt. apply sim_body_bin_op; eauto. Qed.

Lemma sim_simple_case fs ft r n (rc: result) els elt Φ :
  length els = length elt →
  (∀ (es et: expr) (i: Z), 0 ≤ i →
    els !! (Z.to_nat i) = Some es →
    elt !! (Z.to_nat i) = Some et →
    rc = ValR [ScInt i] →
    r ⊨ˢ{n,fs,ft} es ≥ et : Φ) →
  r ⊨ˢ{n,fs,ft} Case rc els ≥ Case rc elt : Φ.
Proof.
  intros ? HH σs σt. apply sim_body_case; first done.
  intros. eapply HH; eauto.
Qed.

End simple.
