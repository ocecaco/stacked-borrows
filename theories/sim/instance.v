From stbor.lang Require Import steps_inversion.
From stbor.sim Require Export local invariant.

Notation "r ⊨{ n , fs , ft } ( es , σs ) ≥ ( et , σt ) : Φ" :=
  (sim_local_body wsat vrel fs ft r n%nat es%E σs et%E σt Φ)
  (at level 70, format "'[hv' r  '/' ⊨{ n , fs , ft }  '/  ' '[ ' ( es ,  '/' σs ) ']'  '/' ≥  '/  ' '[ ' ( et ,  '/' σt ) ']'  '/' :  Φ ']'").


(** "modular" simulation relations dont make assumptions
about the global fn table.
This is very weak! A stronger version would, instead of universally quantifying the
fn table, allow giving a lower bound. But this is good enough for now.

This could be done in general, but we just do it for the instance. *)
Definition sim_mod_fun f1 f2 :=
  ∀ fs ft, sim_local_funs_lookup fs ft →
           sim_local_fun wsat vrel fs ft end_call_sat f1 f2.

Definition sim_mod_funs (fns fnt: fn_env) :=
  ∀ name fn_src, fns !! name = Some fn_src → ∃ fn_tgt,
    fnt !! name = Some fn_tgt ∧
    length fn_src.(fun_args) = length fn_tgt.(fun_args) ∧
    sim_mod_fun fn_src fn_tgt.

Notation "⊨ᶠ f1 ≥ f2" :=
  (sim_mod_fun f1 f2)
  (at level 70, f1, f2 at next level, format "⊨ᶠ  f1  ≥  f2").

(** The modular version permits insertion. *)
Lemma sim_local_funs_lookup_insert fns fnt x fs ft :
  length fns.(fun_args) = length fnt.(fun_args) →
  sim_local_funs_lookup fs ft →
  sim_local_funs_lookup (<[x:=fns]>fs) (<[x:=fnt]>ft).
Proof.
  intros Hnew Hold f f_src.
  destruct (decide (x=f)) as [->|Hne].
  - rewrite lookup_insert=>[=?]. subst. exists fnt. rewrite lookup_insert.
    auto.
  - rewrite lookup_insert_ne // =>Hlk.
    destruct (Hold _ _ Hlk) as (f_tgt & ? & ?). exists f_tgt.
    rewrite lookup_insert_ne //.
Qed.

Lemma sim_mod_funs_insert fs ft x fns fnt :
  length fns.(fun_args) = length fnt.(fun_args) →
  (⊨ᶠ fns ≥ fnt) →
  sim_mod_funs fs ft →
  sim_mod_funs (<[x:=fns]>fs) (<[x:=fnt]>ft).
Proof.
  intros ? Hnew Hold. intros f fn_src.
  destruct (decide (x=f)) as [->|Hne].
  - rewrite lookup_insert=>[=?]. subst. exists fnt. rewrite lookup_insert.
    split; first done. split; first done. apply Hnew.
  - rewrite lookup_insert_ne // =>Hlk.
    destruct (Hold _ _ Hlk) as (f_tgt & ? & ? & Hf). exists f_tgt.
    rewrite lookup_insert_ne //.
Qed.

Lemma sim_mod_funs_to_lookup fs ft:
  sim_mod_funs fs ft → sim_local_funs_lookup fs ft.
Proof.
  intros Hlf name fns Hlk. destruct (Hlf _ _ Hlk) as (fnt & ? & ? & ?).
  eauto.
Qed.

(** Once we got all things together, we can get the whole-program
assumption. *)
Lemma sim_mod_funs_local fs ft :
  sim_mod_funs fs ft →
  sim_local_funs wsat vrel fs ft end_call_sat.
Proof.
  intros Hmod. intros f fn_src Hlk.
  destruct (Hmod _ _ Hlk) as (fn_tgt & ? & ? & ?). exists fn_tgt.
  eauto using sim_mod_funs_to_lookup.
Qed.

(** Whole-programs need a "main". *)
Definition has_main (prog: fn_env) : Prop :=
  ∃ ebs HCs, prog !! "main" = Some (@FunV [] ebs HCs).

Lemma has_main_insert (prog: fn_env) (x: string) (f: function) :
  x ≠ "main" → has_main prog → has_main (<[x:=f]> prog).
Proof.
  intros Hne (ebs & HCs & EQ). exists ebs, HCs.
  rewrite lookup_insert_ne //.
Qed.

Lemma rrel_eq  r (e1 e2: result) :
  rrel vrel r e1 e2 → e1 = e2.
Proof.
  destruct e1, e2; simpl; [|done..|].
  - intros ?. f_equal. by eapply vrel_eq.
  - intros [VREL ?]. subst. apply vrel_eq in VREL. by simplify_eq.
Qed.

Lemma rrel_mono (r1 r2 : resUR) (VAL: ✓ r2) :
  r1 ≼ r2 → ∀ v1 v2, rrel vrel r1 v1 v2 → rrel vrel r2 v1 v2.
Proof.
  intros Le v1 v2. destruct v1, v2; simpl; [|done..|].
  - by apply vrel_mono.
  - intros [VREL ?]. split; [|done]. move : VREL. by apply vrel_mono.
Qed.

Lemma list_Forall_result_value (es: list result) (vs: list value) :
  of_result <$> es = Val <$> vs → es = ValR <$> vs.
Proof.
  revert vs. induction es as [|e es IH]; intros vs.
  { intros Eq. symmetry in Eq. apply fmap_nil_inv in Eq. by subst vs. }
  destruct vs as [|v vs]; [by intros ?%fmap_nil_inv|].
  rewrite 3!fmap_cons. intros Eq.
  inversion Eq as [Eq1].
  rewrite (IH vs) //. f_equal.
  have Eq2 := to_of_result e. rewrite Eq1 /= in Eq2. by simplify_eq.
Qed.

Lemma list_Forall_rrel_vrel r (es et: list result) :
  Forall2 (rrel vrel r) es et →
  Forall (λ ei : expr, is_Some (to_value ei)) (of_result <$> es) →
  Forall (λ ei : expr, is_Some (to_value ei)) (of_result <$> et) →
  ∃ vs vt,  es = ValR <$> vs ∧ et = ValR <$> vt ∧
  Forall2 (vrel r) vs vt.
Proof.
  intros RREL [vs Eqs]%list_Forall_to_value [vt Eqt]%list_Forall_to_value.
  exists vs, vt.
  apply list_Forall_result_value in Eqs.
  apply list_Forall_result_value in Eqt. subst es et.
  do 2 (split; [done|]).
  by rewrite -> Forall2_fmap in RREL.
Qed.

