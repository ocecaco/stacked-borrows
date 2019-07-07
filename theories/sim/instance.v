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
  ∀ fs ft, sim_local_funs_lookup fs ft → sim_local_fun wsat vrel fs ft end_call_sat f1 f2.

Definition sim_mod_funs (fns fnt: fn_env) :=
  ∀ name fn_src, fns !! name = Some fn_src → ∃ fn_tgt,
    fnt !! name = Some fn_tgt ∧
    length fn_src.(fun_b) = length fn_tgt.(fun_b) ∧
    sim_mod_fun fn_src fn_tgt.

Notation "⊨ᶠ f1 ≥ f2" :=
  (sim_mod_fun f1 f2)
  (at level 70, f1, f2 at next level, format "⊨ᶠ  f1  ≥  f2").

(** The modular version permits insertion. *)
Lemma sim_local_funs_lookup_insert fns fnt x fs ft :
  length fns.(fun_b) = length fnt.(fun_b) →
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
  length fns.(fun_b) = length fnt.(fun_b) →
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
