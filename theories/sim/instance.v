From stbor.lang Require Import steps_inversion.
From stbor.sim Require Export local invariant.

Notation "r ⊨{ n , fs , ft } ( es , σs ) ≥ ( et , σt ) : Φ" :=
  (sim_local_body wsat vrel fs ft r n%nat es%E σs et%E σt Φ)
  (at level 70, format "'[hv' r  '/' ⊨{ n , fs , ft }  '/  ' '[ ' ( es ,  '/' σs ) ']'  '/' ≥  '/  ' '[ ' ( et ,  '/' σt ) ']'  '/' :  Φ ']'").

Notation "⊨ᶠ{ fs , ft } f1 ≥ f2" :=
  (sim_local_fun wsat vrel fs ft end_call_sat f1 f2)
  (at level 70, f1, f2 at next level, format "⊨ᶠ{ fs , ft }  f1  ≥  f2").

Lemma sim_body_result fs ft r n es et σs σt Φ :
  (✓ r → Φ r n es σs et σt : Prop) →
  r ⊨{S n,fs,ft} (of_result es, σs) ≥ (of_result et, σt) : Φ.
Proof.
  intros POST. pfold.  split; last first.
  { constructor 1. intros vt' ? STEPT'. exfalso.
    apply result_tstep_stuck in STEPT'. by rewrite to_of_result in STEPT'. }
  { move => ? /= Eqvt'. symmetry in Eqvt'. simplify_eq.
    exists es, σs, r, n. split; last split.
    - right. split; [lia|]. eauto.
    - eauto.
    - rewrite to_of_result in Eqvt'. simplify_eq.
      apply POST. by destruct WSAT as (?&?&?%cmra_valid_op_r &?). }
  { left. rewrite to_of_result. by eexists. }
Qed.

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

Lemma sim_local_body_insert fs ft fns fnt x r n es et σs σt Φ 
  (FRESH : fs !! x = None)
  (HOLD: sim_local_funs_lookup fs ft) :
  ⊨ᶠ{fs,ft} fns ≥ fnt →
  r ⊨{n,fs,ft} (es, σs) ≥ (et, σt) : Φ →
  r ⊨{n,<[x:=fns]> fs,<[x:=fnt]> ft} (es, σs) ≥ (et, σt) : Φ.
Proof.
  intros FUN. revert r n es et σs σt Φ. pcofix CIH.
  intros r1 n es et σs σt Φ SIM. punfold SIM. pfold.
  intros NT r_f WSAT.
  have NT2: never_stuck fs es σs. { admit. }
  specialize (SIM NT2 r_f WSAT) as [NS TE ST]. split.
  - destruct NS as [|RED]; [by left|]. right. admit.
  - intros vt Eqvt.
    specialize (TE _ Eqvt) as (vs' & σs' & r' & n' & STEPS' & WSAT' & HΦ).
    exists vs', σs', r', n'. split; last split; [|done..].
    { destruct STEPS' as [STEPS'|]; [|by right]. left. admit. }
  - inversion ST.
    + constructor 1.
      intros et' σt' STEPT.
      have STEPT2: (et, σt) ~{ft}~> (et', σt'). { admit. }
      specialize (STEP _ _ STEPT2) as (vs' & σs' & r' & n' & STEPS' & WSAT' & CONT).
      exists vs', σs', r', n'. split; last split; [|done|].
      { admit. }
      pclearbot. right. by apply CIH.
    + econstructor 2; eauto.
      { instantiate (1:= Ks). admit. }
      intros r' vs vt σs' σt' VREL' WSAT' STACK'.
      specialize (CONT r' vs vt σs' σt' VREL' WSAT' STACK') as [n' CONT].
      exists n'. pclearbot. right. by apply CIH.
Admitted.

Lemma sim_local_funs_insert fns fnt x fs ft :
  length fns.(fun_b) = length fnt.(fun_b) →
  fs !! x = None →
  (* FIXME: add notation for this. Probably replacing ⊨ᶠ. *)
  (∀ fs ft, sim_local_funs_lookup fs ft → ⊨ᶠ{ fs , ft } fns ≥ fnt) →
  sim_local_funs wsat vrel fs ft end_call_sat →
  sim_local_funs wsat vrel (<[x:=fns]>fs) (<[x:=fnt]>ft) end_call_sat.
Proof.
  intros ?? Hnew Hold. intros f fn_src.
  destruct (decide (x=f)) as [->|Hne].
  - rewrite lookup_insert=>[=?]. subst. exists fnt. rewrite lookup_insert.
    split; first done. split; first done. apply Hnew.
    apply sim_local_funs_lookup_insert; first done.
    exact: sim_local_funs_to_lookup.
  - rewrite lookup_insert_ne // =>Hlk.
    destruct (Hold _ _ Hlk) as (f_tgt & ? & ? & Hf). exists f_tgt.
    rewrite lookup_insert_ne //. split; first done.
    split; first done.
    have ? : sim_local_funs_lookup fs ft by eapply sim_local_funs_to_lookup.
    intros r es et vs vt σs σt VREL SUBS SUBT.
    specialize (Hf r es et vs vt σs σt VREL SUBS SUBT) as [n Hf].
    exists n. apply sim_local_body_insert; [done..|by apply Hnew|done].
Qed.
