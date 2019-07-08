From stbor.lang Require Import steps_inversion.
From stbor.sim Require Export instance.

Set Default Proof Using "Type".


Lemma sim_body_bind fs ft r n
  (Ks: list (ectxi_language.ectx_item (bor_ectxi_lang fs)))
  (Kt: list (ectxi_language.ectx_item (bor_ectxi_lang ft))) es et σs σt Φ :
  r ⊨{n,fs,ft} (es, σs) ≥ (et, σt)
    : (λ r' n' es' σs' et' σt',
        r' ⊨{n',fs,ft} (fill Ks es', σs') ≥ (fill Kt et', σt') : Φ) →
  r ⊨{n,fs,ft} (fill Ks es, σs) ≥ (fill Kt et, σt) : Φ.
Proof.
  revert r n Ks Kt es et σs σt Φ. pcofix CIH.
  intros r1 n Ks Kt es et σs σt Φ SIM. pfold. punfold SIM. intros NT ??.
  have NT2 := never_stuck_fill_inv _ _ _ _ NT.
  destruct (SIM NT2 _ WSAT) as [NTT TM ST]. clear SIM. split.
  { destruct NTT as [[vt Eqvt]|RED].
    - rewrite -(of_to_result _ _ Eqvt).
      destruct (TM _ Eqvt) as (vs' & σs' & r' & SS' & WSAT' & CONT).
      have STEPK: (fill (Λ:=bor_ectxi_lang fs) Ks es, σs)
                ~{fs}~>* (fill (Λ:=bor_ectxi_lang fs) Ks vs', σs').
      { by apply fill_tstep_rtc. }
      have NT3:= never_stuck_tstep_rtc _ _ _ _ _ STEPK NT.
      punfold CONT.
      destruct (CONT NT3 _ WSAT') as [NTT' _ _]. done.
    - right. by eapply tstep_reducible_fill. }
  { (* Kt[et] is a value *)
    clear ST. intros vt Eqvt.
    destruct (fill_result _ Kt et) as [Tt ?]; [by eexists|].
    subst Kt. simpl in *.
    destruct (TM _ Eqvt) as (vs' & σs' & r' & SS' & WSAT' & CONT).
    punfold CONT.
    have STEPK: (fill (Λ:=bor_ectxi_lang fs) Ks es, σs)
                ~{fs}~>* (fill (Λ:=bor_ectxi_lang fs) Ks vs', σs').
    { by apply (fill_tstep_rtc fs Ks es). }
    have NT3:= never_stuck_tstep_rtc _ _ _ _ _ STEPK NT.
    destruct (CONT NT3 _ WSAT') as [NTT' TM' ST'].
    destruct (TM' vt) as (vs2 & σs2 & r2 & SS2 & ?);
      [by apply to_of_result|].
    exists vs2, σs2, r2. split; [|done].
    etrans; [|apply SS2]. by apply fill_tstep_rtc. }
  (* Kt[et] makes a step *)
  inversion_clear ST as [|Ks1 Kt1].
  { (* step into Kt[et] *)
   destruct (to_result et) as [vt|] eqn:Eqvt.
    - (* et is value *)
      have ? : et = of_result vt. { symmetry. by apply of_to_result. }
      subst et. clear Eqvt.
      destruct (TM _ eq_refl) as (vs' & σs' & r' & SS' & WSAT' & CONT').
      clear TM.
      have STEPK: (fill (Λ:=bor_ectxi_lang fs) Ks es, σs)
                  ~{fs}~>* (fill (Λ:=bor_ectxi_lang fs) Ks vs', σs').
      { by apply (fill_tstep_rtc fs Ks es). }
      have NT3:= never_stuck_tstep_rtc _ _ _ _ _ STEPK NT.
      punfold CONT'.
      destruct (CONT' NT3 _ WSAT') as [NTT' TM' ST']. clear CONT' WSAT' STEP.
      inversion ST' as [|Ks1 Kt1].
      + constructor 1. intros.
        destruct (STEP _ _ STEPT) as (es2 & σs2 & r2 & idx2 & SS2 & WSAT2 & CONT2).
        exists es2, σs2, r2, idx2. split; last split; [|done|].
        { clear -SS2 SS' STEPK.
          destruct SS2 as [|[]].
          - left. eapply tc_rtc_l; eauto.
          - simplify_eq. inversion STEPK; simplify_eq.
            + by right.
            + left. eapply tc_rtc_r; [by apply tc_once|eauto]. }
        { pclearbot. left. eapply paco7_mon_bot; eauto. }
      + eapply (sim_local_body_step_over_call _ _ _ _ _ _ _ _ _ _ _ _ _
            Ks1 Kt1 fid vl_tgt _ _ _ _ CALLTGT); eauto; [by etrans|].
        intros r4 vs4 vt4 σs4 σt4 VREL4 WSAT4 STACK4.
        destruct (CONT _ _ _ σs4 σt4 VREL4 WSAT4 STACK4) as [idx4 CONT4].
        exists idx4. pclearbot. left.  eapply paco7_mon_bot; eauto.
    - (* et makes a step *)
      constructor 1. intros.
      destruct (fill_tstep_inv _ _ _ _ _ _ Eqvt STEPT) as [et2 [? STEP2]].
      subst et'.
      destruct (STEP _ _ STEP2) as (es' & σs' & r' & idx' & SS' & WSAT' & CONT').
      exists (fill Ks es'), σs', r', idx'. split; last split; [|done|].
      + clear -SS'. destruct SS' as [|[]].
        * left. by apply fill_tstep_tc.
        * simplify_eq. right. split; [|done]. lia.
      + pclearbot. right. by apply CIH. }
  { (* Kt[et] has a call, and we step over the call *)
    eapply (sim_local_body_step_over_call _ _ _ _ _ _ _ _ _ _ _ _ _
            (Ks1 ++ Ks) (Kt1 ++ Kt) fid vl_tgt); [by rewrite CALLTGT fill_app|..];
            eauto; [rewrite fill_app; by apply fill_tstep_rtc|].
    intros r' vs' vt' σs' σt' VREL' WSAT' STACK'.
    destruct (CONT _ _ _ σs' σt' VREL' WSAT' STACK') as [idx' CONT2]. clear CONT.
    exists idx'. rewrite 2!fill_app.
    pclearbot. right. by apply CIH. }
Qed.


Lemma sim_body_result fs ft r n es et σs σt Φ :
  (✓ r → Φ r n es σs et σt : Prop) →
  r ⊨{n,fs,ft} (of_result es, σs) ≥ (of_result et, σt) : Φ.
Proof.
  intros POST. pfold.  split; last first.
  { constructor 1. intros vt' ? STEPT'. exfalso.
    apply result_tstep_stuck in STEPT'. by rewrite to_of_result in STEPT'. }
  { move => ? /= Eqvt'. symmetry in Eqvt'. simplify_eq.
    exists es, σs, r. split; last split.
    - constructor 1.
    - eauto.
    - rewrite to_of_result in Eqvt'. simplify_eq.
      apply POST. by destruct WSAT as (?&?&?%cmra_valid_op_r &?). }
  { left. rewrite to_of_result. by eexists. }
Qed.

Lemma sim_body_res_ext fs ft n es σs et σt Φ r1 r2:
  r1 ≡ r2 →
  r1 ⊨{n,fs,ft} (es, σs) ≥ (et, σt) : Φ →
  r2 ⊨{n,fs,ft} (es, σs) ≥ (et, σt) : Φ.
Proof.
  revert r1 r2 n es σs et σt Φ. pcofix CIH.
  intros r1 r2 n es σs et σt Φ EQ SIM.
  pfold. punfold SIM.
  intros NT r_f WSAT. rewrite <-EQ in WSAT.
  specialize (SIM NT r_f WSAT) as [NOTS TE SIM].
  constructor; [done|..].
  { intros.
    destruct (TE _ TERM) as (vs' & σs' & r'' & STEP' & WSAT' & HΦ).
    naive_solver. }
  inversion SIM.
  - left. intros.
    specialize (STEP _ _ STEPT) as (es' & σs' & r' & idx' & STEP' & WSAT' & SIM').
    exists es', σs', r', idx'. do 2 (split; [done|]).
    pclearbot. right. eapply CIH; eauto.
  - econstructor 2; eauto.
    intros.
    destruct (CONT _ _ _ σs' σt' VRET WSAT1 STACK) as [idx' SIM'].
    exists idx'. pclearbot.
    right. eapply CIH; eauto.
Qed.

(* TODO: also allow rewriting the postcondition. *)
Global Instance sim_body_res_proper fs ft :
  Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (↔))
    (sim_local_body wsat vrel fs ft).
Proof.
  intros r1 r2 EQr n ? <- es ? <- σs ? <- et ? <- σt ? <- Φ ? <-.
  split; eapply sim_body_res_ext; done.
Qed.
Global Instance: Params (@sim_local_body) 5.

Lemma sim_body_frame' fs ft n (rf r: resUR) es σs et σt Φ :
  r ⊨{n,fs,ft} (es, σs) ≥ (et, σt) : Φ : Prop →
  ∀ (r': resUR), r' ≡ rf ⋅ r →
    r' ⊨{n,fs,ft} (es, σs) ≥ (et, σt) :
    (λ r' n' es' σs' et' σt', ∃ r0, r' = rf ⋅ r0 ∧ Φ r0 n' es' σs' et' σt').
Proof.
  revert n rf r es σs et σt Φ. pcofix CIH.
  intros n rf r0 es σs et σt Φ SIM r' EQ'.
  pfold. punfold SIM.
  intros NT r_f WSAT.
  rewrite ->EQ', ->(cmra_assoc r_f rf r0) in WSAT.
  specialize (SIM NT _ WSAT) as [SU TE ST]. split; [done|..].
  { intros. destruct (TE _ TERM) as (vs' & σs' & r2 & STEP' & WSAT' & POST).
    exists vs', σs', (rf ⋅ r2).
    split; last split; [done|by rewrite cmra_assoc|by exists r2]. }
  inversion ST.
  - constructor 1. intros.
    specialize (STEP _ _ STEPT) as (es' & σs' & r2 & idx' & STEPS' & WSAT' & SIM').
    exists es', σs', (rf ⋅ r2), idx'.
    split; last split; [done|by rewrite cmra_assoc|].
    pclearbot. right. by eapply CIH.
  - econstructor 2; eauto.
    { instantiate (1:= rf ⋅ rc). by rewrite -cmra_assoc (cmra_assoc r_f). }
    intros.
    specialize (CONT _ _ _ σs' σt' VRET) as [idx' SIM']; [|done|].
    { move : WSAT1. by rewrite 3!cmra_assoc. }
    exists idx'. pclearbot. right. eapply CIH; eauto. by rewrite cmra_assoc.
Qed.

Lemma sim_body_frame fs ft n (rf r: resUR) es σs et σt Φ :
  r ⊨{n,fs,ft} (es, σs) ≥ (et, σt) : Φ : Prop →
  rf ⋅ r ⊨{n,fs,ft} (es, σs) ≥ (et, σt) :
    (λ r' n' es' σs' et' σt', ∃ r0, r' = rf ⋅ r0 ∧ Φ r0 n' es' σs' et' σt').
Proof. intros. eapply sim_body_frame'; eauto. Qed.

Lemma sim_body_frame_core fs ft n (r: resUR) es σs et σt Φ :
  r ⊨{n,fs,ft}
    (es, σs) ≥ (et, σt)
  : (λ r' n' es' σs' et' σt', Φ (core r ⋅ r') n' es' σs' et' σt') →
  r ⊨{n,fs,ft} (es, σs) ≥ (et, σt) : Φ.
Proof.
  intros HH. rewrite -(cmra_core_l r).
  eapply sim_local_body_post_mono, sim_body_frame, HH.
  intros r' n' rs' σs' rt' σt' [r'' [-> HΦ]]. done.
Qed.

Lemma sim_body_val_elim fs ft r n vs σs vt σt Φ :
  r ⊨{n,fs,ft} ((Val vs), σs) ≥ ((Val vt), σt) : Φ →
  ∀ r_f (WSAT: wsat (r_f ⋅ r) σs σt),
  ∃ r', Φ r' n (ValR vs) σs (ValR vt) σt ∧ wsat (r_f ⋅ r') σs σt.
Proof.
  intros SIM r_f WSAT. punfold SIM.
  specialize (SIM (never_stuck_val fs vs σs) _ WSAT) as [ST TE STEPSS].
  specialize (TE (ValR vt) eq_refl)
    as (vs' & σs' & r' & STEP' & WSAT' & POST).
  exists r'.
  assert (σs' = σs ∧ vs' = vs) as [].
  { inversion STEP' as [x y Eq|x [] z STEP2] ; subst; simplify_eq.
    - have Eq2 := to_of_result vs'. rewrite -Eq /= in Eq2. by simplify_eq.
    - by apply result_tstep_stuck in STEP2. }
  subst σs' vs'. done.
Qed.
