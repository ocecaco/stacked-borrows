From Coq Require Import Program.Equality Lia.
From Paco Require Import paco.

From stbor.lang Require Import steps_wf steps_inversion.
From stbor.sim Require Import behavior global local invariant sflib global_adequacy.

Set Default Proof Using "Type".

Lemma fill_step_inv_2
      fn K e1 σ1 e2 σ2
      (STEP: (fill (Λ:=bor_ectxi_lang fn) K e1, σ1) ~{fn}~> (e2, σ2)):
  (∃ e2', e2 = fill K e2' ∧ (e1, σ1) ~{fn}~> (e2', σ2)) ∨
  (∃ v, to_result e1 = Some v).
Proof.
  destruct (to_result e1) eqn:Eq1; [right; by eexists|left; by apply fill_tstep_inv].
Qed.

Section local.
Context {A: ucmraT}.
Variable (wsat esat: A → state → state → Prop).
Variable (vrel: A → expr → expr → Prop).
Variable (fns fnt: fn_env).

Hypothesis WSAT_PROPER: Proper ((≡) ==> (=) ==> (=) ==> iff) wsat.
Hypothesis VREL_RESULT:
  ∀ (r: A) (e1 e2: result), vrel r e1 e2 → to_result e1 = Some e2.
Hypothesis VREL_VAL :
  ∀ (r: A) (e1 e2: result),
  vrel r e1 e2 → ∃ v1 v2, e1 = ValR v1 ∧ e2 = ValR v2 ∧ vrel r (Val v1) (Val v2).
Hypothesis ENDCALL_RED:
  ∀ r σs σt (vs vt: value) es' σs',
  wsat r σs σt → (EndCall vs, σs) ~{fns}~> (es', σs') → reducible fnt (EndCall vt) σt.

Record frame: Type := mk_frame {
  rc: A;
  K_src: list (ectxi_language.ectx_item (bor_ectxi_lang fns));
  K_tgt: list (ectxi_language.ectx_item (bor_ectxi_lang fnt));
}.

(* TODO: move *)
Notation PRED := (A → nat → result → state → result → state → Prop)%type.

Inductive sim_local_frames:
  forall (r_f:A)
    (K_src: list (ectxi_language.ectx_item (bor_ectxi_lang fns)))
    (K_tgt: list (ectxi_language.ectx_item (bor_ectxi_lang fnt)))
    (frames:list frame),
    Prop :=
| sim_local_frames_nil
    r_f
  : sim_local_frames r_f nil nil nil
| sim_local_frames_cons
    r_f K_f_src K_f_tgt
    frame frames
    (FRAMES: sim_local_frames r_f K_f_src K_f_tgt frames)
    (CONTINUATION:
       ∀ r' v_src v_tgt σ_src' σ_tgt'
         (* For any new resource r' that are compatible with
             our local resource r and have world satisfaction *)
         (WSAT' : wsat (r_f ⋅ (frame.(rc) ⋅ r')) σ_src' σ_tgt')
         (* and the returned values are related w.r.t. (r ⋅ r' ⋅ r_f) *)
         (VRET  : vrel r' (Val v_src) (Val v_tgt)),
         ∃ idx', sim_local_body wsat vrel fns fnt
                                (frame.(rc) ⋅ r') idx'
                                (fill frame.(K_src) (Val v_src)) σ_src'
                                (fill frame.(K_tgt) (Val v_tgt)) σ_tgt'
                                (λ r _ vs σs vt σt, esat r σs σt ∧ vrel r (of_result vs) (of_result vt)))
  : sim_local_frames
      (r_f ⋅ frame.(rc))
      (EndCallCtx :: frame.(K_src) ++ K_f_src)
      (EndCallCtx :: frame.(K_tgt) ++ K_f_tgt)
      (frame :: frames)
.

Inductive sim_local_conf:
  forall (idx:nat) (e_src:expr) (σ_src:state) (e_tgt:expr) (σ_tgt:state), Prop :=
| sim_local_conf_intro
    r_f K_src K_tgt frames
    rc idx e_src σ_src e_tgt σ_tgt
    Ke_src Ke_tgt
    (FRAMES: sim_local_frames r_f K_src K_tgt frames)
    (LOCAL: sim_local_body wsat vrel fns fnt rc idx e_src σ_src e_tgt σ_tgt
                           (λ r _ vs σs vt σt, esat r σs σt ∧ vrel r (of_result vs) (of_result vt)))
    (KE_SRC: Ke_src = fill K_src e_src)
    (KE_TGT: Ke_tgt = fill K_tgt e_tgt)
    (WSAT: wsat (r_f ⋅ rc) σ_src σ_tgt)
  : sim_local_conf idx Ke_src σ_src Ke_tgt σ_tgt.

Lemma sim_local_conf_sim
      (FUNS: sim_local_funs wsat vrel fns fnt esat)
      (idx:nat) (e_src:expr) (σ_src:state) (e_tgt:expr) (σ_tgt:state)
      (SIM: sim_local_conf idx e_src σ_src e_tgt σ_tgt)
  : sim fns fnt idx (e_src, σ_src) (e_tgt, σ_tgt)
.
Proof.
  revert idx e_src σ_src e_tgt σ_tgt SIM. pcofix CIH. i.
  pfold. ii. inv SIM. punfold LOCAL. exploit LOCAL; eauto.
  { eapply never_stuck_fill_inv; eauto. }
  clear LOCAL. intro LOCAL. inv LOCAL. econs.
  - ii. simpl. des; last (right; by eapply tstep_reducible_fill).
    destruct sim_local_body_stuck as [vt Eqvt].
    rewrite -(of_to_result _ _ Eqvt).
    destruct (sim_local_body_terminal _ Eqvt)
      as (vs' & σs' & r' & idx' & SS' & WSAT' & ESAT' & VREL).
    have STEPK: (fill (Λ:=bor_ectxi_lang fns) K_src0 e_src0, σ_src)
              ~{fns}~>* (fill (Λ:=bor_ectxi_lang fns) K_src0 vs', σs').
    { apply fill_tstep_rtc. destruct SS' as [|[? Eq]].
      by apply tc_rtc. clear -Eq. simplify_eq. constructor. }
    have NT3:= never_stuck_tstep_rtc _ _ _ _ _ STEPK NEVER_STUCK.
    clear -STEPK NT3 FRAMES WSAT' VREL ENDCALL_RED VREL_VAL.
    inversion FRAMES. { left. rewrite to_of_result. by eexists. }
    right. subst K_src0 K_tgt0.
    move : NT3. simpl. intros NT3.
    destruct (NT3 (fill (K_src frame0 ++ K_f_src) (EndCall vs')) σs')
      as [[? TERM]|RED]; [constructor|..].
    { by rewrite fill_not_result in TERM. }
    apply tstep_reducible_fill_inv in RED; [|done].
    apply tstep_reducible_fill.
    destruct RED as [e2 [σ2 Eq2]].
    apply VREL_VAL in VREL as (v1 & v2 & ? & ? & ?). subst vs' vt.
    move : Eq2. eapply ENDCALL_RED; eauto.
  - guardH sim_local_body_stuck.
    s. i. apply fill_result in H. unfold terminal in H. des. subst. inv FRAMES. ss.
    exploit sim_local_body_terminal; eauto. i. des.
    esplits; eauto; ss.
    + rewrite to_of_result. esplits; eauto.
    + ii. clarify. eapply VREL_RESULT; eauto.
  - guardH sim_local_body_stuck.
    i. destruct eσ2_tgt as [e2_tgt σ2_tgt].

    exploit fill_step_inv_2; eauto. i. des; cycle 1.
    { (* return *)
      exploit sim_local_body_terminal; eauto. i. des.

      inv FRAMES; ss.
      { exfalso. apply result_tstep_stuck in H. naive_solver. }
      apply fill_step_inv_2 in H. des; ss. subst.

      apply tstep_end_call_inv in H0; cycle 1.
      { unfold terminal. rewrite x0. eauto. }
      des. subst.
      destruct (VREL_VAL _ _ _ x3) as (vs1 & v1 & Eqvs1 & Eqv1 & VREL1).

      exploit CONTINUATION; eauto.
      { rewrite cmra_assoc; eauto. }
      i. des.

      have STEPK: (fill (Λ:= bor_ectxi_lang fns)
                        (EndCallCtx :: K_src frame0 ++ K_f_src) e_src0, σ_src)
            ~{fns}~>* (fill (Λ:= bor_ectxi_lang fns)
                        (EndCallCtx :: K_src frame0 ++ K_f_src) vs', σs').
      { apply fill_tstep_rtc. destruct x as [|[? Eq]].
        by apply tc_rtc. clear -Eq. simplify_eq. constructor. }
      have NT3 := never_stuck_tstep_rtc _ _ _ _ _ STEPK NEVER_STUCK.
      edestruct NT3 as [[? TERM]|[es [σs1 STEP1]]].
      { constructor 1. } { by rewrite /= fill_not_result in TERM. }

      have Eqes: es = fill (K_src frame0 ++ K_f_src) (Val vs1).
      { rewrite /= in STEP1.
        apply fill_tstep_inv in STEP1 as [e2' [Eq2' STEP2']]; [|done]. subst es.
        f_equal.
        apply tstep_end_call_inv in STEP2' as [v3 [Eq3 [Eq4 ?]]];
          [|rewrite to_of_result; by eexists].
        rewrite Eq4. rewrite Eqvs1 /= in Eq3. by inversion Eq3. } subst es.

      esplits.
      - left. eapply tc_rtc_l.
        + apply fill_tstep_rtc. instantiate (1 := σs'). instantiate (1 := EndCall vs').
          (* EndCallCtx *)
          clear -x.
          unguardH x. destruct x as [STEP|[_ EQ]].
          * by apply tc_rtc, (fill_tstep_tc _ [EndCallCtx]).
          * inversion EQ. econs.
        + (* EndCall step *)
          apply tc_once; eauto.
      - right. apply CIH. econs; eauto; cycle 1.
        + rewrite fill_app. eauto.
        + rewrite fill_app. eauto.
        + admit. (* wsat after return HAI: property of wsat *)
                 (* TODO: extract from sim_body_end_call *)
        + admit.
    }

    subst. clear H. inv sim_local_body_step.
    + (* step *)
      exploit STEP; eauto. intros (es' & σs' & r' & idx' & STEP' & WSAT' & SIM').
      pclearbot. esplits; eauto.
      * instantiate (1 := (fill K_src0 es', σs')). revert sim_local_body_stuck.
        des; [left|right]; esplits; eauto.
        { apply fill_tstep_tc. ss. }
        { inv STEP'0. ss. }
      * right. apply CIH. econs; eauto.
    + (* call *)
      exploit fill_step_inv_2; eauto. i. des; ss.
      exploit tstep_call_inv; try exact x2; eauto. i. des. subst.
      destruct (FUNS _ _ x3) as ([xls ebs HCss] & Eqfs & Eql & SIMf).
      destruct (subst_l_is_Some xls el_src ebs) as [ess Eqss].
      { by rewrite (Forall2_length _ _ _ VREL) -(subst_l_is_Some_length _ _ _ _ x4). }
      specialize (SIMf _ _ _ _ _ σ1_src σ_tgt VSRC VTGT VREL Eqss x4) as [idx2 SIMf].
      esplits.
      * left. eapply tc_rtc_l.
        { apply fill_tstep_rtc. eauto. }
        { econs. rewrite -fill_app. eapply (head_step_fill_tstep).
          econs; econs; eauto. }
      * right. apply CIH. econs.
        { econs 2; eauto. i. instantiate (1 := mk_frame _ _ _). ss.
          destruct (CONT _ _ _ σ_src' σ_tgt' VRET).
          pclearbot. esplits; eauto.
        }
        { eauto. }
        { s. ss. }
        { s. rewrite -fill_app. eauto. }
        { s. rewrite -cmra_assoc; eauto. }
Admitted.

End local.

Section prog.
Context {A: ucmraT}.
Variable (wsat esat: A → state → state → Prop).
Variable (vrel: A → expr → expr → Prop).
Variable (fns fnt: fn_env).

Lemma sim_prog_sim
      prog_src `{NSD: ∀ e σ, Decision (never_stuck prog_src e σ)}
      prog_tgt
      (FUNS: sim_local_funs wsat vrel prog_src prog_tgt esat)
  : behave_prog prog_tgt <1= behave_prog prog_src.
Proof.
  unfold behave_prog. eapply adequacy.
  - apply _.
  - eapply sim_local_conf_sim; eauto.
    econs; eauto; swap 2 4.
    + econs 1.
    + ss.
    + ss.
    + admit. (* sim_local_body for init_expr, init_state HAI: this should come from sim_local_funs of "main" *)
    + admit. (* wsat for init_state HAI: property of wsat *)
  - admit.
  - admit.
Admitted.

End prog.
