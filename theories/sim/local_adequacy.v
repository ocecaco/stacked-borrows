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
Variable (wsat: A → state → state → Prop).
Variable (vrel: A → expr → expr → Prop).
Variable (fns fnt: fn_env).

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
                                (λ r _ vs _ vt _, vrel r (of_result vs) (of_result vt)))
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
                           (λ r _ vs _ vt _, vrel r (of_result vs) (of_result vt)))
    (KE_SRC: Ke_src = fill K_src e_src)
    (KE_TGT: Ke_tgt = fill K_tgt e_tgt)
    (WSAT: wsat (r_f ⋅ rc) σ_src σ_tgt)
  : sim_local_conf idx Ke_src σ_src Ke_tgt σ_tgt.

Lemma sim_local_conf_sim
      (FUNS: sim_local_funs wsat vrel fns fnt)
      (idx:nat) (e_src:expr) (σ_src:state) (e_tgt:expr) (σ_tgt:state)
      (SIM: sim_local_conf idx e_src σ_src e_tgt σ_tgt)
  : sim fns fnt idx (e_src, σ_src) (e_tgt, σ_tgt)
.
Proof.
  revert idx e_src σ_src e_tgt σ_tgt SIM. pcofix CIH. i.
  pfold. ii. inv SIM. punfold LOCAL. exploit LOCAL; eauto.
  { admit. (* never_stuck *) }
  clear LOCAL. intro LOCAL. inv LOCAL. econs.
  - ii. admit. (* stuck_fill_rev *)
  - guardH sim_local_body_stuck.
    s. i. apply fill_result in H. unfold terminal in H. des. subst. inv FRAMES. ss.
    exploit sim_local_body_terminal; eauto. i. des.
    esplits; eauto; ss.
    + rewrite to_of_result. esplits; eauto.
    + ii. clarify. admit. (* vrel, to_result. HAI: property of vrel *)
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

      exploit CONTINUATION; eauto.
      { admit. (* wsat assoc HAI: property of wsat *) }
      { admit. (* vrel #?  HAI: property of vrel *) }
      i. des.

      esplits.
      - left. eapply tc_rtc_l.
        + apply fill_tstep. instantiate (1 := σs'). instantiate (1 := EndCall vs').
          (* EndCallCtx *)
          clear -x.
          unguardH x. destruct x as [STEP|[_ EQ]].
          * by apply tc_rtc, (fill_tstep_tc _ [EndCallCtx]).
          * inversion EQ. econs.
        + (* EndCall step *)
          econs 1. eapply (head_step_fill_tstep).
          (* HAI: property of wsat and vrel *)
          admit.
      - right. apply CIH. econs; eauto.
        + rewrite fill_app. eauto.
        + rewrite fill_app. eauto.
        + admit. (* wsat after return HAI: property of wsat *)
                 (* TODO: extract from sim_body_end_call *)
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
      esplits.
      * left. eapply tc_rtc_l.
        { apply fill_tstep. eauto. }
        { econs. rewrite -fill_app. eapply (head_step_fill_tstep). econstructor.
          (* HAI: need to know more about fns and subst_l of el_src *)
          (* econstructor; eauto. *)
          admit. (* Call #[fid] has a step *)
        }
      * right. apply CIH. econs.
        { econs 2; eauto. i. instantiate (1 := mk_frame _ _ _). ss.
          destruct (CONT _ _ _ σ_src' σ_tgt' VRET).
          pclearbot. esplits; eauto.
        }
        { admit. (* sim_local_body for the call init HAI: I don't know what this is *) }
        { s. ss. }
        { s. rewrite -fill_app. eauto. }
        { s. admit. (* from wsat_assoc HAI: property of wsat *) }
Admitted.

End local.

Section prog.
Context {A: ucmraT}.
Variable (wsat: A → state → state → Prop).
Variable (vrel: A → expr → expr → Prop).
Variable (fns fnt: fn_env).

Lemma sim_prog_sim
      prog_src prog_tgt
      (FUNS: sim_local_funs wsat vrel prog_src prog_tgt)
  : behave_prog prog_tgt <1= behave_prog prog_src.
Proof.
  unfold behave_prog. eapply adequacy. eapply sim_local_conf_sim; eauto.
  econs; eauto; swap 2 4.
  - econs 1.
  - ss.
  - ss.
  - admit. (* sim_local_body for init_expr, init_state HAI: this should come from sim_local_funs of "main" *)
  - admit. (* wsat for init_state HAI: property of wsat *)
Admitted.

End prog.
