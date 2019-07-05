From Coq Require Import Program.Equality Lia.
From Paco Require Import paco.

From stbor.lang Require Import steps_wf steps_inversion.
From stbor.sim Require Import sflib behavior global local.
From stbor.sim Require Import invariant refl_step.

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
Variable (fns fnt: fn_env).

Record frame: Type := mk_frame {
  rc: resUR;
  callids: list nat;
  K_src: list (ectxi_language.ectx_item (bor_ectxi_lang fns));
  K_tgt: list (ectxi_language.ectx_item (bor_ectxi_lang fnt));
}.

Inductive sim_local_frames:
  forall (r_f: resUR)
    (callids: list nat)
    (K_src: list (ectxi_language.ectx_item (bor_ectxi_lang fns)))
    (K_tgt: list (ectxi_language.ectx_item (bor_ectxi_lang fnt)))
    (frames:list frame),
    Prop :=
| sim_local_frames_nil
    r_f
  : sim_local_frames r_f nil nil nil nil
| sim_local_frames_cons
    r_f cids K_f_src K_f_tgt
    frame frames
    (FRAMES: sim_local_frames r_f cids K_f_src K_f_tgt frames)
    (CONTINUATION:
       ∀ r' v_src v_tgt σ_src' σ_tgt'
         (* For any new resource r' that are compatible with
             our local resource r and have world satisfaction *)
         (WSAT' : wsat (r_f ⋅ (frame.(rc) ⋅ r')) σ_src' σ_tgt')
         (* and the returned values are related w.r.t. (r ⋅ r' ⋅ r_f) *)
         (VRET  : vrel_expr r' (Val v_src) (Val v_tgt))
         (CIDS: σ_tgt'.(scs) = frame.(callids)),
         ∃ idx', sim_local_body wsat vrel_expr fns fnt
                                (frame.(rc) ⋅ r') idx'
                                (fill frame.(K_src) (Val v_src)) σ_src'
                                (fill frame.(K_tgt) (Val v_tgt)) σ_tgt'
                                (λ r _ vs σs vt σt,
                                  (∃ c, σt.(scs) = c :: cids) ∧
                                  end_call_sat r σs σt ∧
                                  vrel_expr r (of_result vs) (of_result vt)))
  : sim_local_frames
      (r_f ⋅ frame.(rc))
      frame.(callids)
      (EndCallCtx :: frame.(K_src) ++ K_f_src)
      (EndCallCtx :: frame.(K_tgt) ++ K_f_tgt)
      (frame :: frames)
.

Inductive sim_local_conf:
  forall (idx:nat) (e_src:expr) (σ_src:state) (e_tgt:expr) (σ_tgt:state), Prop :=
| sim_local_conf_intro
    r_f cids K_src K_tgt frames
    rc idx e_src σ_src e_tgt σ_tgt
    Ke_src Ke_tgt
    (FRAMES: sim_local_frames r_f cids K_src K_tgt frames)
    (LOCAL: sim_local_body wsat vrel_expr fns fnt rc idx e_src σ_src e_tgt σ_tgt
                           (λ r _ vs σs vt σt,
                              (∃ c, σt.(scs) = c :: cids) ∧
                              end_call_sat r σs σt ∧
                              vrel_expr r (of_result vs) (of_result vt)))
    (KE_SRC: Ke_src = fill K_src e_src)
    (KE_TGT: Ke_tgt = fill K_tgt e_tgt)
    (WSAT: wsat (r_f ⋅ rc) σ_src σ_tgt)
  : sim_local_conf idx Ke_src σ_src Ke_tgt σ_tgt.

Lemma sim_local_conf_sim
      (FUNS: sim_local_funs wsat vrel_expr fns fnt end_call_sat)
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
      as (vs' & σs' & r' & idx' & SS' & WSAT' & CALLIDS & ESAT' & VREL).
    have STEPK: (fill (Λ:=bor_ectxi_lang fns) K_src0 e_src0, σ_src)
              ~{fns}~>* (fill (Λ:=bor_ectxi_lang fns) K_src0 vs', σs').
    { apply fill_tstep_rtc. destruct SS' as [|[? Eq]].
      by apply tc_rtc. clear -Eq. simplify_eq. constructor. }
    have NT3:= never_stuck_tstep_rtc _ _ _ _ _ STEPK NEVER_STUCK.
    clear -STEPK NT3 FRAMES WSAT' VREL.
    inversion FRAMES. { left. rewrite to_of_result. by eexists. }
    right. subst K_src0 K_tgt0.
    move : NT3. simpl. intros NT3.
    destruct (NT3 (fill (K_src frame0 ++ K_f_src) (EndCall vs')) σs')
      as [[? TERM]|RED]; [constructor|..].
    { by rewrite fill_not_result in TERM. }
    apply tstep_reducible_fill_inv in RED; [|done].
    apply tstep_reducible_fill.
    destruct RED as [e2 [σ2 Eq2]].
    apply vrel_expr_result in VREL as (v1 & v2 & ? & ? & ?). subst vs' vt.
    move : Eq2. eapply end_call_tstep_src_tgt; eauto.
  - guardH sim_local_body_stuck.
    s. i. apply fill_result in H. unfold terminal in H. des. subst. inv FRAMES. ss.
    exploit sim_local_body_terminal; eauto. i. des.
    esplits; eauto; ss.
    + rewrite to_of_result. esplits; eauto.
    + ii. clarify. eapply vrel_expr_to_result; eauto.
  - guardH sim_local_body_stuck.
    i. destruct eσ2_tgt as [e2_tgt σ2_tgt].

    exploit fill_step_inv_2; eauto. i. des; cycle 1.
    { (* return *)
      exploit sim_local_body_terminal; eauto. i. des.

      inv FRAMES; ss.
      { exfalso. apply result_tstep_stuck in H. naive_solver. }

      (* Simulatin EndCall *)
      rename σ_tgt into σt. rename σs' into σs.
      destruct (vrel_expr_result _ _ _ x4) as (vs1 & vt1 & Eqvs1 & Eqv1 & VREL1).
      simplify_eq. have VR: vrel r' vs1 vt1 by apply vrel_expr_vrel.

      set Φ : resUR → nat → result → state → result → state → Prop :=
        λ r2 _ vs2 σs2 vt2 σt2, vrel_expr r2 vs2 vt2 ∧
          ∃ c1 c2 cids1 cids2, σs.(scs) = c1 :: cids1 ∧
            σt.(scs) = c2 :: cids2 ∧
            σs2 = mkState σs.(shp) σs.(sst) cids1 σs.(snp) σs.(snc) ∧
            σt2 = mkState σt.(shp) σt.(sst) cids2 σt.(snp) σt.(snc) ∧
            r2 = ((r'.(rtm),
                    match (r'.(rcm) !! c2) with
                    | Some (Cinl (Excl T)) => <[c2 := to_callStateR csPub]> r'.(rcm)
                    | _ => r'.(rcm)
                    end), r'.(rlm)).
      have SIMEND : r' ⊨{idx',fns,fnt} (EndCall vs1, σs) ≥ (EndCall vt1, σt) : Φ.
      { apply sim_body_end_call; auto.
        clear. intros. rewrite /Φ. naive_solver. }

      have NONE : to_result (EndCall e_tgt0) = None. by done.
      destruct (fill_tstep_inv _ _ _ _ _ _ NONE H) as [et2 [? STEPT2]].
      subst e2_tgt.

      have STEPK: (fill (Λ:= bor_ectxi_lang fns)
                        (EndCallCtx :: K_src frame0 ++ K_f_src) e_src0, σ_src)
            ~{fns}~>* (fill (Λ:= bor_ectxi_lang fns)
                        (EndCallCtx :: K_src frame0 ++ K_f_src) vs1, σs).
      { apply fill_tstep_rtc. destruct x as [|[? Eq]].
        by apply tc_rtc. clear -Eq. simplify_eq. constructor. }
      have NT3 := never_stuck_tstep_rtc _ _ _ _ _ STEPK NEVER_STUCK.
      rewrite /= in NT3.
      have NT4 := never_stuck_fill_inv _ _ _ _ NT3.
      rewrite -(of_to_result _ _ x0) in STEPT2.
      destruct (sim_body_end_call_elim' _ _ _ _ _ _ _ _ _ SIMEND _ _ _ x1 NT4 STEPT2)
        as (r2 & idx2 & σs2 & STEPS & ? & HΦ2 & WSAT2). subst et2.

      exploit (CONTINUATION r2).
      { rewrite cmra_assoc; eauto. }
      { apply HΦ2. }
      { exploit tstep_end_call_inv; try exact STEPT2; eauto. i. des. subst. ss.
        rewrite x2 in x7. inv x7. ss.
      }
      intros [idx3 SIMFR]. rename σ2_tgt into σt2.
      do 2 eexists. split.
      - left. apply fill_tstep_tc. eapply tc_rtc_l; [|apply STEPS].
        apply (fill_tstep_rtc _ [EndCallCtx]).
        clear -x. destruct x as [|[]]. by apply tc_rtc. simplify_eq; constructor.

      - right. apply CIH. econs; eauto.
        + rewrite fill_app. eauto.
        + rewrite fill_app. eauto.
        + rewrite <-cmra_assoc in WSAT2; eauto.
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
        { econs 2; eauto. i. instantiate (1 := mk_frame _ _ _ _). ss.
          destruct (CONT _ _ _ σ_src' σ_tgt' VRET).
          { rewrite CIDS. eauto. }
          pclearbot. esplits; eauto.
        }
        { eapply sim_local_body_post_mono; [|apply SIMf]. simpl. naive_solver. }
        { done. }
        { s. rewrite -fill_app. eauto. }
        { ss. rewrite -cmra_assoc; eauto. }
Qed.

End local.
