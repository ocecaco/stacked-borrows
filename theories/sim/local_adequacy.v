From Coq Require Import Program.Equality Lia.
From Paco Require Import paco.

From stbor.lang Require Import steps_wf.
From stbor.sim Require Import behavior global local invariant sflib global_adequacy.

Set Default Proof Using "Type".

Lemma fill_step_rev
      fn K e1 σ1 e2 σ2
      (STEP: (fill (Λ:=bor_ectxi_lang fn) K e1, σ1) ~{fn}~> (e2, σ2)):
  (exists e2', e2 = fill K e2' /\ (e1, σ1) ~{fn}~> (e2', σ2)) \/
  (exists v, to_result e1 = Some v).
Proof.
Admitted.

Lemma fill_step
      fn K e1 σ1 e2 σ2
      (STEP: (e1, σ1) ~{fn}~> (e2, σ2)):
  (fill (Λ:=bor_ectxi_lang fn) K e1, σ1) ~{fn}~> (fill K e2, σ2).
Proof.
Admitted.

Lemma fill_steps
      fn K e1 σ1 e2 σ2
      (STEP: (e1, σ1) ~{fn}~>* (e2, σ2)):
  (fill (Λ:=bor_ectxi_lang fn) K e1, σ1) ~{fn}~>* (fill K e2, σ2).
Proof.
Admitted.

Lemma fill_stepp
      fn K e1 σ1 e2 σ2
      (STEP: (e1, σ1) ~{fn}~>+ (e2, σ2)):
  (fill (Λ:=bor_ectxi_lang fn) K e1, σ1) ~{fn}~>+ (fill K e2, σ2).
Proof.
Admitted.

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
      (frame.(K_src) ++ K_f_src)
      (frame.(K_tgt) ++ K_f_tgt)
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
  - ii. eapply sim_local_body_stuck. admit. (* stuck_fill_rev *)
  - s. i. subst. apply fill_result in H. des. unfold terminal in H. des. subst. ss.
    exploit sim_local_body_terminal; eauto. i. des.
    clear NEVER_STUCK WSAT.
    clear sim_local_body_stuck sim_local_body_terminal sim_local_body_step.
    assert (VS': to_result vs' = Some x) by admit.
    induction FRAMES; ss.
    { esplits; eauto; ss. ii. clarify. }
    admit. (* global sim should have generalized index *) 
  - i. destruct eσ2_tgt as [e2_tgt σ2_tgt].
    exploit fill_step_rev; eauto. i. des; cycle 1.
    { (* return *)
      admit. (* similar to the above case *)
    }
    subst. clear H. inv sim_local_body_step.
    + (* step *)
      exploit STEP; eauto. intros (es' & σs' & r' & idx' & STEP' & WSAT' & SIM').
      pclearbot. esplits; eauto.
      * instantiate (1 := (fill K_src0 es', σs')).
        des; [left|right]; esplits; eauto.
        { apply fill_stepp. ss. }
        { inv STEP'0. ss. }
      * right. apply CIH. econs; eauto.
    + (* call *)
      esplits.
      * left. eapply tc_rtc_l.
        { apply fill_steps. eauto. }
        { instantiate (1 := (fill K_src0 (fill Ks _), _)).
          admit. (* call has a matching step *)
        }
      * right. apply CIH. econs.
        { econs 2; eauto. i. instantiate (1 := mk_frame _ _ _). ss.
          destruct (CONT _ _ _ _ _ WSAT' VRET).
          pclearbot. esplits; eauto.
        }
        { admit. (* sim_local_body for the call init *) }
        { s. rewrite fill_app. ss. }
        { s. rewrite fill_app. f_equal. admit. (* call ctx *) }
        { s. admit. (* from WSAT0, x1 *) }
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
  - admit. (* sim_local_body for init_expr, init_state *)
  - admit. (* wsat for init_state *)
Admitted.

End prog.
