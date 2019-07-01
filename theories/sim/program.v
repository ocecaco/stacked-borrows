From stbor.lang Require Import steps_wf steps_inversion.
From stbor.sim Require Import sflib behavior global local invariant global_adequacy local_adequacy one_step.

Set Default Proof Using "Type".

Lemma sim_prog_sim
      prog_src `{NSD: ∀ e σ, Decision (never_stuck prog_src e σ)}
      prog_tgt
      (FUNS: sim_local_funs wsat vrel_expr prog_src prog_tgt end_call_sat)
      (MAINT: ∃ ebt HCt, prog_tgt !! "main" = Some (@FunV [] ebt HCt))
  : behave_prog prog_tgt <1= behave_prog prog_src.
Proof.
  destruct MAINT as (ebt & HCt & Eqt).
  destruct (FUNS _ _ Eqt) as ([xls ebs HCs] & Eqs & Eql & SIMf).
  apply nil_length_inv in Eql. subst xls.
  specialize (SIMf ε ebs ebt [] [] init_state init_state) as [idx SIM]; [done..|].
  unfold behave_prog. eapply (adequacy _ _ idx); [apply _| |by apply wf_init_state..].
  eapply sim_local_conf_sim; eauto.
  econs; swap 2 4.
  - econs 1.
  - ss.
  - ss.
  - eapply (sim_body_step_over_call _ _ [] [] init_res ε _ _ [] [] ebt ebt [] HCt);
      [done..|].
    intros r' vs vt σs' σt' VREL'.
    admit.
    (* eapply (sim_body_step_into_call _ _ _ _ _ [] ebs HCs [] ebs [] ebt HCt [] ebt);
      [done..|].
    eapply (sim_body_bind _ _ _ _ [EndCallCtx] [EndCallCtx] (InitCall ebs) (InitCall ebt)).
    eapply sim_local_body_post_mono; [|exact SIM].
    clear SIM. simpl.
    intros r1 idx1 vs σs vt σt [ESAT (v1 & v2 & Eq1 & Eq2 & VREL)].
    rewrite Eq1 Eq2. by apply sim_body_end_call. *)
  - instantiate (1:=ε). rewrite right_id left_id. apply wsat_init_state.
Qed.
