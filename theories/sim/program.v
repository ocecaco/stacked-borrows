From stbor.lang Require Import steps_wf steps_inversion.
From stbor.sim Require Import sflib behavior global local invariant global_adequacy local_adequacy one_step.

Set Default Proof Using "Type".

Lemma sim_prog_sim
      prog_src
      prog_tgt
      `{NSD: ∀ e σ, never_stuck prog_src e σ \/
                    exists e' σ', (e, σ) ~{prog_src}~>* (e', σ') /\
                             ~ terminal e' /\
                             ~ reducible prog_src e' σ'}
      (FUNS: sim_local_funs wsat vrel_expr prog_src prog_tgt end_call_sat)
      (MAINT: ∃ ebt HCt, prog_tgt !! "main" = Some (@FunV [] ebt HCt))
  : behave_prog prog_tgt <1= behave_prog prog_src.
Proof.
  destruct MAINT as (ebt & HCt & Eqt).
  destruct (FUNS _ _ Eqt) as ([xls ebs HCs] & Eqs & Eql & SIMf).
  apply nil_length_inv in Eql. subst xls.
  specialize (SIMf ε ebs ebt [] [] init_state init_state) as [idx SIM]; [done..|].
  unfold behave_prog. eapply (adequacy _ _ idx); [apply NSD| |by apply wf_init_state..].
  eapply sim_local_conf_sim; eauto.
  econs; swap 2 4.
  - econs 1.
  - ss.
  - ss.
  - eapply (sim_body_step_over_call _ _ [] [] init_res ε _ _ [] [] ebt ebt [] );
      [done..|].
    intros. simpl. exists 1%nat.
    apply (sim_body_result _ _ _ _ (ValR vs) (ValR vt)).
    intros VALID.
    have ?: vrel_expr (init_res ⋅ r') (of_result #vs) (of_result #vt).
    { do 2 eexists. do 2 (split; [done|]).
      eapply vrel_mono; [done|apply cmra_included_r|done]. }
    split; last split; last split; [done|..|done].
    { exists O. by rewrite -STACK. }
    rewrite /end_call_sat -STACK.
    intros c Eq. simpl in Eq. simplify_eq.
    have HL: (init_res ⋅ r').2 !! 0%nat ≡ Some (to_callStateR csPub).
    { apply cmap_lookup_op_l_equiv_pub; [apply VALID|].
      by rewrite /= lookup_singleton. }
    split. { destruct ((init_res ⋅ r').2 !! 0%nat). by eexists. by inversion HL. }
    intros r_f VALIDf T HL2. exfalso.
    move : HL2. rewrite lookup_op HL. apply callStateR_exclusive_2.
  - instantiate (1:=ε). rewrite right_id left_id. apply wsat_init_state.
Qed.
