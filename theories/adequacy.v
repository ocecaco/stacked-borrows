From stbor Require Import simulation steps_wf.
From Paco Require Import paco.

Inductive behaviors
  (step: expr * state → expr * state → Prop)
  (cfg: expr * state) : val → Prop :=
| behaviors_term v
    (TERMINAL: terminal cfg.1)
    (EQV: sim_val_expr cfg.1 (of_val v)) :
    behaviors step cfg v
| behaviors_step cfg' v
    (STEP: step cfg cfg')
    (NEXT: behaviors step cfg' v):
    behaviors step cfg v
.

(* If c1 ->* c2 -b-> v then c1 -b-> v *)
Lemma rtc_step_behavior step c1 c2 v
  (STEPS: rtc step c1 c2) (BEH: behaviors step c2 v):
  behaviors step c1 v.
Proof.
  induction STEPS as [|c1 c2 c3 S1 S2 IH]; [done|]. specialize (IH BEH).
  econstructor 2; eauto.
Qed.

Lemma sim_thread_adequacy (cfg_src cfg_tgt: expr * state)
  (WFS: Wf cfg_src.2) (WFT: Wf cfg_tgt.2)
  (STATE: sim_state cfg_src.2 cfg_tgt.2)
  (SIM: sim_thread sim_val_expr cfg_src.1 cfg_src.2 cfg_tgt.1 cfg_tgt.2) :
  ∀ v, behaviors thread_step cfg_tgt v → behaviors thread_step cfg_src v.
Proof.
  intros v BEH. revert cfg_src WFS WFT STATE SIM.
  induction BEH as [cfg_tgt|cfg_tgt cfg_tgt' v STEP BEH IH];
    intros cfg_src WFS WFT STATE SIM.
  - punfold SIM.
    destruct (SIM WFS WFT STATE) as [TERM ?].
    destruct (TERM TERMINAL) as (e2 & σ2 & TS & STATE' & TERM' & VAL).
    eapply (rtc_step_behavior _ _ (e2, σ2)).
    + by destruct cfg_src.
    + constructor; [done|simpl]. etrans; eauto.
  - punfold SIM.
    destruct (SIM WFS WFT STATE) as [? SS].
    destruct cfg_src as [e σ]. destruct cfg_tgt' as [e' σ'].
    destruct (SS e' σ') as (e2 & σ2 & TS & STATE' & SS').
    { clear -STEP. by destruct cfg_tgt. }
    simpl in TS. eapply rtc_step_behavior; first by apply TS.
    apply IH; simpl.
    + by apply (rtc_thread_step_wf _ _ TS).
    + by apply (thread_step_wf _ _ STEP).
    + done.
    + by inversion SS'.
Qed.
