From stbor Require Import simulation steps_wf.
From Paco Require Import paco.

(* TODO: what about divergence and stuckness? *)

Inductive behaviors
  (step: expr * state → expr * state → Prop)
  (cfg: expr * state) : val → Prop :=
| behaviors_term v
    (TERMINAL: terminal cfg.1)
    (EQV: sim_val_expr cfg.1 (of_val v)) :
    behaviors step cfg v
| behaviors_stuck v
    (NT: ¬ terminal cfg.1)
    (NS: ∀ cfg', ¬ step cfg cfg') :
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
  econstructor 3; eauto.
Qed.

Lemma sim_thread_adequacy (cfg_src cfg_tgt: expr * state)
  (WFS: Wf cfg_src.2) (WFT: Wf cfg_tgt.2)
  (SIM: sim_thread (sim_terminal (λ _ _, True)) cfg_src cfg_tgt) :
  ∀ v, behaviors thread_step cfg_tgt v → behaviors thread_step cfg_src v.
Proof.
  intros v BEH. revert cfg_src WFS WFT SIM.
  induction BEH as [cfg_tgt|cfg_tgt v|cfg_tgt cfg_tgt' v STEP BEH IH];
    intros cfg_src WFS WFT SIM.
  - punfold SIM.
    destruct (SIM WFS WFT) as [TERM ?].
    destruct (TERM TERMINAL) as (eσ2 & TS & TERM' & VAL).
    apply (rtc_step_behavior _ _ _ _ TS).
    constructor 1; [done|simpl]. etrans; eauto. by inversion VAL.
  - punfold SIM.
    destruct (SIM WFS WFT) as [TE [SU TS]].
    destruct SU as [eσ2 [TS' [IN NR]]].
    + split; [by apply expr_terminal_False|].
      intros ???? PRIM. eapply (NS (e', σ')). econstructor; eauto.
    + apply (rtc_step_behavior _ _ _ _ TS').
      constructor 2; [by apply expr_terminal_False|].
      intros ? RED. inversion RED. by apply (NR _ _ _ _ PRIM).
  - punfold SIM.
    destruct (SIM WFS WFT) as [? [SU TS]].
    destruct (TS cfg_tgt' STEP) as (eσ & STEP' & TS').
    eapply rtc_step_behavior; first by apply STEP'.
    apply IH; simpl.
    + by apply (rtc_thread_step_wf _ _ STEP').
    + by apply (thread_step_wf _ _ STEP).
    + by inversion TS'.
Qed.
