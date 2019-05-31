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
  (SIM: sim_thread (sim_terminal (λ _ _, True)) cfg_src cfg_tgt) :
  ∀ v, behaviors thread_step cfg_tgt v → behaviors thread_step cfg_src v.
Proof.
  intros v BEH. revert cfg_src WFS WFT SIM.
  induction BEH as [cfg_tgt|cfg_tgt cfg_tgt' v STEP BEH IH];
    intros cfg_src WFS WFT SIM.
  - punfold SIM.
    destruct (SIM WFS WFT) as [TERM ?].
    destruct (TERM TERMINAL) as (eσ2 & TS & TERM' & VAL).
    eapply (rtc_step_behavior _ _ eσ2).
    + by destruct cfg_src.
    + constructor; [done|simpl]. etrans; eauto. by inversion VAL.
  - punfold SIM.
    destruct (SIM WFS WFT) as [? SS].
    destruct (SS cfg_tgt' STEP) as (eσ & TS & SS').
    eapply rtc_step_behavior; first by apply TS.
    apply IH; simpl.
    + by apply (rtc_thread_step_wf _ _ TS).
    + by apply (thread_step_wf _ _ STEP).
    + by inversion SS'.
Qed.
