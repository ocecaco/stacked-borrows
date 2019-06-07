From Paco Require Import paco.

From stbor Require Import simulation.

(* If c1 ->* c2 -b-> v then c1 -b-> v *)
Lemma rtc_step_behavior step c1 c2 v
  (STEPS: rtc step c1 c2) (BEH: behaviors step c2 v):
  behaviors step c1 v.
Proof.
  induction STEPS as [|c1 c2 c3 S1 S2 IH]; [done|]. specialize (IH BEH).
  econstructor 4; eauto.
Qed.

Lemma sim_adequacy {A: Type} Φ (sim_mem: A → state → state → Prop)
  (σG: A) (cfg_src cfg_tgt: expr * state)
  (WFS: Wf cfg_src.2) (WFT: Wf cfg_tgt.2)
  (SIM0: sim_state sim_mem σG cfg_src.2 cfg_tgt.2)
  (NO_UB: ∀ cfg', cfg_src ~t~>* cfg' → ¬ stuck cfg'.1 cfg'.2)
  (SIM: @sim A Φ sim_mem σG cfg_src cfg_tgt) :
  behaviors tstep cfg_tgt <1= behaviors tstep cfg_src.
Proof.
  intros ov BEH. revert σG cfg_src WFS WFT SIM0 NO_UB SIM.
  induction BEH as [cfg_tgt|cfg_tgt|cfg_tgt v|cfg_tgt cfg_tgt' ov STEP BEH IH];
    intros σG cfg_src WFS WFT SIM0 NO_UB SIM.
  - punfold SIM. destruct (SIM WFS WFT SIM0) as (? & ? & TERM & ?); [naive_solver|].
    destruct TERM as (eσ2 & σG' & TS & TERM' & VAL); [by eexists|].
    apply (rtc_step_behavior _ _ _ _ TS).
    constructor. by apply VAL.
  - punfold SIM. destruct (SIM WFS WFT SIM0) as (SU & DIV & ?); [naive_solver|].
    destruct SU as (eσ2 & TS' & IN & NR).
    + split; [by apply expr_terminal_False|].
      intros ???? PRIM. eapply (NS (e', σ')). econstructor; eauto.
    + apply (rtc_step_behavior _ _ _ _ TS').
      constructor 2; [by apply expr_terminal_False|].
      intros ? RED. inversion RED. by apply (NR _ _ _ _ PRIM).
  - punfold SIM. destruct (SIM WFS WFT SIM0) as (SU & DIV & ?); [naive_solver|].
    constructor. by apply DIV.
  - punfold SIM.
    destruct (SIM WFS WFT SIM0) as (SU & DIV & TERM & TS); [naive_solver|].
    destruct (TS cfg_tgt' STEP) as (eσ & σG' & STEP' & SS & HΦ & TS').
    eapply rtc_step_behavior; first by apply STEP'.
    eapply IH; simpl.
    + by apply (rtc_tstep_wf _ _ STEP').
    + by apply (tstep_wf _ _ STEP).
    + eauto.
    + intros cfg' S'. apply NO_UB. by etrans.
    + by inversion TS'.
Qed.
