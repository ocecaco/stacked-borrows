From Paco Require Import paco.

From stbor.lang Require Import steps_wf.
From stbor.sim Require Import global.

Set Default Proof Using "Type".

(** Behaviors ----------------------------------------------------------------*)

Inductive behavior := | Term (v: value) | Stuck | Diverges.

Inductive behaviors
  (step: expr * config → expr * config → Prop)
  (cfg: expr * config) : behavior → Prop :=
| behaviors_term v
    (TERMINAL: to_result cfg.1 = Some (ValR v)) :
    behaviors step cfg (Term v)
| behaviors_stuck
    (NT: ¬ terminal cfg.1)
    (NS: ∀ cfg', ¬ step cfg cfg') :
    behaviors step cfg Stuck
(* | behaviors_diverges
    (DIV: diverges step cfg) :
    behaviors step cfg Diverges *)
| behaviors_step cfg' ov
    (STEP: step cfg cfg')
    (NEXT: behaviors step cfg' ov):
    behaviors step cfg ov
.

(* If c1 ->* c2 -b-> v then c1 -b-> v *)
Lemma rtc_step_behavior step c1 c2 v
  (STEPS: rtc step c1 c2) (BEH: behaviors step c2 v):
  behaviors step c1 v.
Proof.
  induction STEPS as [|c1 c2 c3 S1 S2 IH]; [done|]. specialize (IH BEH).
  econstructor 3; eauto.
Qed.

Lemma sim_adequacy (cfg_src cfg_tgt: expr * config)
  (WFS: Wf cfg_src.2) (WFT: Wf cfg_tgt.2) (NO_UB: no_UB cfg_src)
  (SIM: sim cfg_src cfg_tgt) :
  behaviors tstep cfg_tgt <1= behaviors tstep cfg_src.
Proof.
  intros ov BEH. revert cfg_src WFS WFT NO_UB SIM.
  induction BEH as [cfg_tgt(* |cfg_tgt *)|cfg_tgt v|cfg_tgt cfg_tgt' ov STEP BEH IH];
    intros cfg_src WFS WFT NO_UB SIM.
  - punfold SIM. destruct (SIM WFS WFT) as [? (* ? *) TERM ?]; [naive_solver|].
    destruct TERM as (eσ2 & TS & TERM' & VAL); [by eexists|].
    apply (rtc_step_behavior _ _ _ _ TS).
    constructor. by apply VAL.
  - punfold SIM. destruct (SIM WFS WFT) as [SU]; [naive_solver|].
    destruct SU as (eσ2 & TS' & IN & NR).
    + split; [by apply expr_terminal_False|].
      intros ???? PRIM. eapply (NS (e', σ')). econstructor; eauto.
    + apply (rtc_step_behavior _ _ _ _ TS').
      constructor 2; [by apply expr_terminal_False|].
      intros ? RED. inversion RED. by apply (NR _ _ _ _ PRIM).
  (* - punfold SIM. destruct (SIM WFS WFT SIM0) as (SU & DIV & ?); [naive_solver|].
    constructor. by apply DIV. *)
  - punfold SIM.
    destruct (SIM WFS WFT) as [SU (* DIV *) TERM TS]; [naive_solver|].
    destruct (TS cfg_tgt' STEP) as (eσ & STEP' & TS').
    eapply rtc_step_behavior; first by apply STEP'.
    eapply IH; simpl.
    + by apply (rtc_tstep_wf _ _ STEP').
    + by apply (tstep_wf _ _ STEP).
    + clear -STEP' NO_UB. induction STEP'. done.
      apply IHSTEP'. admit.
    + by inversion TS'.
Abort.
