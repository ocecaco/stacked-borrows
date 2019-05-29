
(*====== The following definitions consider concurrency. Unused for now ======*)
(* THIS DOES NOT BUILD *)

(** Configuration (threadpool) steps *)
(* This duplicates iris.program_logic.language in order to expose a thread id *)
(* Inductive step ρ1 tid ev ρ2 : Prop :=
| StepAtomic e1 σ1 e2 σ2 efs t1 t2 :
   ρ1 = (t1 ++ e1 :: t2, σ1) →
   ρ2 = (t1 ++ e2 :: t2 ++ efs, σ2) →
   thread_step (e1, σ1) ev (e2, σ2) efs →
   tid = length t1 →
   step ρ1 tid ev ρ2.

(* τ-step has no external observation and ignore tid. *)
Inductive τstep ρ1 ρ2 : Prop :=
| CfgTauStep tid ev
    (INTERNAL: external ev = None)
    (STEP: step ρ1 tid ev ρ2).
(* One step can be led by some τ-steps. ev can be either observable or not. *)
Inductive one_step ρ1 tid ev ρ2 : Prop :=
| CfgOneStep ρ1'
    (TAU_STEP: rtc τstep ρ1 ρ1')
    (ONE_STEP: step ρ1' tid ev ρ2).



(* TODO: to use this, we need to redefine thread simulation to handle
  interferences. *)

(** Future states, by interferences *)
(* TODO: fix this *)
Definition future_state : relation state := λ σ1 σ2, σ1 = σ2.

(** Configuration simulation *)
Notation SIM_CFG := (relation (cfg bor_lang))%type.

Definition _sim (sim: SIM_CFG) (ρ1_src ρ1_tgt : cfg bor_lang) : Prop :=
  (* Wf ρ1_src → Wf ρ1_tgt → *)
  ∀ σ1_src σ1_tgt,
  (* σ1_src, σ1_tgt are new states by other threads' interferences *)
  Wf σ1_src → Wf σ1_tgt →
  future_state ρ1_src.2 σ1_src → future_state ρ1_tgt.2 σ1_tgt →
  (* σ1_src, σ1_tgt are related *)
  sim_state σ1_src σ1_tgt →
  (* (1) If `ρ1_tgt` is terminal, then `ρ1_src` terminates with τ steps. *)
  (terminal ρ1_tgt.1 → ∃ Ts2_src σ2_src,
      rtc τstep (ρ1_src.1, σ1_src) (Ts2_src, σ2_src) ∧
      sim_state σ2_src σ1_tgt ∧ terminal Ts2_src) ∧
  (* (2) If `ρ1_tgt` steps to `ρ2_tgt` with observation o, then exists `ρ2_src`
         s.t. `ρ1_src` steps to `ρ2_src` with observation o AND
         ρ2_src and ρ2_tgt related by sim. *)
  (∀ ρ2_tgt tid_tgt ev_tgt,
    one_step (ρ1_tgt.1, σ1_tgt) tid_tgt ev_tgt ρ2_tgt → ∃ ρ2_src tid_src ev_src,
      one_step (ρ1_src.1, σ1_src) tid_src ev_src ρ2_src ∧
      externally_equiv ev_src ev_tgt ∧
      sim_state ρ1_src.2 ρ2_tgt.2 ∧ sim ρ2_src ρ2_tgt).

Lemma _sim_monotone : monotone2 _sim.
Proof.
  intros ρ1_src ρ1_tgt r r' TS LE σ1_src σ1_tgt WF1 WF2 FT1 FT2 SS.
  destruct (TS _ _ WF1 WF2 FT1 FT2 SS) as [TERM STEP]. split; [done|].
  intros ρ2_tgt tid ev_tgt ONE.
  destruct (STEP _ _ _ ONE) as (ρ2_src & tid_src & ev_src & ONE' & EV & SS2 & Hr).
  exists ρ2_src, tid_src, ev_src. do 3 (split; [done|]). by apply LE.
Qed.
Hint Resolve _sim_monotone: paco.

(** The actual simulation *)
Definition sim: SIM_CFG := paco2 _sim bot2. *)

(** Composition : composing disjoint configuration preserves
  configuration simulation *)

(** Adequacy: thread simulation implies configuration simulation *)

(** Adequacy: congfiguration simulation implies behavior inclusion *)
