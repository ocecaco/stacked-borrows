From Paco Require Import paco.
From stbor Require Export properties.

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
Definition sim: SIM_CFG := paco2 _sim bot2.

(** Thread simulation *)
Notation SIM_EXPR := (relation expr)%type.
Notation SIM_THREAD := (SIM_EXPR → expr → state → expr → state → Prop)%type.

(* TODO: sim_state is not right *)
Definition _sim_thread (sim_thread: SIM_THREAD) (sim_terminal: SIM_EXPR)
  (e1_src: expr) (σ0_src: state) (e1_tgt: expr) (σ0_tgt: state) : Prop :=
  (* Wf ρ1_src → Wf ρ1_tgt → *)
  ∀ σ1_src σ1_tgt,
  (* σ1_src, σ1_tgt are new states by other threads' interferences *)
  Wf σ1_src → Wf σ1_tgt →
  future_state σ0_src σ1_src → future_state σ0_tgt σ1_tgt →
  (* σ1_src, σ1_tgt are related *)
  sim_state σ1_src σ1_tgt →
  (* (1) If `e1_tgt` is terminal, then `e1_src` terminates with τ steps *)
  (terminal e1_tgt → ∃ e2_src σ2_src,
    rtc thread_τstep (e1_src, σ1_src) (e2_src, σ2_src) ∧
    sim_state σ2_src σ1_tgt ∧
    terminal e2_src ∧ sim_terminal e2_src e1_tgt) ∧
  (* (2) If `(e1_tgt, σ1_tgt)` steps to `(e2_tgt, σ2_tgt)` with observation o,
         then exists `(e2_src, σ2_src)`
         s.t. `(e1_src, σ1_src)` steps to `(e2_src, σ2_src)` with observation o *)
  (∀ e2_tgt σ2_tgt ev_tgt efs,
    thread_step (e1_tgt, σ1_tgt) ev_tgt (e2_tgt, σ2_tgt) efs → ∃ e2_src σ2_src ev_src,
      thread_1step (e1_src, σ1_src) ev_src (e2_src, σ2_src) ∧
      externally_equiv ev_src ev_tgt ∧
      sim_state σ2_src σ2_tgt ∧
      sim_thread sim_terminal e2_src σ2_src e2_tgt σ2_tgt).

Lemma _sim_thread_monotone : monotone5 _sim_thread.
Proof.
  intros re ???? r r' TS LE σ1_src σ1_tgt WF1 WF2 FT1 FT2 SS.
  destruct (TS _ _ WF1 WF2 FT1 FT2 SS) as [TERM STEP]. split; [done|].
  intros e2_tgt σ2_tgt ev_tgt efs ONE.
  destruct (STEP _ _ _ _ ONE) as (e2_src & σ2_src & ev_src & ONE_src & EV & SS' & Hr).
  exists e2_src, σ2_src, ev_src. do 3 (split; [done|]). by apply LE.
Qed.
Hint Resolve _sim_thread_monotone: paco.

Definition sim_thread: SIM_THREAD := paco5 _sim_thread bot5.

(* Inductive ctx (sim_thread : SIM_THREAD) : SIM_THREAD :=
| CtxIncl (sim_terminal : SIM_EXPR) e_src e_tgt σ_src σ_tgt
    (SIM: sim_thread sim_terminal e_src σ_src e_tgt σ_tgt):
    ctx sim_thread sim_terminal e_src σ_src e_tgt σ_tgt
| CtxBinOp (sim_terminal : SIM_EXPR)
    e1_src e1_tgt σ1_src σ1_tgt e2_src e2_tgt σ2_src σ2_tgt
    (SIM1: sim_thread sim_terminal e1_src σ1_src e1_tgt σ1_tgt)
    (SIM2: sim_thread sim_terminal e2_src σ1_src e1_tgt σ1_tgt) :
    ctx sim_thread sim_terminal e1 σ1 e2 σ2. *)

(** Composition : composing disjoint configuration preserves
  configuration simulation *)

(** Compatibility: language constructs preserve thread/configuration simulation *)

(** Adequacy: thread simulation implies configuration simulation *)

(** Adequacy: congfiguration simulation implies behavior inclusion *)
