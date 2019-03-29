From stbor Require Import lang notation steps.
From Paco Require Import paco.

Class Terminal A := terminal : A → Prop.
Existing Class terminal.

Definition epxr_terminal' (e: expr) : Prop := is_Some (to_val e).
Instance expr_terminal : Terminal expr := epxr_terminal'.

(** Thread simulation *)
Definition SIM_EXPR := relation expr.
Definition SIM_THREAD := SIM_EXPR → expr → state → expr → state → Prop.

(* TODO: we are ignoring fork *)
(* thread τ-step has no observation. *)
Inductive thread_τstep (eσ1 eσ2: expr * state) : Prop :=
| ThreadTauStep (STEP: prim_step eσ1.1 eσ1.2 [] eσ2.1 eσ2.2 []).
Inductive thread_onestep eσ1 o eσ2 : Prop :=
| ThreadOneStep eσ1'
    (TAU_STEP: rtc thread_τstep eσ1 eσ1')
    (ONE_STEP: prim_step eσ1'.1 eσ1'.2 [o] eσ2.1 eσ2.2 []).

Definition _sim_thread (sim_thread: SIM_THREAD) (sim_terminal: SIM_EXPR)
  (e1_src: expr) (σ1_src: state) (e1_tgt: expr) (σ1_tgt: state) : Prop :=
  (* assuming wellformedness *)
  Wf σ1_src → Wf σ1_tgt →
  (* TODO: state relations σ1_src & σ1_tgt → *)
  (* (1) If `e1_tgt` is terminal, then `e1_src` terminates with τ steps *)
  (terminal e1_tgt → ∃ e2_src σ2_src,
    rtc thread_τstep (e1_src, σ1_src) (e2_src, σ2_src) ∧
    terminal e2_src ∧ sim_terminal e2_src e1_tgt
    (* ∧ state relations: σ2_src & σ1_tgt *)) ∧
  (* (2) If `(e1_tgt, σ1_tgt)` steps to `(e2_tgt, σ2_tgt)` with observation o,
         then exists `(e2_src, σ2_src)`
         s.t. `(e1_src, σ1_src)` steps to `(e2_src, σ2_src)` with observation o *)
  (∀ e2_tgt σ2_tgt o, thread_onestep (e1_tgt, σ1_tgt) o (e2_tgt, σ2_tgt)
    → ∃ e2_src σ2_src,
      thread_onestep (e1_src, σ1_src) o (e2_src, σ2_src) ∧
      sim_thread sim_terminal e2_src σ2_src e2_tgt σ2_tgt
      (* TODO: state relations σ2_src & σ2_tgt → *)).

Lemma _sim_thread_monotone : monotone5 _sim_thread.
Proof.
  intros re e1_src σ1_src e1_tgt σ1_tgt r r' TS LE WF1 WF2.
  destruct (TS WF1 WF2) as [TERM STEP]. split; [done|].
  intros e2_tgt σ2_tgt o ONE.
  destruct (STEP _ _ _ ONE) as (e2_src & σ2_src & ONE_src & Hr).
  exists e2_src, σ2_src. split; [done|by apply LE].
Qed.
Hint Resolve _sim_thread_monotone: paco.

Definition sim_thread: SIM_THREAD := paco5 _sim_thread bot5.

(** Configuration simulation *)
Implicit Type (ρ: cfg bor_lang).

Definition cfg_terminal' ρ : Prop := ∀ e, e ∈ ρ.1 → terminal e.
Instance cfg_terminal : Terminal (cfg bor_lang) := cfg_terminal'.

(* This duplicates iris.program_logic.language to expose a thread id *)
Inductive step ρ1 tid κ ρ2 : Prop :=
| StepAtomic e1 σ1 e2 σ2 efs t1 t2 :
   ρ1 = (t1 ++ e1 :: t2, σ1) →
   ρ2 = (t1 ++ e2 :: t2 ++ efs, σ2) →
   prim_step e1 σ1 κ e2 σ2 efs →
   tid = length t1 →
   step ρ1 tid κ ρ2.

(* τ-step has no observation and ignore tid. *)
Inductive τstep ρ1 ρ2 : Prop :=
| TauStep tid (STEP: step ρ1 tid [] ρ2).

(* One true step can be led by some τ-steps. *)
Inductive one_step ρ1 tid o ρ2 : Prop :=
| OneStep ρ1' (TAU_STEP: rtc τstep ρ1 ρ1') (ONE_STEP: step ρ1' tid [o] ρ2).

(* TODO: do we need observations more than a singleton list? *)
(* TODO: de we need to relax the observation relation? *)
Definition _sim (sim: relation (cfg bor_lang)) (ρ1_src ρ1_tgt : cfg bor_lang)
  : Prop :=
  (* assuming wellformedness *)
  Wf ρ1_src.2 → Wf ρ1_tgt.2 →
  (* TODO: state relations ρ1_src & ρ1_tgt → *)
  (* (1) If `ρ1_tgt` is terminal, then `ρ1_src` terminates with τ steps *)
  (terminal ρ1_tgt → ∃ ρ2_src, rtc τstep ρ1_src ρ2_src ∧ terminal ρ2_src
      (* ∧ state relations: ρ2_src & ρ1_tgt *)) ∧
  (* (2) If `ρ1_tgt` steps to `ρ2_tgt` with observation o, then exists `ρ2_src`
         s.t. `ρ1_src` steps to `ρ2_src` with observation o *)
  (∀ ρ2_tgt tid o, one_step ρ1_tgt tid o ρ2_tgt → ∃ ρ2_src,
      one_step ρ1_src tid o ρ2_src ∧ sim ρ2_src ρ2_tgt
      (* TODO: state relations ρ1_src & ρ1_tgt → *)).

Lemma _sim_monotone : monotone2 _sim.
Proof.
  intros ρ1_src ρ1_tgt r r' TS LE WF1 WF2.
  destruct (TS WF1 WF2) as [TERM STEP]. split; [done|].
  intros ρ2_tgt tid o ONE. destruct (STEP _ _ _ ONE) as [ρ2_src [ONE_src Hr]].
  exists ρ2_src. split; [done|by apply LE].
Qed.
Hint Resolve _sim_monotone: paco.

(** The actual simulation *)
Definition sim: relation (cfg bor_lang) := paco2 _sim bot2.

(** Composition (probably not needed: composing disjoint configuration preserves
  configuration simulation *)

(** Compatibility: language constructs preserve thread/configuration simulation *)

(** Adequacy: thread simulation implies configuration simulation *)

(** Adequacy: congfiguration simulation implies behavior inclusion *)
