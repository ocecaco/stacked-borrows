From Paco Require Import paco.

From stbor.lang Require Export defs.

CoInductive diverges
  (step: expr * config → expr * config → Prop)
  (cfg: expr * config) : Prop :=
| DivergeStep cfg' (STEP: step cfg cfg') (DIV: diverges step cfg') .

(* We would want to state that the terminal expression should be [value], but
  that comes from the invariant that all functions return [value]'s, which is
  not visible here. Furthermore, we want to state that terminal means ``not
  reducible but safe'', so we cannot exclude Place from terminal.
  Consequently, we use [result]. *)
Definition sim_expr_terminal (e1 e2: expr) :=
  ∀ v2, to_result e2 = Some v2 → to_result e1 = Some v2.
Instance sim_expr_terminal_po : PreOrder sim_expr_terminal.
Proof.
  constructor.
  - intros ?. rewrite /sim_expr_terminal. naive_solver.
  - move => e1 e2 e3 S1 S2 v3 /S2 /S1 //.
Qed.

Notation SIM_CONFIG := (nat → expr * state → expr * state → Prop)%type.

(* This is a simulation between two expressions without any interference.
  It corresponds to a sequential simulation. *)

Section sim.
Variable (fns fnt: fn_env).

(* We use index to account for divergence. TODO: explain more. *)
Record sim_base (sim: SIM_CONFIG) (idx1: nat) (eσ1_src eσ1_tgt: expr * state)
  : Prop := mkSimBase {
  (* (1) If [eσ1_tgt] gets stuck, [eσ1_src] can also get stuck. *)
  sim_stuck :
    ~ stuck (Λ:= bor_lang fnt) eσ1_tgt.1 eσ1_tgt.2 ;
  (* (2) If [eσ1_tgt] is terminal, then [eσ1_src] terminates with some steps. *)
  sim_terminal :
    terminal eσ1_tgt.1 → ∃ eσ2_src, eσ1_src ~{fns}~>* eσ2_src ∧
      terminal eσ2_src.1 ∧ sim_expr_terminal eσ2_src.1 eσ1_tgt.1 ;
  (* (3) If [eσ1_tgt] steps to [eσ2_tgt] with 1 step,
       then exists [eσ2_src] s.t. [eσ1_src] steps to [eσ2_src] with * step. *)
  sim_step :
    ∀ eσ2_tgt, eσ1_tgt ~{fnt}~> eσ2_tgt → ∃ idx2 eσ2_src,
      (eσ1_src ~{fns}~>+ eσ2_src ∨ ((idx2 < idx1)%nat ∧ eσ1_src = eσ2_src)) ∧
      sim idx2 eσ2_src eσ2_tgt;
}.

(* TODO: duplicate *)
Definition never_stuck fs e σ :=
  ∀ e' σ', (e, σ) ~{fs}~>* (e', σ') → terminal e' ∨ reducible (Λ:=bor_lang fs)  e' σ'.

(* Generator for the actual simulation *)
Definition _sim
  (sim : SIM_CONFIG) (idx1: nat) (eσ1_src eσ1_tgt: expr * state) : Prop :=
  forall (NEVER_STUCK: never_stuck fns eσ1_src.1 eσ1_src.2)
    (WF_SRC: Wf eσ1_src.2)
    (WF_TGT: Wf eσ1_tgt.2),
    sim_base sim idx1 eσ1_src eσ1_tgt.

Lemma _sim_mono : monotone3 (_sim).
Proof.
  intros idx1 eσ_src eσ_tgt r r' TS LE NS WF1 WF2.
  destruct (TS NS WF1 WF2) as [SU TE ST]. repeat split; auto.
  intros eσ2_tgt ONE. destruct (ST _ ONE) as (idx2 & eσ2_src & STEP1 & Hr).
  exists idx2, eσ2_src. split; [done|]. by apply LE.
Qed.

(* Global simulation *)
Definition sim : SIM_CONFIG := paco3 _sim bot3.

End sim.

Hint Resolve _sim_mono: paco.
