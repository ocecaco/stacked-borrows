From Paco Require Import paco.

From stbor.lang Require Export defs.

CoInductive diverges
  (step: expr * config → expr * config → Prop)
  (cfg: expr * config) : Prop :=
| DivergeStep cfg' (STEP: step cfg cfg') (DIV: diverges step cfg') .

Definition sim_expr_terminal (e1 e2: expr) :=
  ∀ v2, to_val e2 = Some v2 → to_val e1 = Some v2.
Instance sim_expr_terminal_po : PreOrder sim_expr_terminal.
Proof.
  constructor.
  - intros ?. rewrite /sim_expr_terminal. naive_solver.
  - move => e1 e2 e3 S1 S2 v3 /S2 /S1 //.
Qed.

Notation SIM_CONFIG := (expr * config → expr * config → Prop)%type.

(* This is a simulation between two expressions without any interference.
  It corresponds to a sequential simulation. *)

Record sim_base (sim: SIM_CONFIG) (eσ1_src eσ1_tgt: expr * config) : Prop := mkSimBase {
  (* (1) If [eσ1_tgt] gets stuck, [eσ1_src] can also get stuck. *)
  sim_stuck :
    stuck eσ1_tgt.1 eσ1_tgt.2 → ∃ eσ2_src,
    eσ1_src ~t~>* eσ2_src ∧ stuck eσ2_src.1 eσ2_src.2 ;
  (* (2) If [eσ1_tgt] diverges, then [eσ1_src] diverges. *)
  (* sim_diverges : diverges tstep eσ1_tgt → diverges tstep eσ1_src ; *)
  (* (3) If [eσ1_tgt] is terminal, then [eσ1_src] terminates with some steps. *)
  sim_terminal :
    terminal eσ1_tgt.1 → ∃ eσ2_src,
    eσ1_src ~t~>* eσ2_src ∧ terminal eσ2_src.1 ∧ sim_expr_terminal eσ2_src.1 eσ1_tgt.1;
  (* (4) If [eσ1_tgt] steps to [eσ2_tgt] with 1 step,
       then exists [eσ2_src] s.t. [eσ1_src] steps to [eσ2_src] with * step. *)
  sim_step :
    ∀ eσ2_tgt, eσ1_tgt ~t~> eσ2_tgt → ∃ eσ2_src,
      eσ1_src ~t~>* eσ2_src ∧ sim eσ2_src eσ2_tgt;
}.

Definition no_UB (eσ: expr * config) : Prop :=
  ¬ (∀ eσ', eσ ~t~>* eσ' → stuck eσ'.1 eσ'.2).

(* Generator for the actual simulation *)
Definition _sim
  (sim : SIM_CONFIG) (eσ1_src eσ1_tgt: expr * config) : Prop :=
  Wf eσ1_src.2 → Wf eσ1_tgt.2 →
  (* If [eσ1_src] gets UB, we can have UB in the target, thus any [eσ1_tgt] is
      acceptable. Otherwise ... *)
  no_UB eσ1_src → sim_base sim eσ1_src eσ1_tgt.

Lemma _sim_mono : monotone2 (_sim).
Proof.
  intros eσ_src eσ_tgt r r' TS LE WF1 WF2 NUB.
  destruct (TS WF1 WF2 NUB) as [SU (* DI *) TE ST]. repeat split; auto.
  intros eσ2_tgt ONE. destruct (ST _ ONE) as (eσ2_src & STEP1 & Hr).
  exists eσ2_src. split; [done|]. by apply LE.
Qed.

(* Global simulation *)
Definition sim : SIM_CONFIG := paco2 _sim bot2.

Hint Resolve _sim_mono: paco.
