From Paco Require Import paco.
From stbor Require Export properties steps_wf.

(** State simulation *)

(* Simulated memory values: ignore tags of locations *)
Definition sim_immediate (v1 v2: immediate) :=
  match v1, v2 with
  | RecV _ _ _, RecV _ _ _ => v1 = v2
  | LitV LitPoison, LitV LitPoison => True
  | LitV (LitInt n1), LitV (LitInt n2) => n1 = n2
  | LitV (LitLoc l1 bor1), LitV (LitLoc l2 bor2) => l1 = l2
  | _,_ => False
  end.

Definition sim_val (v1 v2: val) :=
  match v1, v2 with
  | ImmV v1, ImmV v2 => sim_immediate v1 v2
  | TValV vs1, TValV vs2 =>
    length vs1 = length vs2 ∧
    ∀ i v1 v2, vs1 !! i = Some v1 → vs2 !! i = Some v2 → sim_immediate v1 v2
  | PlaceV l1 tg1 T1, PlaceV l2 tg2 T2 => l1 = l2
  | _, _ => False
  end.

Definition sim_val_expr (e1 e2: expr) :=
  ∀ v2, to_val e2 = Some v2 → ∃ v1, to_val e1 = Some v1 ∧ sim_val v1 v2.

(* Simulated state *)
(* - cheap: Target memory is simulated by source memory
   - cpro: Call states are the same
   - cstk: TODO missing relation between stacks
   - cclk: TODO missing relation between tag clocks *)
Record sim_state (σ_src σ_tgt: state) := {
  sim_state_mem_dom : dom (gset loc) σ_src.(cheap) ≡ dom (gset loc) σ_tgt.(cheap);
  sim_state_stack_dom : dom (gset loc) σ_src.(cstk) ≡ dom (gset loc) σ_tgt.(cstk);
  sim_state_protectors : σ_src.(cpro) = σ_tgt.(cpro);
  sim_state_mem : ∀ l v2,
    σ_tgt.(cheap) !! l = Some v2 → ∃ v1, σ_src.(cheap) !! l = Some v1 ∧ sim_immediate v1 v2;
}.

Instance sim_immediate_po : PreOrder sim_immediate.
Proof.
  constructor; first by intros [[]|].
  intros [[]|] [[]|] [[]|]; simpl; try done; move => -> -> //.
Qed.

Instance sim_val_po : PreOrder sim_val.
Proof.
  constructor; first by (intros []; simpl; naive_solver).
  intros [|vl1|] [|vl2|] [|vl3|]; simpl; try done; [by etrans|..|naive_solver].
  move => [Eql1 H1] [Eql2 H2]. rewrite Eql1 Eql2. split; [done|].
  move => i v1 v3 Eq1 Eq3.
  destruct (lookup_lt_is_Some_2 vl2 i) as [v2 Eq2].
  { rewrite Eql2. by eapply lookup_lt_Some. }
  etrans; [by eapply H1|by eapply H2].
Qed.

Instance sim_val_expr_po : PreOrder sim_val_expr.
Proof.
  constructor.
  - intros ?. rewrite /sim_val_expr. naive_solver.
  - move => e1 e2 e3 S1 S2 v3 /S2 [v2 [/S1 [v1 [??]] ?]].
    exists v1. split; [done|by etrans].
Qed.

(** Thread simulation *)
(* This is a simulation between two expressions without any interference.
  It corresponds to a sequential simulation. *)

Notation SIM_EXPR := (relation expr)%type.
Notation SIM_THREAD := (SIM_EXPR → expr → state → expr → state → Prop)%type.

(* Generator for the actual simulation *)
(* TODO: sim_state is not right *)
(* Target is simulated by source.
  Adequacy should states that any defined behavior by target is also a defined
  behavior by source. In the proof of optimizations, we pick target to be the
  optimized version, and source to be the unoptimized one.
  This simulation is goal-based, ie. it does not have intermediate observation,
  and the simulation finalizes at the simulation `sim_terminal` between the
  non-reducible values.
  The values can contain any observations of the states in between by reading
  the memory. Thus the simulation maintains the relation `sim_state` between
  the states. *)
Definition _sim_thread (sim_thread: SIM_THREAD) (sim_terminal: SIM_EXPR)
  (e1_src: expr) (σ1_src: state) (e1_tgt: expr) (σ1_tgt: state) : Prop :=
  (* Wf ρ1_src → Wf ρ1_tgt → *)
  Wf σ1_src → Wf σ1_tgt →
  (* σ1_src, σ1_tgt are related *)
  sim_state σ1_src σ1_tgt →
  (* (1) If `e1_tgt` is terminal, then `e1_src` terminates with τ steps *)
  (terminal e1_tgt → ∃ e2_src σ2_src,
    rtc thread_step (e1_src, σ1_src) (e2_src, σ2_src) ∧
    sim_state σ2_src σ1_tgt ∧
    terminal e2_src ∧ sim_terminal e2_src e1_tgt) ∧
  (* (2) If `(e1_tgt, σ1_tgt)` steps to `(e2_tgt, σ2_tgt)` with 1+ step,
         then exists `(e2_src, σ2_src)`
         s.t. `(e1_src, σ1_src)` steps to `(e2_src, σ2_src)` with * step
         and still maintains the relation. *)
  (∀ e2_tgt σ2_tgt, thread_step (e1_tgt, σ1_tgt) (e2_tgt, σ2_tgt) →
      ∃ e2_src σ2_src,
      rtc thread_step (e1_src, σ1_src) (e2_src, σ2_src) ∧
      sim_state σ2_src σ2_tgt ∧
      sim_thread sim_terminal e2_src σ2_src e2_tgt σ2_tgt).

Lemma _sim_thread_mono : monotone5 _sim_thread.
Proof.
  intros re ???? r r' TS LE WF1 WF2 SS.
  destruct (TS WF1 WF2 SS) as [TERM STEP]. split; [done|].
  intros e2_tgt σ2_tgt ONE.
  destruct (STEP _ _ ONE) as (e2_src & σ2_src & STEP1 & SS' & Hr).
  exists e2_src, σ2_src. do 2 (split; [done|]). by apply LE.
Qed.
Hint Resolve _sim_thread_mono: paco.

(* Actual simulation *)
Definition sim_thread: SIM_THREAD := paco5 _sim_thread bot5.

Lemma thread_step_wf eσ1 eσ2 :
  thread_step eσ1 eσ2 → Wf eσ1.2 → Wf eσ2.2.
Proof. inversion 1. inversion PRIM. by eapply head_step_wf. Qed.
Lemma rtc_thread_step_wf eσ1 eσ2 :
  rtc thread_step eσ1 eσ2 → Wf eσ1.2 → Wf eσ2.2.
Proof.
  intros SS. induction SS; [done|]. intros WF1. apply IHSS. revert WF1.
  by apply thread_step_wf.
Qed.

Definition sim_expr (sim_thread: SIM_THREAD) (sim_terminal : SIM_EXPR)
  (e_src e_tgt: expr) : Prop :=
  ∀ σ_src σ_tgt, sim_thread sim_terminal e_src σ_src e_tgt σ_tgt.

Lemma sim_expr_mono st1 st2 : st1 <5= st2 → sim_expr st1 <3= sim_expr st2.
Proof. intros ST ??? PR ??. by apply ST, PR. Qed.

Inductive ctx (sim_thread : SIM_THREAD) : SIM_THREAD :=
| CtxIncl (sim_terminal : SIM_EXPR) e_src e_tgt σ_src σ_tgt
    (SIM: sim_thread sim_terminal e_src σ_src e_tgt σ_tgt):
    ctx sim_thread sim_terminal e_src σ_src e_tgt σ_tgt
| CtxBinOp (sim_terminal : SIM_EXPR)
    op e1_src e1_tgt σ_src σ_tgt e2_src e2_tgt
    (SIM1: sim_thread sim_terminal e1_src σ_src e1_tgt σ_tgt)
    (SIM2: sim_expr sim_thread sim_terminal e2_src e2_tgt) :
    ctx sim_thread sim_terminal (BinOp op e1_src e2_src) σ_src
                                (BinOp op e1_tgt e2_tgt) σ_tgt
| CtxApp (sim_terminal : SIM_EXPR)
    e_src e_tgt σ_src σ_tgt el_src el_tgt
    (SIMF: sim_thread sim_terminal e_src σ_src e_tgt σ_tgt)
    (EQL: length el_src = length el_tgt)
    (SIML: ∀ i ei_tgt, el_tgt !! i = Some ei_tgt →
      ∃ ei_src, el_src !! i = Some ei_src ∧ 
      sim_expr sim_thread sim_terminal ei_src ei_tgt) :
    ctx sim_thread sim_terminal (App e_src el_src) σ_src
                                (App e_tgt el_tgt) σ_tgt
| CtxProj (sim_terminal : SIM_EXPR)
    e1_src e1_tgt σ_src σ_tgt e2_src e2_tgt
    (SIM1: sim_thread sim_terminal e1_src σ_src e1_tgt σ_tgt)
    (SIM2: sim_expr sim_thread sim_terminal e2_src e2_tgt) :
    ctx sim_thread sim_terminal (Proj e1_src e2_src) σ_src
                                (Proj e1_tgt e2_tgt) σ_tgt
| CtxConc (sim_terminal : SIM_EXPR)
    e1_src e1_tgt σ_src σ_tgt e2_src e2_tgt
    (SIM1: sim_thread sim_terminal e1_src σ_src e1_tgt σ_tgt)
    (SIM2: sim_expr sim_thread sim_terminal e2_src e2_tgt) :
    ctx sim_thread sim_terminal (Conc e1_src e2_src) σ_src
                                (Conc e1_tgt e2_tgt) σ_tgt
| CtxCopy (sim_terminal : SIM_EXPR)
    e_src e_tgt σ_src σ_tgt
    (SIM: sim_thread sim_terminal e_src σ_src e_tgt σ_tgt) :
    ctx sim_thread sim_terminal (Copy e_src) σ_src
                                (Copy e_tgt) σ_tgt
| CtxWrite (sim_terminal : SIM_EXPR)
    e1_src e1_tgt σ_src σ_tgt e2_src e2_tgt
    (SIM1: sim_thread sim_terminal e1_src σ_src e1_tgt σ_tgt)
    (SIM2: sim_expr sim_thread sim_terminal e2_src e2_tgt) :
    ctx sim_thread sim_terminal (Write e1_src e2_src) σ_src
                                (Write e1_tgt e2_tgt) σ_tgt
| CtxDeref (sim_terminal : SIM_EXPR) T
    e_src e_tgt σ_src σ_tgt
    (SIM: sim_thread sim_terminal e_src σ_src e_tgt σ_tgt) :
    ctx sim_thread sim_terminal (Deref e_src T) σ_src
                                (Deref e_tgt T) σ_tgt
| CtxRef (sim_terminal : SIM_EXPR)
    e_src e_tgt σ_src σ_tgt
    (SIM: sim_thread sim_terminal e_src σ_src e_tgt σ_tgt) :
    ctx sim_thread sim_terminal (Ref e_src) σ_src
                                (Ref e_tgt) σ_tgt
| CtxField (sim_terminal : SIM_EXPR) path
    e_src e_tgt σ_src σ_tgt
    (SIM: sim_thread sim_terminal e_src σ_src e_tgt σ_tgt) :
    ctx sim_thread sim_terminal (Field e_src path) σ_src
                                (Field e_tgt path) σ_tgt
| CtxEndCall (sim_terminal : SIM_EXPR)
    e_src e_tgt σ_src σ_tgt
    (SIM: sim_thread sim_terminal e_src σ_src e_tgt σ_tgt) :
    ctx sim_thread sim_terminal (EndCall e_src) σ_src
                                (EndCall e_tgt) σ_tgt
| CtxRetag (sim_terminal : SIM_EXPR) kind
    e1_src e1_tgt σ_src σ_tgt e2_src e2_tgt
    (SIM1: sim_thread sim_terminal e1_src σ_src e1_tgt σ_tgt)
    (SIM2: sim_expr sim_thread sim_terminal e2_src e2_tgt) :
    ctx sim_thread sim_terminal (Retag e1_src kind e2_src) σ_src
                                (Retag e1_tgt kind e2_tgt) σ_tgt
| CtxCase (sim_terminal : SIM_EXPR)
    e_src e_tgt σ_src σ_tgt el_src el_tgt
    (SIMF: sim_thread sim_terminal e_src σ_src e_tgt σ_tgt)
    (EQL: length el_src = length el_tgt)
    (SIML: ∀ i ei_tgt, el_tgt !! i = Some ei_tgt →
      ∃ ei_src, el_src !! i = Some ei_src ∧
      sim_expr sim_thread sim_terminal ei_src ei_tgt) :
    ctx sim_thread sim_terminal (Case e_src el_src) σ_src
                                (Case e_tgt el_tgt) σ_tgt
.

Lemma ctx_mono: monotone5 ctx.
Proof.
  intros se e1 σ1 e2 σ2 r r' CTX TS. inversion CTX; subst.
  - econstructor 1; auto.
  - econstructor 2; auto. by eapply sim_expr_mono.
  - econstructor 3; auto. naive_solver eauto using sim_expr_mono.
  - econstructor 4; auto. by eapply sim_expr_mono.
  - econstructor 5; auto. by eapply sim_expr_mono.
  - econstructor 6; auto.
  - econstructor 7; auto. by eapply sim_expr_mono.
  - econstructor 8; auto.
  - econstructor 9; auto.
  - econstructor 10; auto.
  - econstructor 11; auto.
  - econstructor 12; auto. by eapply sim_expr_mono.
  - econstructor 13; auto. naive_solver eauto using sim_expr_mono.
Qed.

(** Compatibility: language constructs preserve thread simulation *)

Lemma ctx_weak_respectful: weak_respectful5 _sim_thread ctx.
Proof.
  econstructor; [by apply ctx_mono|].
  intros l r M1 M2 se e1 σ1 e2 σ2 CTX. destruct CTX.
  - (* incl *)
    eapply _sim_thread_mono; eauto. apply rclo5_incl.
  - intros WF1 WF2 SS. split.
    + intros TERM. exfalso. move : TERM. clear. cbv. naive_solver.
    + destruct (M2 _ _ _ _ _ SIM1 WF1 WF2 SS) as [TT ST].
      intros e2 σ2. admit.
  - intros WF1 WF2 SS. split.
    + intros TERM. exfalso. move : TERM. clear. cbv. naive_solver.
    + admit.
  - intros WF1 WF2 SS. split.
    + intros TERM. exfalso. move : TERM. clear. cbv. naive_solver.
Abort.

Lemma ctx_respectful: respectful5 _sim_thread ctx.
Proof.
  econstructor; [by apply ctx_mono|].
  intros l r M1 M2 se e1 σ1 e2 σ2 CTX. destruct CTX.
  - eapply _sim_thread_mono; eauto. intros. by econstructor 1.
  - intros WF1 WF2 SS.
    destruct (M2 _ _ _ _ _ SIM1 WF1 WF2 SS) as [TT ST]. split.
    + intros TERM. exfalso. move : TERM. clear. cbv. naive_solver.
    + intros e_tgt' σ_tgt' STEP.
Abort.
