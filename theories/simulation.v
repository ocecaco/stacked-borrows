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
(* TODO: alloc need to be deterministic *)
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

Notation SIM_CONFIG := (relation (expr * state))%type.
Notation SIM_THREAD := (SIM_CONFIG → SIM_CONFIG)%type.

Infix "~t~>" := thread_step (at level 70).
Infix "~t~>*" := (rtc thread_step) (at level 70).

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
Definition _sim_thread (sim_thread: SIM_THREAD) (sim_term: SIM_CONFIG)
  (eσ1_src eσ1_tgt: expr * state) : Prop :=
  Wf eσ1_src.2 → Wf eσ1_tgt.2 →
  (* (1) If `e1_tgt` is terminal, then `e1_src` terminates with τ steps *)
  (terminal eσ1_tgt.1 → ∃ eσ2_src,
    eσ1_src ~t~>* eσ2_src ∧ terminal eσ2_src.1 ∧ sim_term eσ2_src eσ1_tgt) ∧
  (* (2) If `(e1_tgt, σ1_tgt)` steps to `(e2_tgt, σ2_tgt)` with 1+ step,
         then exists `(e2_src, σ2_src)`
         s.t. `(e1_src, σ1_src)` steps to `(e2_src, σ2_src)` with * step
         and still maintains the relation. *)
  (∀ eσ2_tgt, eσ1_tgt ~t~> eσ2_tgt → ∃ eσ2_src,
      eσ1_src ~t~>* eσ2_src ∧ sim_thread sim_term eσ2_src eσ2_tgt).

Lemma _sim_thread_mono : monotone3 _sim_thread.
Proof.
  intros re ?? r r' TS LE WF1 WF2.
  destruct (TS WF1 WF2) as [TERM STEP]. split; [done|].
  intros eσ2_tgt ONE. destruct (STEP _ ONE) as (eσ2_src & STEP1 & Hr).
  exists eσ2_src. split; [done|]. by apply LE.
Qed.
Hint Resolve _sim_thread_mono: paco.

(* Actual simulation *)
Definition sim_thread: SIM_THREAD := paco3 _sim_thread bot3.

Lemma thread_step_wf eσ1 eσ2 :
  eσ1 ~t~> eσ2 → Wf eσ1.2 → Wf eσ2.2.
Proof. inversion 1. inversion PRIM. by eapply head_step_wf. Qed.
Lemma rtc_thread_step_wf eσ1 eσ2 :
  eσ1 ~t~>* eσ2 → Wf eσ1.2 → Wf eσ2.2.
Proof.
  intros SS. induction SS; [done|]. intros WF1. apply IHSS. revert WF1.
  by apply thread_step_wf.
Qed.


Notation SIM_STATE := (relation state)%type.

Inductive sim_terminal (sim_state : SIM_STATE) : SIM_CONFIG :=
| SimTerminal e_src σ_src e_tgt σ_tgt
    (TERM: terminal e_tgt)
    (VAL: sim_val_expr e_src e_tgt)
    (STATE: sim_state σ_src σ_tgt)
  : sim_terminal sim_state (e_src, σ_src) (e_tgt, σ_tgt).

Definition sim_expr (sim_thread: SIM_THREAD)
  (simp_pre : SIM_STATE) (e_src e_tgt: expr) (sim_post : SIM_STATE) : Prop :=
  ∀ σ_src σ_tgt, simp_pre σ_src σ_tgt →
    sim_thread (sim_terminal sim_post) (e_src, σ_src) (e_tgt, σ_tgt).

Lemma sim_expr_mono st1 st2 : st1 <3= st2 → sim_expr st1 <4= sim_expr st2.
Proof. intros ST ???? PR ???. by apply ST, PR. Qed.

Inductive ctx (sim_thread : SIM_THREAD) : SIM_THREAD :=
| CtxIncl (sim_post : SIM_CONFIG) eσ_src eσ_tgt
    (SIM: sim_thread sim_post eσ_src eσ_tgt) :
    ctx sim_thread sim_post eσ_src eσ_tgt
| CtxTerm (sim_post : SIM_STATE) eσ_src eσ_tgt
    (SIM: sim_terminal sim_post eσ_src eσ_tgt) :
    ctx sim_thread (sim_terminal sim_post) eσ_src eσ_tgt
| CtxBinOp (sim1 sim2 : SIM_STATE)
    op e1_src e1_tgt σ1_src σ1_tgt e2_src e2_tgt
    (SIM1: sim_thread (sim_terminal sim1) (e1_src, σ1_src) (e1_tgt, σ1_tgt))
    (SIM2: sim_expr sim_thread sim1 e2_src e2_tgt sim2) :
    ctx sim_thread (sim_terminal sim2) (BinOp op e1_src e2_src, σ1_src)
                                        (BinOp op e1_tgt e2_tgt, σ1_tgt)
| CtxBinOpR (sim : SIM_STATE)
    op e1_src e1_tgt σ_src σ_tgt e2_src e2_tgt
    (TERM1: terminal e1_src) (TERM2: terminal e1_tgt)
    (SIM1: sim_thread (sim_terminal sim) (e2_src, σ_src) (e2_tgt, σ_tgt)) :
    ctx sim_thread (sim_terminal sim)
                   (BinOp op e1_src e2_src, σ_src)
                   (BinOp op e1_tgt e2_tgt, σ_tgt).

(* | CtxApp (simλ : SIM_STATE)
    e_src e_tgt σ_src σ_tgt el_src el_tgt
    (SIMF: sim_thread simλ e_src σ_src e_tgt σ_tgt)
    (EQL: length el_src = length el_tgt)
    (SIML: ∀ i ei_tgt, el_tgt !! i = Some ei_tgt →
      ∃ ei_src, el_src !! i = Some ei_src ∧
      sim_expr sim_thread sim_terminal ei_src ei_tgt) :
    ctx sim_thread sim_terminal (App e_src el_src) σ_src
                                (App e_tgt el_tgt) σ_tgt. *)
(* | CtxTVal
    ctx sim_thread sim_terminal (TVal el_src) σ_src
                                (TVal el_tgt) σ_tgt. *)
(* | CtxProj (sim1 sim2 : SIM_STATE)
    e1_src e1_tgt σ_src σ_tgt e2_src e2_tgt
    (SIM1: sim_thread sim1 e1_src σ_src e1_tgt σ_tgt)
    (SIM2: sim_expr sim_thread sim1 e2_src e2_tgt sim2) :
    ctx sim_thread sim2 (Proj e1_src e2_src) σ_src
                        (Proj e1_tgt e2_tgt) σ_tgt
| CtxConc (sim1 sim2 : SIM_STATE)
    e1_src e1_tgt σ_src σ_tgt e2_src e2_tgt
    (SIM1: sim_thread sim1 e1_src σ_src e1_tgt σ_tgt)
    (SIM2: sim_expr sim_thread sim1 e2_src e2_tgt sim2) :
    ctx sim_thread sim2 (Conc e1_src e2_src) σ_src
                        (Conc e1_tgt e2_tgt) σ_tgt
| CtxCopy (sim_post : SIM_STATE)
    e_src e_tgt σ_src σ_tgt
    (SIM: sim_thread sim_post e_src σ_src e_tgt σ_tgt) :
    ctx sim_thread sim_post (Copy e_src) σ_src
                                (Copy e_tgt) σ_tgt
| CtxWrite (sim1 sim2 : SIM_STATE)
    e1_src e1_tgt σ_src σ_tgt e2_src e2_tgt
    (SIM1: sim_thread sim1 e1_src σ_src e1_tgt σ_tgt)
    (SIM2: sim_expr sim_thread sim1 e2_src e2_tgt sim2) :
    (* FIXME: not sim2, but sim2 + the effect of the write *)
    ctx sim_thread sim2 (Write e1_src e2_src) σ_src
                        (Write e1_tgt e2_tgt) σ_tgt
| CtxDeref (sim_post : SIM_STATE) T
    e_src e_tgt σ_src σ_tgt
    (SIM: sim_thread sim_post e_src σ_src e_tgt σ_tgt) :
    ctx sim_thread sim_post (Deref e_src T) σ_src
                            (Deref e_tgt T) σ_tgt
| CtxRef (sim_post : SIM_STATE)
    e_src e_tgt σ_src σ_tgt
    (SIM: sim_thread sim_post e_src σ_src e_tgt σ_tgt) :
    ctx sim_thread sim_post (Ref e_src) σ_src
                                (Ref e_tgt) σ_tgt
| CtxField (sim_post : SIM_STATE) path
    e_src e_tgt σ_src σ_tgt
    (SIM: sim_thread sim_post e_src σ_src e_tgt σ_tgt) :
    ctx sim_thread sim_post (Field e_src path) σ_src
                            (Field e_tgt path) σ_tgt
| CtxEndCall (sim_post : SIM_STATE)
    e_src e_tgt σ_src σ_tgt
    (SIM: sim_thread sim_post e_src σ_src e_tgt σ_tgt) :
    ctx sim_thread sim_post (EndCall e_src) σ_src
                            (EndCall e_tgt) σ_tgt
| CtxRetag (sim1 sim2 : SIM_STATE) kind
    e1_src e1_tgt σ_src σ_tgt e2_src e2_tgt
    (SIM1: sim_thread sim1 e1_src σ_src e1_tgt σ_tgt)
    (SIM2: sim_expr sim_thread sim1 e2_src e2_tgt sim2) :
    (* FIXME: not sim2, but sim2 + the effect of the retag *)
    ctx sim_thread sim2 (Retag e1_src kind e2_src) σ_src
                        (Retag e1_tgt kind e2_tgt) σ_tgt. *)
(* | CtxCase (sim_terminal : SIM_STATE)
    e_src e_tgt σ_src σ_tgt el_src el_tgt
    (SIMF: sim_thread sim_terminal e_src σ_src e_tgt σ_tgt)
    (EQL: length el_src = length el_tgt)
    (SIML: ∀ i ei_tgt, el_tgt !! i = Some ei_tgt →
      ∃ ei_src, el_src !! i = Some ei_src ∧
      sim_expr sim_thread sim_terminal ei_src ei_tgt) :
    ctx sim_thread sim_terminal (Case e_src el_src) σ_src
                                (Case e_tgt el_tgt) σ_tgt
. *)

Lemma ctx_mono: monotone3 ctx.
Proof.
  intros se [e1 σ1] [e2 σ2] r r' CTX TS. inversion CTX; subst.
  - econstructor 1; auto.
  - econstructor 2; auto.
  - econstructor 3. by eapply TS. by eapply sim_expr_mono.
  - econstructor 4; auto.
(*   - econstructor 3. by eapply TS. by eapply sim_expr_mono.
  - econstructor 4. by eapply TS. by eapply sim_expr_mono.
  - econstructor 5; auto.
  - econstructor 6. by eapply TS. by eapply sim_expr_mono.
  - econstructor 7; auto.
  - econstructor 8; auto.
  - econstructor 9; auto.
  - econstructor 10; auto.
  - econstructor 11. by eapply TS. by eapply sim_expr_mono.
 *)Qed.

(** Compatibility: language constructs preserve thread simulation *)

Ltac inv_head_step :=
  repeat match goal with
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : _ = of_val ?v |- _ =>
     is_var v; destruct v; first[discriminate H|injection H as H]
  | H : head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H ; subst; clear H
  end.

Lemma thread_step_bin_op_left_non_terminal op e1 e2 e' σ σ'
  (STEP: (BinOp op e1 e2, σ) ~t~> (e', σ'))
  (NT: ¬ terminal e1):
  ∃ e1', (e1, σ) ~t~> (e1', σ') ∧ e' = BinOp op e1' e2.
Proof.
  inversion_clear STEP; simpl in PRIM.
  inversion_clear PRIM as [??? Eq1 ? HS]. subst.
  have Eq: BinOp op e1 e2 = ectx_language.fill [BinOpLCtx op e2] e1 by done.
  rewrite Eq in Eq1.
  apply expr_terminal_False in NT.
  destruct (step_by_val _ _ _ _ _ _ _ _ _ Eq1 NT HS) as [K'' Eq'].
  rewrite Eq' -fill_comp in Eq1.
  have Eq'' := fill_inj _ _ _ Eq1.
  eexists. split.
  - econstructor. econstructor; [exact Eq''|..|exact HS]. eauto.
  - by rewrite Eq' -fill_comp.
Qed.

Lemma thread_step_bin_op_right_non_terminal op e1 e2 e' σ σ'
  (STEP: (BinOp op e1 e2, σ) ~t~> (e', σ'))
  (TM: terminal e1) (NT: ¬ terminal e2):
  ∃ e2', (e2, σ) ~t~> (e2', σ') ∧ e' = BinOp op e1 e2'.
Proof.
  inversion_clear STEP; simpl in PRIM.
  inversion_clear PRIM as [??? Eq1 ? HS]. subst.
  move : TM => /expr_terminal_True [v1 Eqv1].
  have Eq: BinOp op e1 e2 = ectx_language.fill [BinOpRCtx op v1] e2.
  { by rewrite /= -(of_to_val _ _ Eqv1). }
  rewrite Eq in Eq1.
  apply expr_terminal_False in NT.
  destruct (step_by_val _ _ _ _ _ _ _ _ _ Eq1 NT HS) as [K'' Eq'].
  rewrite Eq' -fill_comp in Eq1.
  have Eq'' := fill_inj _ _ _ Eq1.
  eexists. split.
  - econstructor. econstructor; [exact Eq''|..|exact HS]. eauto.
  - by rewrite Eq' -fill_comp -(of_to_val _ _ Eqv1) /=.
Qed.


Require Import Coq.Program.Equality.
Lemma thread_step_bin_op_red_r e1 σ1 e1' σ1' e2 e2' σ2' op:
  (e1, σ1) ~t~>* (e1', σ1') → terminal e1' →
  (e2, σ1') ~t~>* (e2', σ2') →
  (BinOp op e1 e2, σ1) ~t~>* (BinOp op e1' e2', σ2').
Proof.
  intros S1 T1 S2.
  etrans. instantiate (1:= (BinOp op e1' e2, σ1')).
  - clear S2 T1.
    dependent induction S1 generalizing e1 σ1 e2; first by constructor.
    destruct y as [e0 σ0].
    etrans; last apply IHS1; [|eauto..]. apply rtc_once.
    clear -H. admit.
  - clear S1.
    dependent induction S2 generalizing e2 σ1'; first by constructor.
    destruct y as [e0 σ0].
    etrans; last apply IHS2; [|eauto..]. apply rtc_once.
    clear -H. admit.
Admitted.

Lemma sim_val_expr_terminal e_src e_tgt :
  sim_val_expr e_src e_tgt → terminal e_tgt → terminal e_src.
Proof. move => SIM /expr_terminal_True [? /SIM [? [??]]]. by eexists. Qed.
Lemma expr_terminal_no_step eσ1 eσ2 :
  terminal eσ1.1 → ¬ thread_step eσ1 eσ2.
Proof.
  destruct eσ1 as [e σ].
  move => EQ STEP.
  inversion_clear STEP; simpl in PRIM.
  inversion_clear PRIM as [??? Eq1 ? HS%val_head_stuck]. subst.
  apply fill_val in EQ.
  rewrite /= HS in EQ. by destruct EQ.
Qed.

Lemma sim_terminal_sim_thread
  (sim: SIM_THREAD) (sim_post: SIM_STATE) eσ_src eσ_tgt :
  sim_terminal sim_post eσ_src eσ_tgt →
  _sim_thread sim (sim_terminal sim_post) eσ_src eσ_tgt.
Proof.
  intros SIM WF1 WF2. inversion SIM; subst. split.
  - intros ?. exists (e_src, σ_src). split; [constructor|]. split; [|done].
    by eapply sim_val_expr_terminal.
  - intros ??. exfalso. by eapply expr_terminal_no_step; eauto.
Qed.

Lemma ctx_weak_respectful: weak_respectful3 _sim_thread ctx.
Proof.
  econstructor; [by apply ctx_mono|].
  intros l r LE GF se [e1 σ1] [e2 σ2] CTX.
  destruct CTX;
    [(* incl *) eapply _sim_thread_mono; eauto; apply rclo3_incl
    |(* term *) by apply sim_terminal_sim_thread|..];
    intros WF1 WF2;
    (split; [intros TERM; exfalso; move : TERM; clear; cbv; naive_solver|]);
    intros [eo_tgt σo_tgt] STEP.
  - (* BinOp *)
    destruct (GF _ _ _ SIM1 WF1 WF2) as [TT ST].
    case (decide (terminal e1_tgt)) as [Te1|NTe1].
    + destruct (TT Te1) as ([e1'_src σ1'_src] & RS & Te1' & ST').
      inversion ST'; subst.
      (* have ST2:= GF _ _ _ _ _ (SIM2 σ1'_src σ_tgt). *)
      destruct (GF _ _ _ (SIM2 _ _ STATE) (rtc_thread_step_wf _ _ RS WF1)
                  WF2) as [TT2 ST2].
      case (decide (terminal e2_tgt)) as [Te2|NTe2].
      * destruct (TT2 Te2) as ([e2'_src σ2'_src] & RS2 & Te2' & ST2').
        eexists (_, σ2'_src). split.
        { admit. }
        { apply rclo3_step, CtxTerm. inversion ST2'; subst. constructor.
          - admit.
          - admit.
          - (* σo_tgt - σ1_tgt *) admit. }
      * destruct (thread_step_bin_op_right_non_terminal _ _ _ _ _ _ STEP Te1 NTe2)
          as [e2'_tgt [STEP' Eq']]. rewrite Eq'.
        destruct (ST2 _ STEP') as ([e2'_src σ2'_src] & TS' & HR).
        exists (BinOp op e1'_src e2'_src, σ2'_src). split.
        { eapply thread_step_bin_op_red_r; eauto. }
        { apply rclo3_step, CtxBinOpR; auto. by apply rclo3_incl. }
    + destruct (thread_step_bin_op_left_non_terminal _ _ _ _ _ _ STEP NTe1)
        as [e1'_tgt [STEP' Eq']]. rewrite Eq'.
      destruct (ST _ STEP') as ([e1'_src σ1'_src] & RS & HR).
      exists (BinOp op e1'_src e2_src, σ1'_src). split.
      * admit.
      * eapply rclo3_step, CtxBinOp.
        { by apply rclo3_incl. }
        { eapply sim_expr_mono; [by apply rclo3_incl|].
          eapply sim_expr_mono; [by apply LE|done]. }
  - (* BinOpR *)
    destruct (GF _ _ _ SIM1 WF1 WF2) as [TT ST].
    case (decide (terminal e2_tgt)) as [Te2|NTe2].
    + destruct (TT Te2) as ([e2'_src σ2'_src] & RS2 & Te2' & ST2').
      eexists (_, σ2'_src). split.
      { admit. }
      { apply rclo3_step, CtxTerm. inversion ST2'; subst.
        constructor.
        - admit.
        - admit.
        - (* σo_tgt - σ1_tgt *) admit. }
    + destruct (thread_step_bin_op_right_non_terminal _ _ _ _ _ _ STEP TERM2 NTe2)
        as [e2'_tgt [STEP' Eq']]. rewrite Eq'.
      destruct (ST _ STEP') as ([e2'_src σ2'_src] & TS' & HR).
      exists (BinOp op e1_src e2'_src, σ2'_src). split.
      { admit. }
      { apply rclo3_step, CtxBinOpR; auto. by apply rclo3_incl. }
Abort.

(* Lemma ctx_respectful: respectful5 _sim_thread ctx.
Proof.
  econstructor; [by apply ctx_mono|].
  intros l r LE M2 se e1 σ1 e2 σ2 CTX.
  destruct CTX;
    [(* incl *) eapply _sim_thread_mono; eauto;  intros; by econstructor 1|..];
    intros WF1 WF2 SS;
    (split; [intros TERM; exfalso; move : TERM; clear; cbv; naive_solver|]);
    intros e_tgt' σ_tgt' STEP.
  - (* BinOp *)
    destruct (M2 _ _ _ _ _ SIM1 WF1 WF2 SS) as [TT ST].
    case (decide (terminal e1_tgt)) as [Te1|NTe1].
    + destruct (TT Te1) as (e1'_src & σ1'_src & RS & SS' & Te1' & ST').
      destruct (M2 _ _ _ _ _ (SIM2 σ1'_src σ_tgt) (rtc_thread_step_wf _ _ RS WF1)
                  WF2 SS') as [TT2 ST2].
      case (decide (terminal e2_tgt)) as [Te2|NTe2].
      * destruct (TT2 Te2) as (e2'_src & σ2'_src & RS2 & SS2' & Te2' & ST2').
        admit.
      * destruct (thread_step_bin_op_right_non_terminal _ _ _ _ _ _ STEP Te1 NTe2)
          as [e2'_tgt [STEP' Eq']]. rewrite Eq'.
        destruct (ST2 _ _ STEP') as (e2'_src & σ2'_src & RS2 & SS2' & HR).
        exists (BinOp op e1'_src e2'_src), σ2'_src. split; last split; [|done|].
        { admit. }
        { apply CtxBinOp.
          - admit.
          - eapply sim_expr_mono; [by apply rclo5_incl|].
            eapply sim_expr_mono; [by apply LE|].
            admit. }
    + destruct (thread_step_bin_op_left_non_terminal _ _ _ _ _ _ STEP NTe1)
        as [e1'_tgt [STEP' Eq']]. rewrite Eq'.
      destruct (ST _ _ STEP') as (e1'_src & σ1'_src & RS & SS' & HR).
      exists (BinOp op e1'_src e2_src), σ1'_src. split; last split; [|done|].
      * admit.
      * apply rclo5_step, CtxBinOp.
        { by apply rclo5_incl. }
        { eapply sim_expr_mono; [by apply rclo5_incl|].
          eapply sim_expr_mono; [by apply LE|done]. }
Abort. *)
