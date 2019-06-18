From Coq Require Import Program.Equality Lia.
From Paco Require Import paco.

From stbor.lang Require Import steps_wf.
From stbor.sim Require Import global invariant sflib.

Set Default Proof Using "Type".

(** Behaviors ----------------------------------------------------------------*)

Section BEHAVIOR.
  Context {Config State Value: Type}
           (step: forall (conf:Config) (s s':State), Prop)
           (term: forall (conf:Config) (s:State) (val:Value), Prop)
  .

  Inductive observation: Type :=
  | obs_term (retval:Value)
  | obs_inftau
  .

  Inductive behmatch
            (conf:Config)
            (behave: forall (s:State) (obs:observation), Prop)
    : forall (s:State) (obs:observation), Prop :=
  | beh_stuck
      s obs
      (NT: forall val, ¬ term conf s val)
      (NS: ∀ s', ¬ step conf s s')
    : behmatch conf behave s obs
  | beh_term
      s v
      (TERM: term conf s v)
    : behmatch conf behave s (obs_term v)
  | beh_inftau
      s s'
      (STEP: step conf s s')
      (INF: behave s' obs_inftau)
    : behmatch conf behave s obs_inftau
  .
  Hint Constructors behmatch.

  Inductive behave_ (conf:Config) behave (s:State) (obs:observation): Prop :=
  | behave_intro
      s'
      (TAU: rtc (step conf) s s')
      (MAT: behmatch conf behave s' obs)
  .
  Hint Constructors behave_.

  Lemma behave_mon conf: monotone2 (behave_ conf).
  Proof.
    repeat intro. destruct IN. destruct MAT; eauto.
  Qed.
  Hint Resolve behave_mon: paco.

  Definition behave (conf:Config): forall (s:State) (obs:observation), Prop := paco2 (behave_ conf) bot2.
End BEHAVIOR.
Hint Constructors behmatch.
Hint Constructors behave_.
Hint Resolve behave_mon: paco.

Definition init_expr := (Call #["main"] []).
Definition init_state := (mkState ∅ ∅ [] O O).

Definition term (prog:fn_env) (s:expr * state) (v:value): Prop :=
  to_result s.1 = Some (ValR v).

Definition behave_prog (prog:fn_env) (obs:@observation value): Prop :=
  behave tstep term prog (init_expr, init_state) obs.

(* TODO: move *)
Lemma tc_inv_l
      A (R:relation A) x z
      (TC: tc R x z):
  exists y, rtc R x y /\ R y z.
Proof.
  induction TC.
  - esplits; eauto. reflexivity.
  - des. esplits; [|by eauto]. eapply rtc_l; eauto.
Qed.

(* TODO: move *)
Lemma strong_induction
      (P : nat -> Prop)
      (IH: forall (n:nat) (IH: forall (k:nat) (LT: (k < n)%nat), P k), P n):
  forall n : nat, P n.
Proof.
  i. cut (forall (m k:nat), (k < m -> P k)%nat); [by eauto|].
  induction m.
  - i. nia.
  - i. apply lt_le_S in H. inv H; eauto.
Qed.

Lemma adequacy
      prog_src prog_tgt idx conf_src conf_tgt
      (SIM: sim prog_src prog_tgt idx conf_src conf_tgt)
  : behave tstep term prog_tgt conf_tgt <1= behave tstep term prog_src conf_src.
Proof.
  revert idx conf_src conf_tgt SIM. pcofix CIH. intros.
  punfold PR. inv PR.
  rename x2 into obs. rename s' into conf'_tgt. revert idx conf_src SIM MAT.
  dependent induction TAU; cycle 1.
  - rename x into conf_tgt.
    rename y into conf'_tgt.
    rename z into conf''_tgt.
    i. punfold SIM. exploit SIM.
    { admit. (* WF *) }
    { admit. (* WF *) }
    clear SIM. intro SIM. inv SIM.
    exploit sim_step; eauto. i. des.
    + inv x0; ss.
      rename eσ2_src into conf'_src.
      exploit IHTAU; eauto.
      intro BEH. punfold BEH. inv BEH.
      pfold. econs; [|by eauto]. etrans; eauto. apply tc_rtc. ss.
    + inv x0; ss.
      rename eσ2_src into conf'_src.
      exploit IHTAU; eauto.
  - intros idx. revert x.
    induction idx using strong_induction. i.
    punfold SIM. exploit SIM.
    { admit. (* WF *) }
    { admit. (* WF *) }
    clear SIM. intro SIM. inv SIM. inv MAT.
    + exploit sim_stuck; eauto.
      { admit. (* property of stuck *) }
      i. des.
      pfold. econs; eauto.
      admit. (* property of stuck *)
    + exploit sim_terminal; eauto. i. des.
      pfold. econs; eauto.
      econs 2.
      admit. (* property of terminal *)
    + pclearbot. exploit sim_step; eauto. i. des.
      * inv x1; ss.
        exploit CIH; eauto. i.
        apply tc_inv_l in x0. des.
        pfold. econs; eauto.
      * inv x1; ss. exploit IH; eauto.
        punfold INF. inv INF. inv TAU; eauto.
        econs 3; eauto.
Admitted.
