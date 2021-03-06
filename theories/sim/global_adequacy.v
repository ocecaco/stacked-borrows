From Coq Require Import Program.Equality Lia.
From Paco Require Import paco.

From stbor.lang Require Import steps_wf steps_inversion.
From stbor.sim Require Import behavior global invariant sflib.

Set Default Proof Using "Type".

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

(** A classically provable assumption: each program is either never-stuck or it can get stuck. *)
Definition stuck_decidable_1 prog: Prop :=
  ∀ e σ, never_stuck prog e σ \/
                    exists e' σ', (e, σ) ~{prog}~>* (e', σ') /\
                             ~ terminal e' /\
                             ~ reducible prog e' σ'.
Definition stuck_decidable: Prop := ∀ prog, stuck_decidable_1 prog.

Lemma classically_stuck_decidable :
  (∀ P, P ∨ ¬P) → stuck_decidable.
Proof.
  intros EM prog e σ.
  set RHS := exists _, _. destruct (EM RHS) as [POS|NEG]; first by right.
  left. intros ???. destruct (EM (terminal e' ∨ reducible prog e' σ')) as [POS2|NEG2]; first done.
  exfalso. apply NEG. eexists _, _. split; first eassumption.
  split; intros ?; apply NEG2; auto.
Qed.

Lemma adequacy_never_stuck
      prog_src
      prog_tgt idx conf_src conf_tgt
      (SIM: sim prog_src prog_tgt idx conf_src conf_tgt)
      (WFS: Wf conf_src.2) (WFT: Wf conf_tgt.2)
      (NEVERSTUCK: never_stuck prog_src conf_src.1 conf_src.2)
  : behave tstep term prog_tgt conf_tgt <1= behave tstep term prog_src conf_src.
Proof.
  revert idx conf_src conf_tgt SIM WFS WFT NEVERSTUCK. pcofix CIH. intros.
  punfold PR. inv PR.
  rename x2 into obs. rename s' into conf'_tgt. revert idx conf_src WFS NEVERSTUCK SIM MAT.
  dependent induction TAU; cycle 1.
  - rename x into conf_tgt.
    rename y into conf'_tgt.
    rename z into conf''_tgt.
    i. punfold SIM. exploit SIM; auto.
    clear SIM. intro SIM. inv SIM.
    have WFT': Wf conf'_tgt.2 by eapply tstep_wf; eauto.
    exploit sim_step; eauto. i. revert sim_stuck. des.
    + inv x0; ss.
      rename eσ2_src into conf'_src.
      have WFS' : Wf conf'_src.2 by eapply tstep_tc_wf; eauto.
      exploit (IHTAU WFT' idx2 _ WFS'); eauto.
      { eapply never_stuck_tstep_tc'; eauto. }
      intro BEH. punfold BEH. inv BEH.
      pfold. econs; [|by eauto]. etrans; eauto. apply tc_rtc. ss.
    + inv x0; ss.
      rename eσ2_src into conf'_src.
      exploit (IHTAU WFT' idx2 _ WFS); eauto.
  - intros idx. revert x WFT.
    induction idx using strong_induction. i.
    punfold SIM. exploit SIM; auto.
    clear SIM. intro SIM. inv SIM. inv MAT.
    + exfalso. destruct sim_stuck as [[v TE]|ST].
      * by apply (NT v).
      * unfold reducible in ST. des. eapply NS.
        destruct x. eauto.
    + clear sim_stuck. exploit sim_terminal; eauto. i. des.
      pfold. econs; eauto.
      unfold terminal in *. des.
      econs 2. unfold term. erewrite x2; eauto.
    + pclearbot. exploit sim_step; eauto. i. revert sim_stuck.
      rename s' into conf'_tgt.
      have WFT': Wf conf'_tgt.2 by eapply tstep_wf; eauto.
      des.
      * inv x1; ss.
        rename eσ2_src into conf'_src.
        exploit (CIH idx2 conf'_src conf'_tgt); eauto.
        { by eapply tstep_tc_wf; eauto. }
        { by eapply never_stuck_tstep_tc'; eauto. }
        intros ?.
        apply tc_inv_l in x0. des.
        pfold. econs; eauto.
      * inv x1; ss.
        rename eσ2_src into conf'_src.
        exploit (IH idx2 x0 conf'_tgt WFT' conf'_src); eauto.
        punfold INF. inv INF. inv TAU; eauto.
        econs 3; eauto.
Qed.

Lemma adequacy_classical
      prog_src
      prog_tgt idx conf_src conf_tgt
      `{NSD: stuck_decidable_1 prog_src}
      (SIM: sim prog_src prog_tgt idx conf_src conf_tgt)
      (WFS: Wf conf_src.2)
      (WFT: Wf conf_tgt.2)
  : behave tstep term prog_tgt conf_tgt <1= behave tstep term prog_src conf_src.
Proof.
  destruct (NSD conf_src.1 conf_src.2); cycle 1.
  { i. des. destruct conf_src as [e σ]. ss.
    pfold. econs; eauto. econs 1.
    - ii. eapply H0. unfold terminal, term in *. rewrite H2. eauto.
    - ii. apply H1. unfold reducible. destruct s'. eauto.
  }
  eapply adequacy_never_stuck; eauto.
Qed.
