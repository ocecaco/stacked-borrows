From Coq Require Import Program.Equality Lia.
From Paco Require Import paco.

From stbor.lang Require Import steps_wf.
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

Lemma stuck_terminal prog (eσ: expr * state):
  stuck (Λ:=bor_lang prog) eσ.1 eσ.2 ↔ (∀ r, ¬ term prog eσ r) ∧ ∀ eσ', ¬ eσ ~{prog}~> eσ'.
Proof.
 split => [[NT NS]|[NT NS]]; split.
 - rewrite /term. move => ?. by rewrite NT.
 - move => eσ' ST. inversion ST. eapply (NS _ eσ'.1 eσ'.2); eauto.
 - destruct (language.to_val eσ.1) as [v|] eqn:Eqv; [|done]. exfalso.
   apply (NT v Eqv).
 - intros ???? PRIM. apply (NS (e', σ')). by econstructor; eauto.
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
    { admit. (* never_stuck *) }
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
    { admit. (* never_stuck *) }
    { admit. (* WF *) }
    { admit. (* WF *) }
    clear SIM. intro SIM. inv SIM. inv MAT.
    + exfalso. eapply sim_stuck; eauto.
      apply stuck_terminal. ss.
    + exploit sim_terminal; eauto. i. des.
      pfold. econs; eauto.
      econs 2. rename x2 into SE. by apply SE.
    + pclearbot. exploit sim_step; eauto. i. des.
      * inv x1; ss.
        exploit CIH; eauto. i.
        apply tc_inv_l in x0. des.
        pfold. econs; eauto.
      * inv x1; ss. exploit IH; eauto.
        punfold INF. inv INF. inv TAU; eauto.
        econs 3; eauto.
Admitted.
