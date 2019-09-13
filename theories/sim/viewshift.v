From stbor.sim Require Export instance.

Set Default Proof Using "Type".

Lemma viewshift_frame_l r r1 r2 :
  r1 |==> r2 → (r ⋅ r1) |==> (r ⋅ r2).
Proof. intros VS r_f σs σt. rewrite 2!cmra_assoc. apply VS. Qed.

Lemma viewshift_frame_r r r1 r2 :
  r1 |==> r2 → (r1 ⋅ r) |==> (r2 ⋅ r).
Proof. intros VS ???. rewrite (cmra_comm r1) (cmra_comm r2) 2!cmra_assoc. apply VS. Qed.

Lemma viewshift_state_frame_l r r1 r2 σs σt :
  r1 |={σs,σt}=> r2 → (r ⋅ r1) |={σs,σt}=> (r ⋅ r2).
Proof. intros VS r_f. rewrite 2!cmra_assoc. apply VS. Qed.

Lemma viewshift_state_frame_r r r1 r2 σs σt :
  r1 |={σs,σt}=> r2 → (r1 ⋅ r) |={σs,σt}=> (r2 ⋅ r).
Proof. intros VS ?. rewrite (cmra_comm r1) (cmra_comm r2) 2!cmra_assoc. apply VS. Qed.

Lemma vs_state_drop_protector r c t L Ts σs σt
  (HN: Ts !! t = None)
  (REL: ∀ l, l ∈ L → pub_loc r l σs σt) :
  r ⋅ res_cs c (<[t := L]> Ts) |={σs, σt}=> r ⋅ res_cs c Ts.
Proof.
  intros r_f. rewrite 2!cmra_assoc.
  intros (WFS & WFT & VALID & PINV & CINV & SREL).

  have EQtm: (r_f ⋅ r ⋅ res_cs c (<[t := L]> Ts)).(rtm) ≡
             (r_f ⋅ r ⋅ res_cs c Ts).(rtm) by done.
  have UNIQUE: (r_f ⋅ r).(rcm) !! c = None.
  { destruct ((r_f ⋅ r).(rcm) !! c) eqn:Eqcs; [|done].
    move : (proj2 VALID c). rewrite lookup_op.
    rewrite Eqcs res_cs_lookup -Some_op.
    intros ?%exclusive_r; [done|apply _]. }
  have EQO: (r_f ⋅ r ⋅ res_cs c (<[t := L]> Ts)).(rcm) !! c ≡ Excl' (<[t := L]> Ts).
  { by rewrite lookup_op UNIQUE left_id res_cs_lookup. }

  have VALID': ✓ (r_f ⋅ r ⋅ res_cs c Ts).
  { by apply (local_update_discrete_valid_frame _ _ _ VALID), res_cs_local_update. }

  split; last split; last split; last split; last split; [done|done|done|..].
  - intros ???. rewrite -EQtm. apply PINV.
  - intros c1 Ts1.
    case (decide (c1 = c)) => ?; [subst c1|].
    + rewrite lookup_op UNIQUE left_id res_cs_lookup.
      intros Eq%Some_equiv_inj%Excl_inj%leibniz_equiv_iff. subst Ts1.
      specialize (CINV _ _ EQO) as [IN CINV].
      split; [done|]. intros t1 L1 Eq1.
      apply CINV. rewrite lookup_insert_ne; [done|].
      intros ?. subst t1. by rewrite HN in Eq1.
    + intros EQcs. apply (CINV c1 Ts1).
      rewrite lookup_op res_cs_lookup_ne; [|done].
      move : EQcs. by rewrite lookup_op res_cs_lookup_ne.
  - destruct SREL as (?&?&?&?& PB). do 4 (split; [done|]).
    intros l InD.
    specialize (PB _ InD) as [PB|(t1 & k1 & h1 & Eq1 & IS1 & PV)]; [by left|].
    rewrite ->EQtm in Eq1.
    destruct PV as [|(Eqk1 & c1 & T1 & L1 & Eqc1 & EqT1 & InL1)].
    { right. exists t1, k1, h1. do 2 (split; [done|]); by left. }
    case (decide (c1 = c)) => ?; [subst c1|].
    + move : Eqc1. rewrite lookup_op UNIQUE res_cs_lookup left_id.
      intros ?%Some_equiv_inj%Excl_inj%leibniz_equiv_iff. subst T1.
      case (decide (t1 = t)) => ?; [subst t1|].
      * left. eapply pub_loc_mono; [done|..|apply REL].
        { etrans; [|apply cmra_included_l]. apply cmra_included_r. }
        { clear - EqT1 InL1. move : EqT1.
          rewrite lookup_insert. intros. by simplify_eq. }
      * right. exists t1, k1, h1. do 2 (split; [done|]).
        right. split; [done|]. exists c, Ts, L1. split; last split; [..|done].
        { by rewrite lookup_op UNIQUE res_cs_lookup left_id. }
        { move : EqT1. by rewrite lookup_insert_ne. }
    + right. exists t1, k1, h1. do 2 (split; [done|]).
      right. split; [done|]. exists c1, T1, L1. split; [|done].
      rewrite lookup_op res_cs_lookup_ne; [|done].
      move : Eqc1. by rewrite lookup_op res_cs_lookup_ne.
Qed.
