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

Lemma vs_call_empty_public c :
  res_callState c (csOwned ∅) |==> res_callState c csPub.
Proof.
  intros r_f σs σt.
  intros (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  have EQtm: (r_f ⋅ res_callState c (csOwned ∅)).(rtm) ≡
             (r_f ⋅ res_callState c csPub).(rtm) by done.
  have EQlm: (r_f ⋅ res_callState c (csOwned ∅)).(rlm) ≡
             (r_f ⋅ res_callState c csPub).(rlm) by done.
  have UNIQUE: r_f.(rcm) !! c = None.
  { move : (proj2 (proj1 VALID) c). rewrite lookup_op.
    destruct (r_f.(rcm) !! c) as [cs|] eqn:Eqcs; [|done].
    rewrite Eqcs /= lookup_insert -Some_op.
    intros ?%exclusive_r; [done|apply _]. }
  have EQO: (r_f ⋅ res_callState c (csOwned ∅)).(rcm) !! c ≡ Some $ to_callStateR (csOwned ∅).
  { rewrite lookup_op UNIQUE left_id /= lookup_insert //. }
  split; last split; last split; last split; last split; last split;
    [done|done|..].
  - apply (local_update_discrete_valid_frame _ _ _ VALID).
    rewrite (cmra_comm r_f) (cmra_comm _ (res_callState _ csPub)).
    apply prod_local_update_1, prod_local_update_2.
    rewrite /= -insert_singleton_op // -insert_singleton_op //.
    rewrite -(insert_insert _ c (Cinr ()) (Cinl (Excl ∅))).
    eapply singleton_local_update; [by rewrite lookup_insert|].
    by apply exclusive_local_update.
  - intros t k h. rewrite -EQtm. intros Eqkh. by apply PINV.
  - intros c' cs'. case (decide (c' = c)) => ?; [subst c'|].
    + rewrite lookup_op UNIQUE left_id /= lookup_insert.
      intros Eq%Some_equiv_inj.
      specialize (CINV _ _ EQO) as [IN _].
      have Lt := state_wf_cid_agree _ WFT _ IN.
      destruct cs' as [[]| |]; try inversion Eq. done.
    + intros EQcs. apply (CINV  c' cs').
      move : EQcs. rewrite 2!lookup_op lookup_insert_ne // lookup_insert_ne //.
  - destruct SREL as (?&?&?&?& PB). do 4 (split; [done|]).
    intros l InD. specialize (PB _ InD) as [PB|(t & h & Eqh & PV)]; [left|right].
    + intros st Eqst. specialize (PB _ Eqst) as (ss & ? & AREL).
      by exists ss.
    + exists t, h. rewrite -EQtm -EQlm. split; [done|].
      destruct PV as [?|(c' & T' & Eqc' & InT & ?)]; [by left|right].
      exists c', T'. split; [|done].
      have ? : c' ≠ c.
      { intros ?. subst c'. move : Eqc'.
        rewrite lookup_op /= lookup_insert. intros ?%callStateR_exclusive_eq.
        subst T'. by apply not_elem_of_empty in InT. }
      move : Eqc'.
      rewrite 2!lookup_op lookup_insert_ne // lookup_insert_ne //.
  - intros l. setoid_rewrite <-EQlm. by specialize (LINV l).
Qed.
