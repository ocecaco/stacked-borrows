From stbor.sim Require Export instance.

Set Default Proof Using "Type".

Definition res_call_empty (c: call_id) : resUR :=
  ((ε, {[c := to_callStateR (csOwned ∅)]}), ε).
Definition res_call_pub (c: call_id) : resUR :=
  ((ε, {[c := to_callStateR csPub]}), ε).

Lemma vs_call_empty_public r c :
  r ⋅ res_call_empty c |==> r ⋅ res_call_pub c.
Proof.
  intros r_f σs σt. rewrite 2!cmra_assoc.
  intros (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  have EQtm: (r_f ⋅ r ⋅ res_call_empty c).(rtm) ≡ (r_f ⋅ r ⋅ res_call_pub c).(rtm) by done.
  have EQlm: (r_f ⋅ r ⋅ res_call_empty c).(rlm) ≡ (r_f ⋅ r ⋅ res_call_pub c).(rlm) by done.
  have UNIQUE: (r_f ⋅ r).(rcm) !! c = None.
  { move : (proj2 (proj1 VALID) c).
    rewrite lookup_op.
    destruct ((r_f ⋅ r).(rcm) !! c) as [cs|] eqn:Eqcs; [|done].
    rewrite Eqcs /res_call_empty /= lookup_insert -Some_op.
    intros ?%exclusive_r; [done|apply _]. }
  have EQO: (r_f ⋅ r ⋅ res_call_empty c).(rcm) !! c ≡ Some $ to_callStateR (csOwned ∅).
  { rewrite lookup_op UNIQUE left_id /= lookup_insert //. }
  split; last split; last split; last split; last split; last split;
    [done|done|..].
  - apply (local_update_discrete_valid_frame _ _ _ VALID).
    rewrite (cmra_comm (r_f ⋅ r)) (cmra_comm _ (res_call_pub _)).
    apply prod_local_update_1, prod_local_update_2.
    rewrite /res_call_pub /= -insert_singleton_op // -insert_singleton_op //.
    rewrite -(insert_insert _ c (Cinr ()) (Cinl (Excl ∅))).
    eapply singleton_local_update; [by rewrite lookup_insert|].
    by apply exclusive_local_update.
  - intros t k h. rewrite -EQtm. intros Eqkh.
    specialize (PINV _ _ _ Eqkh) as [? PINV]. split; [done|].
    intros l s Eqs. rewrite -EQlm.
    by specialize (PINV _ _ Eqs) as [? PINV].
  - intros c' cs'. case (decide (c' = c)) => ?; [subst c'|].
    + rewrite lookup_op UNIQUE left_id /= lookup_insert.
      intros Eq%Some_equiv_inj.
      specialize (CINV _ _ EQO) as [IN _].
      have Lt := state_wf_cid_agree _ WFT _ IN.
      destruct cs' as [[]| |]; try inversion Eq. done.
    + intros EQcs. apply (CINV  c' cs').
      move : EQcs. rewrite lookup_op (lookup_op _ (res_call_empty c).(rcm))
        /rcm /res_call_pub /= lookup_insert_ne // lookup_insert_ne //.
  - destruct SREL as (?&?&?&?& PB). do 4 (split; [done|]).
    intros l InD. rewrite -EQlm. intros SHR.
    specialize (PB _ InD SHR) as [PB|(t & c' & T & h & Eqc' & InT & ?)]; [left|right].
    + intros st Eqst. specialize (PB _ Eqst) as (ss & ? & AREL).
      by exists ss.
    + exists t, c', T, h. rewrite -EQtm. split; [|done].
      have ? : c' ≠ c.
      { intros ?. subst c'. move : Eqc'.
        rewrite lookup_op /= lookup_insert. intros ?%callStateR_exclusive_eq.
        subst T. by apply not_elem_of_empty in InT. }
      move : Eqc'.
      rewrite lookup_op (lookup_op _ (res_call_pub c).(rcm))
        /rcm /res_call_pub /= lookup_insert_ne // lookup_insert_ne //.
  - intros l. setoid_rewrite <-EQlm. by specialize (LINV l).
Qed.
