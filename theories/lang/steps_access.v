From stbor.lang Require Export defs steps_foreach steps_list.

Set Default Proof Using "Type".

Lemma access1_in_stack stk kind t cids n stk' :
   access1 stk kind (Tagged t) cids = Some (n, stk') →
   ∃ it, it ∈ stk ∧ it.(tg) = Tagged t.
Proof.
  rewrite /access1. case find_granting as [gip|] eqn:Eq1; [|done].
  apply fmap_Some in Eq1 as [[i it] [[IN [? Eq]]%list_find_Some EQ]].
  intros ?. exists it. split; [|done]. by eapply elem_of_list_lookup_2.
Qed.

Lemma access1_tagged_sublist stk kind bor cids n stk' :
  access1 stk kind bor cids = Some (n, stk') → tagged_sublist stk' stk.
Proof.
  rewrite /access1. case find_granting as [gip|]; [|done]. simpl.
  destruct kind.
  - case replace_check as [stk1|] eqn:Eq; [|done].
    simpl. intros. simplify_eq.
    rewrite -{2}(take_drop gip.1 stk). apply tagged_sublist_app; [|done].
    move : Eq. by apply replace_check_tagged_sublist.
  - case find_first_write_incompatible as [idx|]; [|done]. simpl.
    case remove_check as [stk1|] eqn:Eq; [|done].
    simpl. intros. simplify_eq.
    rewrite -{2}(take_drop gip.1 stk). apply tagged_sublist_app; [|done].
    move : Eq. by apply remove_check_tagged_sublist.
Qed.

Lemma access1_non_empty stk kind bor cids n stk' :
  access1 stk kind bor cids = Some (n, stk') → stk' ≠ [].
Proof.
  rewrite /access1. case find_granting as [gip|] eqn:Eq1; [|done].
  apply fmap_Some in Eq1 as [[i it] [[IN ?]%list_find_Some EQ]].
  subst gip; simpl.
  have ?: drop i stk ≠ [].
  { move => ND. move : IN. by rewrite -(Nat.add_0_r i) -(lookup_drop) ND /=. }
  destruct kind.
  - case replace_check as [stk1|]; [|done].
    simpl. intros ?. simplify_eq => /app_nil [_ ?]. by subst.
  - case find_first_write_incompatible as [?|]; [|done]. simpl.
    case remove_check as [?|]; [|done].
    simpl. intros ?. simplify_eq => /app_nil [_ ?]. by subst.
Qed.

Lemma for_each_access1 α nxtc l n tg kind α' :
  for_each α l n false
          (λ stk, nstk' ← access1 stk kind tg nxtc; Some nstk'.2) = Some α' →
  ∀ (l: loc) stk', α' !! l = Some stk' → ∃ stk, α !! l = Some stk ∧
    tagged_sublist stk' stk ∧ (stk ≠ [] → stk' ≠ []).
Proof.
  intros EQ. destruct (for_each_lookup  _ _ _ _ _ EQ) as [EQ1 [EQ2 EQ3]].
  intros l1 stk1 Eq1.
  case (decide (l1.1 = l.1)) => [Eql|NEql];
    [case (decide (l.2 ≤ l1.2 < l.2 + n)) => [[Le Lt]|NIN]|].
  - have Eql2: l1 = l +ₗ Z.of_nat (Z.to_nat (l1.2 - l.2)). {
      destruct l, l1. move : Eql Le => /= -> ?.
      rewrite /shift_loc /= Z2Nat.id; [|lia]. f_equal. lia. }
    destruct (EQ2 (Z.to_nat (l1.2 - l.2)) stk1)
      as [stk [Eq [[n1 stk'] [Eq' Eq0]]%bind_Some]];
      [rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; lia|by rewrite -Eql2|].
    exists stk. split; [by rewrite Eql2|]. simplify_eq.
    split; [by eapply access1_tagged_sublist|intros; by eapply access1_non_empty].
  - exists stk1. split; [|done]. rewrite -EQ3; [done|].
    intros i Lt Eq. apply NIN. rewrite Eq /=. lia.
  - exists stk1. split; [|done]. rewrite -EQ3; [done|].
    intros i Lt Eq. apply NEql. by rewrite Eq.
Qed.

Lemma for_each_access1_non_empty α cids l n tg kind α' :
  for_each α l n false
          (λ stk, nstk' ← access1 stk kind tg cids; Some nstk'.2) = Some α' →
  wf_non_empty α → wf_non_empty α'.
Proof.
  move => /for_each_access1 EQ1 WF ?? /EQ1 [? [? [? NE]]]. by eapply NE, WF.
Qed.

Lemma access1_stack_item_tagged_NoDup stk kind bor cids n stk' :
  access1 stk kind bor cids = Some (n, stk') →
  stack_item_tagged_NoDup stk → stack_item_tagged_NoDup stk'.
Proof.
  rewrite /access1. case find_granting as [gip|] eqn:Eq1; [|done].
  apply fmap_Some in Eq1 as [[i it] [[IN ?]%list_find_Some EQ]].
  subst gip; simpl.
  destruct kind.
  - case replace_check as [stk1|] eqn:Eqc ; [|done].
    simpl. intros ?. simplify_eq.
    rewrite -{1}(take_drop n stk). move : Eqc.
    by apply replace_check_stack_item_tagged_NoDup_2.
  - case find_first_write_incompatible as [?|]; [|done]. simpl.
    case remove_check as [?|] eqn:Eqc ; [|done].
    simpl. intros ?. simplify_eq.
    rewrite -{1}(take_drop n stk). move : Eqc.
    apply remove_check_stack_item_tagged_NoDup_2.
Qed.

Lemma for_each_access1_stack_item α nxtc cids nxtp l n tg kind α' :
  for_each α l n false
          (λ stk, nstk' ← access1 stk kind tg cids; Some nstk'.2) = Some α' →
  wf_stack_item α nxtp nxtc → wf_stack_item α' nxtp nxtc.
Proof.
  intros ACC WF l' stk' Eq'.
  destruct (for_each_access1 _ _ _ _ _ _ _ ACC _ _ Eq') as [stk [Eq [SUB NN]]].
  split.
  - move => ? /SUB [? [IN [-> [-> ?]]]]. by apply (proj1 (WF _ _ Eq) _ IN).
  - clear SUB NN.
    destruct (for_each_lookup_case _ _ _ _ _ ACC _ _ _ Eq Eq') as [?|[Eqf ?]].
    { subst. by apply (WF _ _ Eq). }
    destruct (access1 stk kind tg cids) as [[]|] eqn:Eqf'; [|done].
    simpl in Eqf. simplify_eq.
    eapply access1_stack_item_tagged_NoDup; eauto. by apply (WF _ _ Eq).
Qed.

(** Dealloc *)
Lemma for_each_dealloc_lookup α l n f α' :
  for_each α l n true f = Some α' →
  (∀ (i: nat), (i < n)%nat → α' !! (l +ₗ i) = None) ∧
  (∀ (l': loc), (∀ (i: nat), (i < n)%nat → l' ≠ l +ₗ i) → α' !! l' = α !! l').
Proof.
  revert α. induction n as [|n IH]; intros α; simpl.
  { move => [<-]. split; intros ??; by [lia|]. }
  case (α !! (l +ₗ n)) as [stkn|] eqn:Eqn; [|done] => /=.
  case f as [stkn'|] eqn: Eqn'; [|done] => /= /IH [IH1 IH2]. split.
  - intros i Lt. case (decide (i = n)) => Eq'; [subst i|].
    + rewrite IH2; [by apply lookup_delete|].
      move => ?? /shift_loc_inj /Z_of_nat_inj ?. by lia.
    + apply IH1. by lia.
  - intros l' Lt. rewrite IH2.
    + rewrite lookup_delete_ne; [done|]. move => Eql'. apply (Lt n); by [lia|].
    + move => ??. apply Lt. lia.
Qed.

Lemma memory_deallocated_delete' α nxtc l bor n α' (m: nat):
  memory_deallocated α nxtc (l +ₗ m) bor n = Some α' →
  α' = fold_right (λ (i: nat) α, delete (l +ₗ i) α) α (seq m n).
Proof.
  revert α.
  induction n as [|n IHn]; intros α; [by move => [->]|].
  rewrite /memory_deallocated /=.
  case lookup => stack /= ; [|done]. case dealloc1 => stack'; [|done].
  move => /IHn ->. clear. revert m. induction n as [|n IH]; intros m.
  - by rewrite /= shift_loc_0.
  - simpl. f_equal.
    by rewrite shift_loc_assoc -Nat2Z.inj_add -Nat.add_succ_comm Nat2Z.inj_add
               -shift_loc_assoc IH.
Qed.

Lemma memory_deallocated_delete α nxtc l bor n α':
  memory_deallocated α nxtc l bor n = Some α' →
  α' = fold_right (λ (i: nat) α, delete (l +ₗ i) α) α (seq O n).
Proof. intros. eapply memory_deallocated_delete'. rewrite shift_loc_0. by eauto. Qed.
