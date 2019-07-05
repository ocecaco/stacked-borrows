From stbor.lang Require Export defs.

Set Default Proof Using "Type".

Lemma for_each_lookup α l n f α' :
  for_each α l n false f = Some α' →
  (∀ (i: nat) stk, (i < n)%nat → α !! (l +ₗ i) = Some stk → ∃ stk',
    α' !! (l +ₗ i) = Some stk' ∧ f stk = Some stk' ) ∧
  (∀ (i: nat) stk', (i < n)%nat → α' !! (l +ₗ i) = Some stk' → ∃ stk,
    α !! (l +ₗ i) = Some stk ∧ f stk = Some stk') ∧
  (∀ (l': loc), (∀ (i: nat), (i < n)%nat → l' ≠ l +ₗ i) → α' !! l' = α !! l').
Proof.
  revert α. induction n as [|n IH]; intros α; simpl.
  { move => [<-]. split; last split; intros ??; [lia|lia|done]. }
  case (α !! (l +ₗ n)) as [stkn|] eqn:Eqn; [|done] => /=.
  case f as [stkn'|] eqn: Eqn'; [|done] => /= /IH [IH1 [IH2 IH3]].
  split; last split.
  - intros i stk Lt Eqi. case (decide (i = n)) => Eq'; [subst i|].
    + rewrite Eqi in Eqn. simplify_eq.
      rewrite Eqn' IH3; [by rewrite lookup_insert; eexists|].
      move => ?? /shift_loc_inj /Z_of_nat_inj ?. by lia.
    + apply IH1; [lia|]. rewrite lookup_insert_ne; [done|].
      by move => /shift_loc_inj /Z_of_nat_inj ? //.
  - intros i stk Lt Eqi. case (decide (i = n)) => Eq'; [subst i|].
    + move : Eqi. rewrite IH3.
      * rewrite lookup_insert. intros. simplify_eq. naive_solver.
      * move => ?? /shift_loc_inj /Z_of_nat_inj ?. by lia.
    + destruct (IH2 i stk) as [stk0 [Eq0 Eqf0]]; [lia|done|].
      exists stk0. split; [|done]. move : Eq0. rewrite lookup_insert_ne; [done|].
      by move => /shift_loc_inj /Z_of_nat_inj ? //.
  - intros l' Lt. rewrite IH3.
    + rewrite lookup_insert_ne; [done|]. move => Eql'. apply (Lt n); by [lia|].
    + move => ??. apply Lt. lia.
Qed.

Lemma for_each_lookup_case α l n f α' :
  for_each α l n false f = Some α' →
  ∀ l' stk stk', α !! l' = Some stk → α' !! l' = Some stk' →
  stk = stk' ∨ f stk = Some stk' ∧ ∃ i, (0 ≤ i < n) ∧ l' = l +ₗ i.
Proof.
  intros EQ. destruct (for_each_lookup  _ _ _ _ _ EQ) as [EQ1 [EQ2 EQ3]].
  intros l1 stk stk' Eq Eq'.
  case (decide (l1.1 = l.1)) => [Eql|NEql];
    [case (decide (l.2 ≤ l1.2 < l.2 + n)) => [[Le Lt]|NIN]|].
  - have Eql2: l1 = l +ₗ Z.of_nat (Z.to_nat (l1.2 - l.2)). {
      destruct l, l1. move : Eql Le => /= -> ?.
      rewrite /shift_loc /= Z2Nat.id; [|lia]. f_equal. lia. }
    destruct (EQ2 (Z.to_nat (l1.2 - l.2)) stk') as [stk1 [Eq1 Eq2]];
      [rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; lia|by rewrite -Eql2 |].
    rewrite -Eql2 in Eq1. simplify_eq. right. split; [done|].
    exists (Z.to_nat (l1.2 - l.2)). rewrite -Eql2. split; [|done].
    rewrite Z2Nat.id; lia.
  - left. rewrite EQ3 in Eq'; [by simplify_eq|].
    intros i Lt Eq3. apply NIN. rewrite Eq3 /=. lia.
  - left. rewrite EQ3 in Eq'; [by simplify_eq|].
    intros i Lt Eq3. apply NEql. by rewrite Eq3.
Qed.

Lemma init_mem_lookup l n h :
  (∀ (i: nat), (i < n)%nat → init_mem l n h !! (l +ₗ i) = Some ☠%S) ∧
  (∀ (l': loc), (∀ (i: nat), (i < n)%nat → l' ≠ l +ₗ i) →
    init_mem l n h !! l' = h !! l').
Proof.
  revert l h. induction n as [|n IH]; intros l h; simpl.
  { split; intros ??; [lia|done]. }
  destruct (IH (l +ₗ 1) h) as [IH1 IH2].
  split.
  - intros i Lt. destruct i as [|i].
    + rewrite shift_loc_0_nat lookup_insert //.
    + have Eql: l +ₗ S i = (l +ₗ 1) +ₗ i.
      { rewrite shift_loc_assoc. f_equal. lia. }
      rewrite lookup_insert_ne.
      * rewrite Eql. destruct (IH (l +ₗ 1) h) as [IH' _].
        apply IH'; lia.
      * rewrite -{1}(shift_loc_0_nat l). intros ?%shift_loc_inj. lia.
  - intros l' Lt. rewrite lookup_insert_ne.
    + apply IH2. intros i Lt'.
      rewrite (_: (l +ₗ 1) +ₗ i = l +ₗ S i); last first.
      { rewrite shift_loc_assoc. f_equal. lia. }
      apply Lt. lia.
    + specialize (Lt O ltac:(lia)). by rewrite shift_loc_0_nat in Lt.
Qed.

Lemma init_mem_lookup_case l n h :
  ∀ l' s', init_mem l n h !! l' = Some s' →
  h !! l' = Some s' ∧ (∀ i : nat, (i < n)%nat → l' ≠ l +ₗ i) ∨
  ∃ i, (0 ≤ i < n) ∧ l' = l +ₗ i.
Proof.
  destruct (init_mem_lookup l n h) as [EQ1 EQ2].
  intros l1 s1 Eq'.
  case (decide (l1.1 = l.1)) => [Eql|NEql];
    [case (decide (l.2 ≤ l1.2 < l.2 + n)) => [[Le Lt]|NIN]|].
  - have Eql2: l1 = l +ₗ Z.of_nat (Z.to_nat (l1.2 - l.2)). {
      destruct l, l1. move : Eql Le => /= -> ?.
      rewrite /shift_loc /= Z2Nat.id; [|lia]. f_equal. lia. }
    right. rewrite Eql2. eexists; split; [|done].
    rewrite Eql2 /= in Lt. lia.
  - left.
    have ?: ∀ i : nat, (i < n)%nat → l1 ≠ l +ₗ i.
    { intros i Lt Eq3. apply NIN. rewrite Eq3 /=. lia. }
     rewrite EQ2 // in Eq'.
  - left.
    have ?: ∀ i : nat, (i < n)%nat → l1 ≠ l +ₗ i.
    { intros i Lt Eq3. apply NEql. by rewrite Eq3. }
    rewrite EQ2 // in Eq'.
Qed.

Lemma init_mem_lookup_empty l n :
  ∀ l' s', init_mem l n ∅ !! l' = Some s' →
  ∃ i, (0 ≤ i < n) ∧ l' = l +ₗ i.
Proof. move => l' s' /init_mem_lookup_case [[//]|//]. Qed.

Lemma init_stacks_lookup α l n t :
  (∀ (i: nat), (i < n)%nat →
    init_stacks α l n t !! (l +ₗ i) = Some [mkItem Unique t None]) ∧
  (∀ (l': loc), (∀ (i: nat), (i < n)%nat → l' ≠ l +ₗ i) →
    init_stacks α l n t !! l' = α !! l').
Proof.
  revert l α. induction n as [|n IH]; intros l α; simpl.
  { split; intros ??; [lia|done]. }
  destruct (IH (l +ₗ 1) α) as [IH1 IH2].
  split.
  - intros i Lt. destruct i as [|i].
    + rewrite shift_loc_0_nat lookup_insert //.
    + have Eql: l +ₗ S i = (l +ₗ 1) +ₗ i.
      { rewrite shift_loc_assoc. f_equal. lia. }
      rewrite lookup_insert_ne.
      * rewrite Eql. destruct (IH (l +ₗ 1) α) as [IH' _].
        apply IH'; lia.
      * rewrite -{1}(shift_loc_0_nat l). intros ?%shift_loc_inj. lia.
  - intros l' Lt. rewrite lookup_insert_ne.
    + apply IH2. intros i Lt'.
      rewrite (_: (l +ₗ 1) +ₗ i = l +ₗ S i); last first.
      { rewrite shift_loc_assoc. f_equal. lia. }
      apply Lt. lia.
    + specialize (Lt O ltac:(lia)). by rewrite shift_loc_0_nat in Lt.
Qed.

Lemma init_stacks_lookup_case α l n t :
  ∀ l' s', init_stacks α l n t !! l' = Some s' →
  α !! l' = Some s' ∧ (∀ i : nat, (i < n)%nat → l' ≠ l +ₗ i) ∨
  ∃ i, (0 ≤ i < n) ∧ l' = l +ₗ i.
Proof.
  destruct (init_stacks_lookup α l n t) as [EQ1 EQ2].
  intros l1 s1 Eq'.
  case (decide (l1.1 = l.1)) => [Eql|NEql];
    [case (decide (l.2 ≤ l1.2 < l.2 + n)) => [[Le Lt]|NIN]|].
  - have Eql2: l1 = l +ₗ Z.of_nat (Z.to_nat (l1.2 - l.2)). {
      destruct l, l1. move : Eql Le => /= -> ?.
      rewrite /shift_loc /= Z2Nat.id; [|lia]. f_equal. lia. }
    right. rewrite Eql2. eexists; split; [|done].
    rewrite Eql2 /= in Lt. lia.
  - left.
    have ?: ∀ i : nat, (i < n)%nat → l1 ≠ l +ₗ i.
    { intros i Lt Eq3. apply NIN. rewrite Eq3 /=. lia. }
     rewrite EQ2 // in Eq'.
  - left.
    have ?: ∀ i : nat, (i < n)%nat → l1 ≠ l +ₗ i.
    { intros i Lt Eq3. apply NEql. by rewrite Eq3. }
    rewrite EQ2 // in Eq'.
Qed.

Lemma init_stacks_lookup_case_2 α l n t :
  ∀ l' s', α !! l' = Some s' →
  init_stacks α l n t !! l' = Some s' ∧ (∀ i : nat, (i < n)%nat → l' ≠ l +ₗ i) ∨
  ∃ i, (0 ≤ i < n) ∧ l' = l +ₗ i ∧
    init_stacks α l n t !! l' = Some [mkItem Unique t None].
Proof.
  destruct (init_stacks_lookup α l n t) as [EQ1 EQ2].
  intros l1 s1 Eq'.
  case (decide (l1.1 = l.1)) => [Eql|NEql];
    [case (decide (l.2 ≤ l1.2 < l.2 + n)) => [[Le Lt]|NIN]|].
  - have Eql2: l1 = l +ₗ Z.of_nat (Z.to_nat (l1.2 - l.2)). {
      destruct l, l1. move : Eql Le => /= -> ?.
      rewrite /shift_loc /= Z2Nat.id; [|lia]. f_equal. lia. }
    right. rewrite Eql2. rewrite Eql2 /= in Lt.
    eexists; split; last split; [|done|].
    + lia.
    + rewrite EQ1 //. lia.
  - left.
    have ?: ∀ i : nat, (i < n)%nat → l1 ≠ l +ₗ i.
    { intros i Lt Eq3. apply NIN. rewrite Eq3 /=. lia. }
    rewrite EQ2 //.
  - left.
    have ?: ∀ i : nat, (i < n)%nat → l1 ≠ l +ₗ i.
    { intros i Lt Eq3. apply NEql. by rewrite Eq3. }
    rewrite EQ2 //.
Qed.

Lemma for_each_dom α l n f α' :
  for_each α l n false f = Some α' →
  dom (gset loc) α ≡ dom (gset loc) α'.
Proof.
  revert α. induction n as [|n IH]; intros α; [by move => /= [-> //]|].
  simpl. destruct (α !! (l +ₗ n)) eqn:Eq; [|done].
  simpl. case f => stack' /=; [|done]. move => /IH <-.
  symmetry. apply dom_map_insert_is_Some. rewrite Eq. by eexists.
Qed.
