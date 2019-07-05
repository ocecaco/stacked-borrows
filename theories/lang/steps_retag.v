From stbor.lang Require Export defs steps_foreach steps_list.

Set Default Proof Using "Type".

(** Active protector preserving *)
Definition active_preserving (cids: call_id_stack) (stk stk': stack) :=
  ∀ pm t c, c ∈ cids → mkItem pm t (Some c) ∈ stk → mkItem pm t (Some c) ∈ stk'.

Instance active_preserving_preorder cids : PreOrder (active_preserving cids).
Proof.
  constructor.
  - intros ??. done.
  - intros ??? AS1 AS2 ?????. naive_solver.
Qed.

Lemma active_preserving_app_mono (cids: call_id_stack) (stk1 stk2 stk': stack) :
  active_preserving cids stk1 stk2 →
  active_preserving cids (stk1 ++ stk') (stk2 ++ stk').
Proof.
  intros AS pm t c Inc. rewrite 2!elem_of_app.
  specialize (AS pm t c Inc). set_solver.
Qed.

Lemma remove_check_active_preserving cids stk stk' idx:
  remove_check cids stk idx = Some stk' → active_preserving cids stk stk'.
Proof.
  revert idx.
  induction stk as [|it stk IH]; intros idx; simpl.
  { destruct idx; [|done]. intros ??. by simplify_eq. }
  destruct idx as [|idx]; [intros ??; by simplify_eq|].
  case check_protector eqn:Eq; [|done].
  move => /IH AS pm t c IN /elem_of_cons [?|]; [|by apply AS].
  subst it. exfalso. move : Eq.
  by rewrite /check_protector /= /is_active bool_decide_true //.
Qed.

Lemma replace_check'_active_preserving cids acc stk stk':
  replace_check' cids acc stk = Some stk' → active_preserving cids stk stk'.
Proof.
  revert acc.
  induction stk as [|it stk IH]; intros acc; simpl.
  { intros. simplify_eq. by intros ?????%not_elem_of_nil. }
  case decide => ?; [case check_protector eqn:Eq; [|done]|].
  - move => /IH AS pm t c IN /elem_of_cons [?|]; [|by apply AS].
    subst it. exfalso. move : Eq.
    by rewrite /check_protector /= /is_active bool_decide_true //.
  - move => Eq pm t c IN /elem_of_cons [?|].
    + apply (replace_check'_acc_result _ _ _ _ Eq), elem_of_app. right.
      by apply elem_of_list_singleton.
    + by apply (IH _ Eq).
Qed.

Lemma replace_check_active_preserving cids stk stk':
  replace_check cids stk = Some stk' → active_preserving cids stk stk'.
Proof. by apply replace_check'_active_preserving. Qed.

Lemma access1_active_preserving stk stk' kind tg cids n:
  access1 stk kind tg cids = Some (n, stk') →
  active_preserving cids stk stk'.
Proof.
  rewrite /access1. case find_granting as [gip|]; [|done]. simpl.
  destruct kind.
  - case replace_check as [stk1|] eqn:Eq; [|done].
    simpl. intros. simplify_eq.
    rewrite -{1}(take_drop gip.1 stk).
    by apply active_preserving_app_mono, replace_check_active_preserving.
  - case find_first_write_incompatible as [idx|]; [|done]. simpl.
    case remove_check as [stk1|] eqn:Eq; [|done].
    simpl. intros. simplify_eq.
    rewrite -{1}(take_drop gip.1 stk).
    by eapply active_preserving_app_mono, remove_check_active_preserving.
Qed.

Lemma for_each_access1_active_preserving α cids l n tg kind α':
  for_each α l n false
          (λ stk, nstk' ← access1 stk kind tg cids; Some nstk'.2) = Some α' →
  ∀ l stk, α !! l = Some stk →
  ∃ stk', α' !! l = Some stk' ∧ active_preserving cids stk stk'.
Proof.
  intros EQ. destruct (for_each_lookup  _ _ _ _ _ EQ) as [EQ1 [EQ2 EQ3]].
  intros l1 stk1 Eq1.
  case (decide (l1.1 = l.1)) => [Eql|NEql];
    [case (decide (l.2 ≤ l1.2 < l.2 + n)) => [[Le Lt]|NIN]|].
  - have Eql2: l1 = l +ₗ Z.of_nat (Z.to_nat (l1.2 - l.2)). {
      destruct l, l1. move : Eql Le => /= -> ?.
      rewrite /shift_loc /= Z2Nat.id; [|lia]. f_equal. lia. }
    destruct (EQ1 (Z.to_nat (l1.2 - l.2)) stk1)
      as [stk [Eq [[n1 stk'] [Eq' Eq0]]%bind_Some]];
      [rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; lia|by rewrite -Eql2|].
    exists stk. rewrite -Eql2 in Eq. split; [done|]. simpl in Eq0. simplify_eq.
    eapply access1_active_preserving; eauto.
  - rewrite EQ3; [naive_solver|].
    intros i Lt Eq. apply NIN. rewrite Eq /=. lia.
  - rewrite EQ3; [naive_solver|].
    intros i Lt Eq. apply NEql. by rewrite Eq.
Qed.


(** Head preserving *)
Definition is_stack_head (it: item) (stk: stack) :=
  ∃ stk', stk = it :: stk'.

Lemma sublist_head_preserving t it it' stk stk' :
  stk' `sublist_of` stk →
  it'.(tg) = Tagged t → it.(tg) = Tagged t →
  it' ∈ stk' →
  stack_item_tagged_NoDup stk →
  is_stack_head it stk →
  is_stack_head it stk'.
Proof.
  intros SUB Eqt' Eqt In' ND.
  induction SUB as [|???? IH|???? IH]; [done|..]; intros [stk1 ?]; simplify_eq;
    [by eexists|].
  exfalso. move : ND.
  rewrite /stack_item_tagged_NoDup filter_cons decide_True;
    last by rewrite /is_tagged Eqt.
  rewrite fmap_cons NoDup_cons. intros [NI ?].
  apply NI, elem_of_list_fmap. exists it'. split; [rewrite Eqt' Eqt //|].
  apply elem_of_list_filter. split. by rewrite /is_tagged Eqt'. by rewrite <-SUB.
Qed.

Lemma replace_check'_head_preserving stk stk' acc stk0 cids pm pm' t opro:
  stack_item_tagged_NoDup (acc ++ stk ++ stk0) →
  pm ≠ Disabled →
  mkItem pm (Tagged t) opro ∈ (stk' ++ stk0) →
  replace_check' cids acc stk = Some stk' →
  is_stack_head (mkItem pm' (Tagged t) opro) (acc ++ stk ++ stk0) →
  is_stack_head (mkItem pm' (Tagged t) opro) (stk' ++ stk0).
Proof.
  intros ND NDIS IN. revert acc ND.
  induction stk as [|it stk IH]; simpl; intros acc ND.
  { intros ?. by simplify_eq. }
  case decide => ?; [case check_protector; [|done]|];
    [|move => /IH; rewrite -(app_assoc acc [it] (stk ++ stk0)); naive_solver].
  move => RC.
  rewrite (app_assoc acc [it] (stk ++ stk0)).
  have ND3: stack_item_tagged_NoDup
    ((acc ++ [mkItem Disabled it.(tg) it.(protector)]) ++ stk ++ stk0).
  { move : ND. clear.
    rewrite (app_assoc acc [it]) 2!(Permutation_app_comm acc) -2!app_assoc.
    rewrite /stack_item_tagged_NoDup 2!filter_cons /=.
    case decide => ?; [rewrite decide_True //|rewrite decide_False //]. }
  intros HD. apply (IH _ ND3 RC). clear IH. move : HD.
  destruct acc as [|it1 acc]; last first.
  { simpl in *. move => [? Eq]. inversion Eq. simplify_eq. by eexists. }
  simpl. intros [stk2 Eq]. exfalso. simplify_eq; simpl in *.
  have IN1:= (replace_check'_acc_result _ _ _ _ RC).
  have IN': mkItem Disabled (Tagged t) opro ∈ stk' ++ stk0 by set_solver. clear IN1.
  have ND4 := replace_check'_stack_item_tagged_NoDup_2 _ _ _ _ _ RC ND3.
  have EQ := stack_item_tagged_NoDup_eq _ _ _ _ ND4 IN IN' eq_refl eq_refl.
  by inversion EQ.
Qed.

Lemma replace_check_head_preserving stk stk' stk0 cids pm pm' t opro:
  stack_item_tagged_NoDup (stk ++ stk0) →
  pm ≠ Disabled →
  mkItem pm (Tagged t) opro ∈ (stk' ++ stk0) →
  replace_check cids stk = Some stk' →
  is_stack_head (mkItem pm' (Tagged t) opro) (stk ++ stk0) →
  is_stack_head (mkItem pm' (Tagged t) opro) (stk' ++ stk0).
Proof. intros. eapply replace_check'_head_preserving; eauto. done. Qed.

Lemma access1_head_preserving stk stk' kind tg cids n pm pm' t opro:
  stack_item_tagged_NoDup stk →
  pm ≠ Disabled →
  mkItem pm (Tagged t) opro ∈ stk' →
  access1 stk kind tg cids = Some (n, stk') →
  is_stack_head (mkItem pm' (Tagged t) opro) stk →
  is_stack_head (mkItem pm' (Tagged t) opro) stk'.
Proof.
  intros ND NDIS IN.
  rewrite /access1. case find_granting as [gip|]; [|done]. simpl.
  destruct kind.
  - case replace_check as [stk1|] eqn:Eq; [|done].
    simpl. intros ?. simplify_eq.
    rewrite -{1}(take_drop gip.1 stk). intros HD.
    rewrite -{1}(take_drop gip.1 stk) in ND.
    eapply replace_check_head_preserving; eauto.
  - case find_first_write_incompatible as [idx|]; [|done]. simpl.
    case remove_check as [stk1|] eqn:Eq; [|done].
    simpl. intros ?. simplify_eq.
    have SUB: stk1 ++ drop gip.1 stk `sublist_of` stk.
    { rewrite -{2}(take_drop gip.1 stk). apply sublist_app; [|done].
      move : Eq. apply remove_check_sublist. }
    eapply sublist_head_preserving; eauto. done.
Qed.


(** active_SRO preserving *)
Lemma active_SRO_cons_elem_of t it stk :
  t ∈ active_SRO (it :: stk) ↔
  it.(perm) = SharedReadOnly ∧ (it.(tg) = Tagged t ∨ t ∈ active_SRO stk).
Proof.
  simpl. destruct it.(perm); [set_solver..| |set_solver].
  case tg => [?|]; [rewrite elem_of_union elem_of_singleton|]; naive_solver.
Qed.

Lemma sublist_active_SRO_preserving t it stk stk' :
  stk' `sublist_of` stk →
  it.(tg) = Tagged t →
  it ∈ stk' →
  stack_item_tagged_NoDup stk →
  t ∈ active_SRO stk → t ∈ active_SRO stk'.
Proof.
  intros SUB Eqt In' ND.
  induction SUB as [|it1 stk1 stk2 ? IH|it1 stk1 stk2 ? IH]; [done|..].
  - intros [? Eq]%active_SRO_cons_elem_of. apply active_SRO_cons_elem_of.
    split; [done|]. destruct Eq as [?|Eq]; [by left|].
    apply elem_of_cons in In' as [?|In'].
    + subst it. rewrite Eqt. by left.
    + right. apply IH; auto. by eapply stack_item_tagged_NoDup_cons_1.
  - intros [? Eq]%active_SRO_cons_elem_of.
    destruct Eq as [Eq|In2].
    + exfalso. move : ND.
      rewrite /stack_item_tagged_NoDup filter_cons decide_True;
        last by rewrite /is_tagged Eq.
      rewrite fmap_cons NoDup_cons. intros [NI ?].
      apply NI, elem_of_list_fmap. exists it. split; [rewrite Eqt Eq //|].
      apply elem_of_list_filter. split. by rewrite /is_tagged Eqt. by rewrite <-SUB.
    + apply IH; auto. by eapply stack_item_tagged_NoDup_cons_1.
Qed.

Lemma active_SRO_tag_eq_elem_of stk1 stk2 t :
  fmap tg stk1 = fmap tg stk2 →
  Forall2 (λ pm1 pm2, pm1 = SharedReadOnly → pm2 = SharedReadOnly)
          (fmap perm stk1) (fmap perm stk2) →
  t ∈ active_SRO stk1 → t ∈ active_SRO stk2.
Proof.
  revert stk2.
  induction stk1 as [|it stk1 IH]; intros stk2; [simpl; set_solver|].
  destruct stk2 as [|it2 stk2]; [naive_solver|].
  rewrite 4!fmap_cons. inversion 1 as [Eqt].
  inversion 1 as [|???? Eq1 FA]; subst. rewrite 2!active_SRO_cons_elem_of.
  intros [EqSRO Eq]. specialize (Eq1 EqSRO). split; [done|].
  destruct Eq as [Eq|In1].
  - rewrite -Eqt. by left.
  - right. by apply IH.
Qed.

Lemma replace_check'_active_SRO_preserving cids acc stk stk' stk0 t it:
  it.(tg) = Tagged t →
  it ∈ stk' ++ stk0 →
  replace_check' cids acc stk = Some stk' →
  stack_item_tagged_NoDup (acc ++ stk ++ stk0) →
  t ∈ active_SRO (acc ++ stk ++ stk0) → t ∈ active_SRO (stk' ++ stk0).
Proof.
  intros Eqt IN. revert acc.
  induction stk as [|it1 stk IH]; simpl; intros acc.
  { intros ?. by simplify_eq. }
  case decide => [EqU|?]; [case check_protector; [|done]|];
    [|move => /IH; rewrite -(app_assoc acc [it1] (stk ++ stk0)); naive_solver].
  move => RC ND.
  rewrite (app_assoc acc [it1] (stk ++ stk0)).
  have ND3: stack_item_tagged_NoDup
    ((acc ++ [mkItem Disabled it1.(tg) it1.(protector)]) ++ stk ++ stk0).
  { move : ND. clear.
    rewrite (app_assoc acc [it1]) 2!(Permutation_app_comm acc) -2!app_assoc.
    rewrite /stack_item_tagged_NoDup 2!filter_cons /=.
    case decide => ?; [rewrite decide_True //|rewrite decide_False //]. }
  intros HD. apply (IH _ RC ND3). clear IH. move : HD.
  apply active_SRO_tag_eq_elem_of.
  - by rewrite !fmap_app /=.
  - rewrite 2!(fmap_app _ _ (stk ++ stk0)).
    apply Forall2_app; [rewrite 2!fmap_app; apply Forall2_app|].
    + by apply Forall_Forall2, Forall_forall.
    + apply Forall2_cons; [|constructor]. by rewrite EqU.
    + by apply Forall_Forall2, Forall_forall.
Qed.

Lemma replace_check_active_SRO_preserving cids stk stk' stk0 it t:
  it.(tg) = Tagged t →
  it ∈ stk' ++ stk0 →
  replace_check cids stk = Some stk' →
  stack_item_tagged_NoDup (stk ++ stk0) →
  t ∈ active_SRO (stk ++ stk0) → t ∈ active_SRO (stk' ++ stk0).
Proof. by apply replace_check'_active_SRO_preserving. Qed.

Lemma access1_active_SRO_preserving stk stk' kind tg cids n pm t opro:
  stack_item_tagged_NoDup stk →
  mkItem pm (Tagged t) opro ∈ stk' →
  access1 stk kind tg cids = Some (n, stk') →
  t ∈ active_SRO stk → t ∈ active_SRO stk'.
Proof.
  intros ND IN.
  rewrite /access1. case find_granting as [gip|]; [|done]. simpl.
  destruct kind.
  - case replace_check as [stk1|] eqn:Eq; [|done].
    simpl. intros ?. simplify_eq.
    rewrite -{1}(take_drop gip.1 stk). intros HD.
    rewrite -{1}(take_drop gip.1 stk) in ND.
    eapply replace_check_active_SRO_preserving; eauto. done.
  - case find_first_write_incompatible as [idx|]; [|done]. simpl.
    case remove_check as [stk1|] eqn:Eq; [|done].
    simpl. intros ?. simplify_eq.
    have SUB: stk1 ++ drop gip.1 stk `sublist_of` stk.
    { rewrite -{2}(take_drop gip.1 stk). apply sublist_app; [|done].
      move : Eq. apply remove_check_sublist. }
    eapply sublist_active_SRO_preserving; eauto. done.
Qed.

(** Removing incompatible items *)
Lemma find_granting_incompatible_head stk kind t ti idx pm pmi oproi
  (HD: is_stack_head (mkItem pmi (Tagged ti) oproi) stk)
  (NEQ: t ≠ ti) :
  find_granting stk kind (Tagged t) = Some (idx, pm) →
  is_stack_head (mkItem pmi (Tagged ti) oproi) (take idx stk).
Proof.
  destruct HD as [stk' Eqi]. rewrite Eqi.
  rewrite /find_granting /= decide_False; last (intros [_ Eq]; by inversion Eq).
  case list_find => [[idx' pm'] /=|//]. intros . simplify_eq. simpl.
  by eexists.
Qed.

Lemma find_first_write_incompatible_head stk pm idx t opro pmi
  (HD: is_stack_head (mkItem pmi t opro) stk)
  (NSRW: pmi ≠ SharedReadWrite) :
  find_first_write_incompatible stk pm = Some idx → (0 < idx)%nat.
Proof.
  set it := (mkItem pmi t opro).
  destruct HD as [stk' Eqi]. rewrite Eqi.
  destruct pm; [..|done|done]; simpl.
  - intros. simplify_eq. lia.
  - rewrite reverse_cons.
    destruct (list_find_elem_of (λ it, it.(perm) ≠ SharedReadWrite)
                (reverse stk' ++ [it]) it) as [[id fnd] Eqf]; [set_solver|done|].
    rewrite Eqf.
    intros. simplify_eq. apply list_find_Some in Eqf as [Eqi ?].
    apply lookup_lt_Some in Eqi.
    rewrite app_length /= reverse_length Nat.add_1_r in Eqi. lia.
Qed.

Lemma remove_check_incompatible_items cids stk stk' stk0 n it i t
  (ND: stack_item_tagged_NoDup (stk ++ stk0)) :
  it.(tg) = Tagged t → stk !! i = Some it → (i < n)%nat →
  remove_check cids stk n = Some stk' →
  ∀ it', it'.(tg) = Tagged t → it' ∈ (stk' ++ stk0) → False.
Proof.
  intros Eqt. revert i stk stk0 ND.
  induction n as [|n IH]; simpl; intros i stk stk0 ND Eqit Lt; [lia|].
  destruct stk as [|it' stk]; [done|]. simpl.
  case check_protector; [|done].
  destruct i as [|i].
  - simpl in Eqit. simplify_eq.
    intros SUB%remove_check_sublist it' Eq' IN.
    have SUB': stk' ++ stk0 `sublist_of` stk ++ stk0 by apply sublist_app.
    rewrite -> SUB' in IN.
    clear -ND Eqt Eq' IN.
    move : ND.
    rewrite /stack_item_tagged_NoDup filter_cons decide_True;
            [|by rewrite /is_tagged Eqt].
    rewrite fmap_cons NoDup_cons Eqt -Eq'.
    intros [IN' _]. apply IN'. apply elem_of_list_fmap.
    exists it'. split; [done|]. apply elem_of_list_filter. by rewrite /is_tagged Eq'.
  - apply (IH i); [|done|lia]. by apply stack_item_tagged_NoDup_cons_1 in ND.
Qed.

Lemma access1_write_remove_incompatible_head stk t ti cids n stk'
  (ND: stack_item_tagged_NoDup stk) :
  (∃ oproi, is_stack_head (mkItem Unique (Tagged ti) oproi) stk) →
  access1 stk AccessWrite (Tagged t) cids = Some (n, stk') →
  t ≠ ti →
  ∀ pm opro, (mkItem pm (Tagged ti) opro) ∈ stk' → False.
Proof.
  intros HD. rewrite /access1.
  case find_granting as [[n' pm']|] eqn:GRANT; [|done]. simpl.
  case find_first_write_incompatible as [idx|] eqn:INC; [|done]. simpl.
  case remove_check as [stk1|] eqn:Eq; [|done].
  simpl. intros ?. simplify_eq.
  intros NEQ. destruct HD as [oproi HD].
  have HD' := find_granting_incompatible_head _ _ _ _ _ _ _ _ HD NEQ GRANT.
  have Gt0 := find_first_write_incompatible_head _ _ _ _ _ _ HD' (ltac:(done)) INC.
  rewrite -{1}(take_drop n stk) in ND.
  intros pm opro.
  have EQH : take n stk !! 0%nat = Some (mkItem Unique (Tagged ti) oproi).
  { destruct HD' as [? Eq']. by rewrite Eq'. }
  eapply (remove_check_incompatible_items _ _ _ _ idx
            (mkItem Unique (Tagged ti) oproi) O ti ND); done.
Qed.

Lemma active_SRO_elem_of t stk :
  t ∈ active_SRO stk → ∃ i it, stk !! i = Some it ∧ it.(tg) = Tagged t ∧
  it.(perm) = SharedReadOnly ∧
  ∀ j jt, (j < i)%nat → stk !! j = Some jt → jt.(perm) = SharedReadOnly.
Proof.
  induction stk as [|it' stk IH]; simpl; [set_solver|].
  destruct it'.(perm) eqn:Eqp; [set_solver..| |set_solver].
  destruct it'.(tg) eqn:Eqt;
    [rewrite elem_of_union elem_of_singleton; intros [?|Eq]; [subst|]|].
  - exists O, it'. repeat split; [done..|intros; lia].
  - destruct (IH Eq) as (i & it1 & ? & ? & ? & HL).
    exists (S i), it1. repeat split; [done..|].
    intros j jt Lt. destruct j; simpl.
    + intros. by simplify_eq.
    + apply HL. lia.
  - intros Eq. destruct (IH Eq) as (i & it1 & ? & ? & ? & HL).
    exists (S i), it1. repeat split; [done..|].
    intros j jt Lt. destruct j; simpl.
    + intros. by simplify_eq.
    + apply HL. lia.
Qed.

Lemma find_granting_incompatible_active_SRO stk t ti idx pm
  (HD: ti ∈ active_SRO stk) :
  find_granting stk AccessWrite (Tagged t) = Some (idx, pm) →
  ti ∈ active_SRO (take idx stk).
Proof.
  revert idx. induction stk as [|it stk IH]; simpl; intros idx; [set_solver|].
  move : HD. rewrite /find_granting /=.
  destruct it.(perm) eqn:Eqp; [set_solver..| |set_solver].
  rewrite decide_False; last (intros [PM _]; by rewrite Eqp in PM).
  destruct (list_find (matched_grant AccessWrite (Tagged t)) stk)
    as [[n' pm']|] eqn:Eql; [|done].
  simpl. intros IN ?. simplify_eq. rewrite /= Eqp. move : IN.
  destruct it.(tg) eqn:Eqt; simpl;
    [rewrite elem_of_union elem_of_singleton; intros [|IN]; [subst|]|]; simpl.
  - set_solver.
  - rewrite elem_of_union. right. apply IH. done. by rewrite /find_granting Eql.
  - intros ?. apply IH. done. by rewrite /find_granting Eql.
Qed.

Lemma find_first_write_incompatible_active_SRO stk pm idx :
  find_first_write_incompatible stk pm = Some idx →
  ∀ t, t ∈ active_SRO stk → ∃ i it, stk !! i = Some it ∧
    it.(tg) = Tagged t ∧ (i < idx)%nat.
Proof.
  intros EF t IN.
  destruct (active_SRO_elem_of _ _ IN) as (i1 & it1 & Eqit1 & Eqt1 & Eqp1 & HL1).
  move  : EF.
  destruct pm; [| |done..].
  { simpl. intros. simplify_eq. exists i1, it1.
    repeat split; [done..|]. by eapply lookup_lt_Some. }
  simpl.
  destruct (list_find_elem_of (λ it, it.(perm) ≠ SharedReadWrite) (reverse stk) it1)
    as [[n1 pm1] Eqpm1].
  { rewrite elem_of_reverse. by eapply elem_of_list_lookup_2. }
  { by rewrite Eqp1. }
  rewrite Eqpm1. intros. simplify_eq.
  exists i1, it1. repeat split; [done..|].
  apply list_find_Some_not_earlier in Eqpm1 as (Eqrv & Eqpmv & HLv).
  case (decide (i1 + n1 < length stk)%nat) => [?|]; [lia|].
  rewrite Nat.nlt_ge => GE. exfalso.
  destruct (reserve_lookup _ _ _ Eqit1) as (j & Eqj & Eql).
  have Lt: (j < n1)%nat by lia.
  specialize (HLv _ _ Lt Eqj). rewrite Eqp1 in HLv. by apply HLv.
Qed.

Lemma access1_write_remove_incompatible_active_SRO stk t ti cids n stk'
  (ND: stack_item_tagged_NoDup stk) :
  (ti ∈ active_SRO stk) →
  access1 stk AccessWrite (Tagged t) cids = Some (n, stk') →
  ∀ pm opro, (mkItem pm (Tagged ti) opro) ∈ stk' → False.
Proof.
  intros HD. rewrite /access1.
  case find_granting as [[n' pm']|] eqn:GRANT; [|done]. simpl.
  case find_first_write_incompatible as [idx|] eqn:INC; [|done]. simpl.
  case remove_check as [stk1|] eqn:Eq; [|done].
  simpl. intros ?. simplify_eq.
  intros NEQ.
  have HD' := find_granting_incompatible_active_SRO _ _ _ _ _ HD GRANT.
  destruct (find_first_write_incompatible_active_SRO _ _ _ INC _ HD')
    as (i & it & Eqi & Eqt & Lt).
  rewrite -{1}(take_drop n stk) in ND. intros ?.
  eapply (remove_check_incompatible_items _ _ _ _ idx it i ti ND); eauto.
Qed.
