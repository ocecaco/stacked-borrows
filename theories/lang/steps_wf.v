From stbor.lang Require Import helpers.
From stbor.lang Require Export defs.

Set Default Proof Using "Type".

(** Steps preserve wellformedness *)

Lemma init_mem_foldr' l n h (m: nat):
  init_mem (l +ₗ m) n h =
  fold_right (λ (i: nat) hi, <[(l +ₗ i):=☠%S]> hi) h (seq m n).
Proof.
  revert m. induction n as [|n IHn]; intros m; [done|]. simpl. f_equal.
  by rewrite shift_loc_assoc -(Nat2Z.inj_add m 1) Nat.add_1_r IHn.
Qed.
Lemma init_mem_foldr l n h:
  init_mem l n h =
  fold_right (λ (i: nat) hi, <[(l +ₗ i):=☠%S]> hi) h (seq 0 n).
Proof. by rewrite -init_mem_foldr' shift_loc_0. Qed.

Lemma free_mem_foldr' l n h (m: nat):
  free_mem (l +ₗ m) n h =
  fold_right (λ (i: nat) hi, delete (l +ₗ i) hi) h (seq m n).
Proof.
  revert m. induction n as [|n IHn]; intros m; [done|]. simpl. f_equal.
  by rewrite shift_loc_assoc -(Nat2Z.inj_add m 1) Nat.add_1_r IHn.
Qed.
Lemma free_mem_foldr l n h:
  free_mem l n h =
  fold_right (λ (i: nat) hi, delete (l +ₗ i) hi) h (seq 0 n).
Proof. by rewrite -free_mem_foldr' shift_loc_0. Qed.

Lemma init_stacks_foldr' α l n si (m: nat):
  init_stacks α (l +ₗ m) n si =
  fold_right (λ (i: nat) hi, <[(l +ₗ i):=[mkItem Unique si None]]> hi) α (seq m n).
Proof.
  revert m. induction n as [|n IHn]; intros m; [done|]. simpl. f_equal.
  by rewrite shift_loc_assoc -(Nat2Z.inj_add m 1) Nat.add_1_r IHn.
Qed.
Lemma init_stacks_foldr α l n si:
  init_stacks α l n si =
  fold_right (λ (i: nat) hi, <[(l +ₗ i):=[mkItem Unique si None]]> hi) α (seq 0 n).
Proof. by rewrite -init_stacks_foldr' shift_loc_0. Qed.

Lemma wf_stack_item_mono α :
  Proper ((≤)%nat ==> (≤)%nat ==> impl) (wf_stack_item α).
Proof.
  move=> ?? Le1 ? ? Le2 WF ?? /WF [Hf ND]. split; [|done].
  move => ? /Hf [TG1 TG2]. split.
  - move : TG1. case tg => [?|]; [lia|done].
  - move : TG2. case protector => [?|]; [lia|done].
Qed.

Lemma wf_mem_tag_mono h :
  Proper ((≤)%nat ==> impl) (wf_mem_tag h).
Proof. move => ??? WF ??? /WF /=. lia. Qed.

(** NoDup for tagged item *)
Lemma stack_item_tagged_NoDup_singleton it:
  stack_item_tagged_NoDup [it].
Proof.
  rewrite /stack_item_tagged_NoDup filter_cons filter_nil.
  case decide => ? /=. apply NoDup_singleton. apply NoDup_nil_2.
Qed.

(** Alloc *)
Lemma alloc_step_wf (σ σ': state) e e' h0 l bor T:
  mem_expr_step σ.(shp) e (AllocEvt l bor T) h0 e' →
  bor_step h0 σ.(sst) σ.(scs) σ.(snp) σ.(snc)
                    (AllocEvt l bor T)
                  σ'.(shp) σ'.(sst) σ'.(scs) σ'.(snp) σ'.(snc) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α cids nxtp nxtc].
  destruct σ' as [h' α' cids' nxtp' nxtc']. simpl.
  intros BS IS WF. inversion BS. clear BS. simplify_eq.
  destruct (tsize T) eqn:Eqs.
  - inversion IS; clear IS; simplify_eq; constructor; simpl;
      try rewrite Eqs /=; try by apply WF.
    + eapply wf_mem_tag_mono; [|by apply WF]. simpl; lia.
    + eapply wf_stack_item_mono; [..|by apply WF]; [simpl; lia|done].
  - inversion IS; clear IS; simplify_eq; constructor; cbn -[init_mem].
    + rewrite Eqs init_stacks_foldr init_mem_foldr.
      apply foldr_gmap_insert_dom, WF.
    + intros ?? bor. rewrite init_mem_foldr.
      intros [|Eq]%foldr_gmap_insert_lookup; [done|].
      move : (state_wf_mem_tag _ WF _ _ _ Eq). destruct bor; simpl; lia.
    + intros ??. rewrite init_stacks_foldr.
      intros [->|Eq]%foldr_gmap_insert_lookup; split.
      * intros si ->%elem_of_list_singleton. simpl. split; [lia|done].
      * apply stack_item_tagged_NoDup_singleton.
      * move => si /(proj1 (state_wf_stack_item _ WF _ _ Eq)) /= [Lt ?].
        split; [|done]. destruct si.(tg); [simpl; lia|done..].
      * apply (state_wf_stack_item _ WF _ _ Eq).
    + intros ??. rewrite init_stacks_foldr.
      intros [->|Eq]%foldr_gmap_insert_lookup; [done|].
      by apply (state_wf_non_empty _ WF _ _ Eq).
    + apply WF.
    + apply WF.
    (* + intros ??. rewrite init_stacks_foldr.
      intros [->|Eq]%foldr_gmap_insert_lookup; [by apply NoDup_singleton|].
      by apply (state_wf_no_dup _ WF _ _ Eq). *)
Qed.

(** Dealloc *)
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

Lemma dealloc_step_wf σ σ' e e' h0 l bor T :
  mem_expr_step σ.(shp) e (DeallocEvt l bor T) h0 e' →
  bor_step h0 σ.(sst) σ.(scs) σ.(snp) σ.(snc)
                    (DeallocEvt l bor T)
                  σ'.(shp) σ'.(sst) σ'.(scs) σ'.(snp) σ'.(snc) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α cids nxtp nxtc].
  destruct σ' as [h' α' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  rewrite (memory_deallocated_delete α cids' l bor (tsize T) α'); [|done].
  constructor; simpl.
  - rewrite free_mem_foldr. apply foldr_gmap_delete_dom, WF.
  - intros ???. rewrite free_mem_foldr.
    intros Eq%foldr_gmap_delete_lookup.
    apply (state_wf_mem_tag _ WF _ _ _ Eq).
  - intros ?? Eq%foldr_gmap_delete_lookup.
    apply (state_wf_stack_item _ WF _ _ Eq).
  - intros ?? Eq%foldr_gmap_delete_lookup.
    apply (state_wf_non_empty _ WF _ _ Eq).
  - apply WF.
  - apply WF.
  (* - intros ?? Eq%foldr_gmap_delete_lookup.
    apply (state_wf_no_dup _ WF _ _ Eq). *)
Qed.

(** Copy *)
Lemma for_each_dom α l n f α' :
  for_each α l n false f = Some α' →
  dom (gset loc) α ≡ dom (gset loc) α'.
Proof.
  revert α. induction n as [|n IH]; intros α; [by move => /= [-> //]|].
  simpl. destruct (α !! (l +ₗ n)) eqn:Eq; [|done].
  simpl. case f => stack' /=; [|done]. move => /IH <-.
  symmetry. apply dom_map_insert_is_Some. rewrite Eq. by eexists.
Qed.

Definition tagged_sublist (stk1 stk2: stack) :=
  ∀ it1, it1 ∈ stk1 → ∃ it2,
  it2 ∈ stk2 ∧ it1.(tg) = it2.(tg) ∧ it1.(protector) = it2.(protector).
Instance tagged_sublist_preorder : PreOrder tagged_sublist.
Proof.
  constructor.
  - intros ??. naive_solver.
  - move => ??? H1 H2 ? /H1 [? [/H2 ? [-> ->]]]. naive_solver.
Qed.

Instance tagged_sublist_proper stk : Proper ((⊆) ==> impl) (tagged_sublist stk).
Proof. move => ?? SUB H1 ? /H1 [? [/SUB ? ?]]. naive_solver. Qed.

Lemma tagged_sublist_app l1 l2 k1 k2 :
  tagged_sublist l1 l2 → tagged_sublist k1 k2 →
  tagged_sublist (l1 ++ k1) (l2 ++ k2).
Proof.
  move => H1 H2 it. setoid_rewrite elem_of_app.
  move => [/H1|/H2]; naive_solver.
Qed.

Lemma remove_check_tagged_sublist cids stk stk' idx:
  remove_check cids stk idx = Some stk' → tagged_sublist stk' stk.
Proof.
  revert stk' idx.
  induction stk as [|it stk IH]; intros stk' idx; simpl.
  { destruct idx; [|done]. intros. by simplify_eq. }
  destruct idx as [|idx]; [intros; by simplify_eq|].
  case check_protector eqn:Eq; [|done].
  move => /IH. apply tagged_sublist_proper. set_solver.
Qed.

Lemma replace_check'_tagged_sublist cids acc stk stk':
  replace_check' cids acc stk = Some stk' → tagged_sublist stk' (acc ++ stk).
Proof.
  revert acc stk'.
  induction stk as [|it stk IH]; intros acc stk'; simpl.
  { intros. simplify_eq. by rewrite app_nil_r. }
  case decide => ?; [case check_protector; [|done]|];
    move => /IH; [|by rewrite -app_assoc].
  move => H1 it1 /H1 [it2 [IN2 [Eq1 Eq2]]].
  setoid_rewrite elem_of_app. setoid_rewrite elem_of_cons.
  move : IN2 => /elem_of_app [/elem_of_app [?|/elem_of_list_singleton Eq]|?];
    [naive_solver| |naive_solver].
  subst it2. exists it. naive_solver.
Qed.

Lemma replace_check_tagged_sublist cids stk stk':
  replace_check cids stk = Some stk' → tagged_sublist stk' stk.
Proof. move => /replace_check'_tagged_sublist. by rewrite app_nil_l. Qed.

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
  revert stk' idx.
  induction stk as [|it stk IH]; intros stk' idx; simpl.
  { destruct idx; [|done]. intros ??. by simplify_eq. }
  destruct idx as [|idx]; [intros ??; by simplify_eq|].
  case check_protector eqn:Eq; [|done].
  move => /IH AS pm t c IN /elem_of_cons [?|]; [|by apply AS].
  subst it. exfalso. move : Eq.
  by rewrite /check_protector /= /is_active bool_decide_true //.
Qed.

Lemma replace_check'_acc_result cids acc stk stk' :
  replace_check' cids acc stk = Some stk' → acc ⊆ stk'.
Proof.
   revert acc stk'.
  induction stk as [|it stk IH]; intros acc stk'; simpl; [by intros; simplify_eq|].
  case decide => ?; [case check_protector; [|done]|];
    move => /IH; set_solver.
Qed.

Lemma replace_check'_active_preserving cids acc stk stk':
  replace_check' cids acc stk = Some stk' → active_preserving cids stk stk'.
Proof.
  revert acc stk'.
  induction stk as [|it stk IH]; intros acc stk'; simpl.
  { intros. simplify_eq. by intros ?????%not_elem_of_nil. }
  case decide => ?; [case check_protector eqn:Eq; [|done]|].
  - move => /IH AS pm t c IN /elem_of_cons [?|]; [|by apply AS].
    subst it. exfalso. move : Eq.
    by rewrite /check_protector /= /is_active bool_decide_true //.
  - move => Eq pm t c IN /elem_of_cons [?|].
    + apply (replace_check'_acc_result _ _ _ _ Eq), elem_of_app. right.
      by apply elem_of_list_singleton.
    + by apply (IH _ _ Eq).
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
Lemma access1_head_preserving stk stk' kind tg cids n pm t opro:
  access1 stk kind tg cids = Some (n, stk') →
  mkItem pm (Tagged t) opro ∈ stk' →
  (∃ stk1 opro1, stk = (mkItem Unique (Tagged t) opro1) :: stk1) →
  (∃ stk1 opro1, stk' = (mkItem Unique (Tagged t) opro1) :: stk1).
Proof.
Abort.

(** Wellformedness *)
Lemma for_each_access1_non_empty α cids l n tg kind α' :
  for_each α l n false
          (λ stk, nstk' ← access1 stk kind tg cids; Some nstk'.2) = Some α' →
  wf_non_empty α → wf_non_empty α'.
Proof.
  move => /for_each_access1 EQ1 WF ?? /EQ1 [? [? [? NE]]]. by eapply NE, WF.
Qed.

(* TODO: move *)
Lemma list_subseteq_nil_sublist {A: Type} (x: list A):
  x ⊆ [] → sublist x [].
Proof. destruct x; set_solver. Qed.

Lemma list_subseteq_nil_inv {A: Type} (x: list A):
  x ⊆ [] → x = [].
Proof.
  intros. apply : anti_symm.
  by apply list_subseteq_nil_sublist. by apply sublist_nil_l.
Qed.

Lemma NoDup_sublist {A: Type} (x y: list A) (SUB: sublist x y) :
  NoDup y → NoDup x.
Proof.
  induction SUB as [|???? IH|???? IH].
  - done.
  - move => /NoDup_cons [NI /IH ND]. apply NoDup_cons. split; [|done].
    move => In1. apply NI. move : In1. by apply elem_of_list_sublist_proper.
  - move => /NoDup_cons [NI /IH //].
Qed.

Instance NoDup_sublist_proper {A: Type} :
  Proper (sublist ==> flip impl) (@NoDup A).
Proof. intros ????. by eapply NoDup_sublist. Qed.

Lemma filter_sublist {A: Type} (P : A → Prop)
  `{∀ x, Decision (P x)} (x y: list A) :
  sublist x y → sublist (filter P x) (filter P y).
Proof.
  induction 1 as [|???? IH|???? IH].
  - done.
  - rewrite 2!filter_cons. case decide => ? //. by constructor 2.
  - rewrite filter_cons. case decide => ? //. by constructor 3.
Qed.

Lemma filter_app {A: Type} (P : A → Prop)
  `{∀ x, Decision (P x)} (x y: list A) :
  filter P (x ++ y) = filter P x ++ filter P y.
Proof.
  induction x as [|a x IH]; [done|].
  rewrite -app_comm_cons 2!filter_cons.
  case decide => ? //. by rewrite -app_comm_cons IH.
Qed.

(* end TODO: move *)

Lemma stack_item_tagged_NoDup_cons_1 it stk :
  stack_item_tagged_NoDup (it :: stk) → stack_item_tagged_NoDup stk.
Proof.
  rewrite /stack_item_tagged_NoDup filter_cons.
  case decide => [NT|IT //]. rewrite fmap_cons. by apply NoDup_cons_12.
Qed.

Lemma stack_item_tagged_NoDup_sublist stk1 stk2:
  sublist stk1 stk2 → stack_item_tagged_NoDup stk2 → stack_item_tagged_NoDup stk1.
Proof.
  intros SUB. rewrite /stack_item_tagged_NoDup.
  by apply NoDup_sublist, fmap_sublist, filter_sublist.
Qed.

Lemma replace_check'_stack_item_tagged_NoDup cids acc stk stk':
  replace_check' cids acc stk = Some stk' →
  stack_item_tagged_NoDup (acc ++ stk) → stack_item_tagged_NoDup stk'.
Proof.
  revert acc stk'.
  induction stk as [|it stk IH]; intros acc stk'; simpl.
  { intros ?. simplify_eq. by rewrite app_nil_r. }
  case decide => ?; [case check_protector; [|done]|];
    move => /IH; [|by rewrite -app_assoc].
  move => IH1 ND. apply IH1. clear IH1. move : ND.
  rewrite /stack_item_tagged_NoDup 3!filter_app 2!filter_cons.
  case decide => [IT|NT].
  - by rewrite decide_True // 3!fmap_app 2!fmap_cons /= -assoc.
  - by rewrite decide_False // /= filter_nil app_nil_r.
Qed.

Lemma replace_check'_stack_item_tagged_NoDup_2 cids acc stk stk' stk0:
  replace_check' cids acc stk = Some stk' →
  stack_item_tagged_NoDup (acc ++ stk ++ stk0) → stack_item_tagged_NoDup (stk' ++ stk0).
Proof.
  revert acc stk' stk0.
  induction stk as [|it stk IH]; intros acc stk' stk0; simpl.
  { intros ?. by simplify_eq. }
  case decide => ?; [case check_protector; [|done]|];
    move => /IH; [|rewrite (app_assoc acc [it] (stk ++ stk0)); naive_solver].
  move => IH1 ND. apply IH1. clear IH1. move : ND.
  rewrite /stack_item_tagged_NoDup 3!filter_app 2!filter_cons.
  case decide => [IT|NT].
  - by rewrite decide_True // 3!fmap_app 2!fmap_cons /= -assoc.
  - by rewrite decide_False // /= filter_nil app_nil_r.
Qed.

Lemma replace_check_stack_item_tagged_NoDup cids stk stk' :
  replace_check cids stk = Some stk' →
  stack_item_tagged_NoDup stk → stack_item_tagged_NoDup stk'.
Proof. intros. eapply replace_check'_stack_item_tagged_NoDup; eauto. Qed.

Lemma replace_check_stack_item_tagged_NoDup_2 cids stk stk' stk0:
  replace_check cids stk = Some stk' →
  stack_item_tagged_NoDup (stk ++ stk0) → stack_item_tagged_NoDup (stk' ++ stk0).
Proof. intros; eapply replace_check'_stack_item_tagged_NoDup_2; eauto. Qed.

Lemma remove_check_stack_item_tagged_NoDup cids stk stk' idx:
  remove_check cids stk idx = Some stk' →
  stack_item_tagged_NoDup stk → stack_item_tagged_NoDup stk'.
Proof.
  revert stk' idx.
  induction stk as [|it stk IH]; intros stk' idx; simpl.
  { destruct idx; [|done]. intros ??. by simplify_eq. }
  destruct idx as [|idx]; [intros ??; by simplify_eq|].
  case check_protector eqn:Eq; [|done].
  move => /IH IH' ND. apply IH'. by eapply stack_item_tagged_NoDup_cons_1.
Qed.

Lemma remove_check_stack_item_tagged_NoDup_2 cids stk stk' stk0 idx:
  remove_check cids stk idx = Some stk' →
  stack_item_tagged_NoDup (stk ++ stk0) → stack_item_tagged_NoDup (stk' ++ stk0).
Proof.
  revert stk' stk0 idx.
  induction stk as [|it stk IH]; intros stk' stk0 idx; simpl.
  { destruct idx; [|done]. intros ??. by simplify_eq. }
  destruct idx as [|idx]; [intros ??; by simplify_eq|].
  case check_protector eqn:Eq; [|done].
  move => /IH IH' ND. apply IH'. by eapply stack_item_tagged_NoDup_cons_1.
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
  - move => ? /SUB [? [IN [-> ->]]]. by apply (proj1 (WF _ _ Eq) _ IN).
  - clear SUB NN.
    destruct (for_each_lookup_case _ _ _ _ _ ACC _ _ _ Eq Eq') as [?|[Eqf ?]].
    { subst. by apply (WF _ _ Eq). }
    destruct (access1 stk kind tg cids) as [[]|] eqn:Eqf'; [|done].
    simpl in Eqf. simplify_eq.
    eapply access1_stack_item_tagged_NoDup; eauto. by apply (WF _ _ Eq).
Qed.

Lemma copy_step_wf σ σ' e e' h0 l bor T vl :
  mem_expr_step σ.(shp) e (CopyEvt l bor T vl) h0 e' →
  bor_step h0 σ.(sst) σ.(scs) σ.(snp) σ.(snc)
                    (CopyEvt l bor T vl)
                  σ'.(shp) σ'.(sst) σ'.(scs) σ'.(snp) σ'.(snc) →
  Wf σ → Wf σ' ∧ vl <<t σ'.(snp).
Proof.
  destruct σ as [h α cids nxtp nxtc].
  destruct σ' as [h' α' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq. split; [|done].
  constructor; simpl.
  - rewrite -(for_each_dom α l (tsize T) _ _ ACC). by apply WF.
  - apply WF.
  - eapply for_each_access1_stack_item; eauto. apply WF.
  - eapply for_each_access1_non_empty; eauto. apply WF.
  - apply WF.
  - apply WF.
Qed.

(** Write *)
Lemma write_mem_dom l vl h
  (DEFINED: ∀ i : nat, (i < strings.length vl)%nat → (l +ₗ i) ∈ dom (gset loc) h) :
  dom (gset loc) (write_mem l vl h) ≡ dom (gset loc) h.
Proof.
  revert l h DEFINED. induction vl as [|v vl IH]; intros l h DEFINED; [done|].
  rewrite /= IH.
  - apply dom_map_insert_is_Some. rewrite -(shift_loc_0_nat l).
    apply (elem_of_dom (D:=gset loc)), DEFINED. simpl. lia.
  - intros i Lt. apply elem_of_dom. rewrite lookup_insert_is_Some'. right.
    rewrite (shift_loc_assoc_nat l 1). apply (elem_of_dom (D:=gset loc)), DEFINED.
    simpl. lia.
Qed.

Lemma write_mem_lookup l vl h :
  (∀ (i: nat), (i < length vl)%nat → write_mem l vl h !! (l +ₗ i) = vl !! i) ∧
  (∀ (l': loc), (∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i) →
    write_mem l vl h !! l' = h !! l').
Proof.
  revert l h. induction vl as [|v vl IH]; move => l h; simpl;
    [split; [intros ?; by lia|done]|].
  destruct (IH (l +ₗ 1) (<[l:=v]> h)) as [IH1 IH2]. split.
  - intros i Lt. destruct i as [|i].
    + rewrite shift_loc_0_nat /=. rewrite IH2; [by rewrite lookup_insert|].
      move => ? _.
      rewrite shift_loc_assoc -{1}(shift_loc_0 l) => /shift_loc_inj ?. by lia.
    + rewrite /= -IH1; [|lia].  by rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
  - intros l' Lt. rewrite IH2.
    + rewrite lookup_insert_ne; [done|].
      move => ?. subst l'. apply (Lt O); [lia|by rewrite shift_loc_0_nat].
    + move => i Lti. rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
      apply Lt. by lia.
Qed.

Lemma write_step_wf σ σ' e e' h0 l bor T vl :
  mem_expr_step σ.(shp) e (WriteEvt l bor T vl) h0 e' →
  bor_step h0 σ.(sst) σ.(scs) σ.(snp) σ.(snc)
                    (WriteEvt l bor T vl)
                  σ'.(shp) σ'.(sst) σ'.(scs) σ'.(snp) σ'.(snc) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α cids nxtp nxtc].
  destruct σ' as [h' α' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl.
  - rewrite -(for_each_dom α l (tsize T) _ _ ACC).
    rewrite write_mem_dom; [by apply WF|done].
  - move => l0 l' bor'. destruct (write_mem_lookup l vl h) as [IN OUT].
    case (decide (l0.1 = l.1)) => Eq1.
    + have Eql0: l0 = (l +ₗ (l0.2 - l.2)).
      { rewrite /shift_loc -Eq1. destruct l0; simpl. f_equal. by lia. }
      case (decide (0 ≤ l0.2 - l.2 < length vl)) => [[Le Lt]|NLe].
      * rewrite Eql0 -(Z2Nat.id _ Le) IN.
        intros Eq%elem_of_list_lookup_2. apply (BOR _ _ Eq).
        rewrite -(Nat2Z.id (length vl)) -Z2Nat.inj_lt; [done|lia..].
      * rewrite OUT; [by apply (state_wf_mem_tag _ WF)|].
        move => i Lt Eq. rewrite Eql0 in Eq. apply shift_loc_inj in Eq.
        apply NLe. rewrite Eq. lia.
    + rewrite OUT; [by apply (state_wf_mem_tag _ WF)|].
      move => ? _ Eq. apply Eq1. rewrite Eq. by apply shift_loc_block.
  - eapply for_each_access1_stack_item; eauto. apply WF.
  - eapply for_each_access1_non_empty; eauto. apply WF.
  - apply WF.
  - apply WF.
Qed.

(** Call *)
Lemma initcall_step_wf σ σ' e e' h0 n :
  mem_expr_step σ.(shp) e (InitCallEvt n) h0 e' →
  bor_step h0 σ.(sst) σ.(scs) σ.(snp) σ.(snc)
                    (InitCallEvt n)
                  σ'.(shp) σ'.(sst) σ'.(scs) σ'.(snp) σ'.(snc) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α cids nxtp nxtc].
  destruct σ' as [h' α' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  (* have EqN: nxtc !! fresh (dom (gset nat) nxtc) = None
    by apply (not_elem_of_dom (D:= gset nat)), is_fresh. *)
  constructor; simpl; [apply WF..|intros ?? Eq; split|apply WF| |].
  - intros ? In.
    destruct ((proj1 (state_wf_stack_item _ WF _ _ Eq)) _ In) as [SI1 SI2].
    split; [done|]. move : SI2. destruct si.(protector); [simpl; lia|done].
  - apply (state_wf_stack_item _ WF _ _ Eq).
  - apply NoDup_cons_2; [|apply WF].
    move => /(state_wf_cid_agree _ WF) /=. lia.
  - intros c. rewrite elem_of_cons.
    move => [->|/(state_wf_cid_agree _ WF)]; [by left|by right].
Qed.

(** EndCall *)
Lemma endcall_step_wf σ σ' e e' h0 n v :
  mem_expr_step σ.(shp) e (EndCallEvt n v) h0 e' →
  bor_step h0 σ.(sst) σ.(scs) σ.(snp) σ.(snc)
                    (EndCallEvt n v)
                  σ'.(shp) σ'.(sst) σ'.(scs) σ'.(snp) σ'.(snc) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α cids nxtp nxtc].
  destruct σ' as [h' α' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl; [apply WF..|intros ?? Eq; split|apply WF| |].
  - intros ? In. apply ((proj1 (state_wf_stack_item _ WF _ _ Eq)) _ In).
  - apply (state_wf_stack_item _ WF _ _ Eq).
  - eapply NoDup_cons_12, WF.
  - intros c IN. apply WF. by right.
Qed.

(** Retag *)

Lemma tag_value_included_trans tg :
  Proper ((≤)%nat ==> impl) (tag_included tg).
Proof.
  intros nxtp nxtp' Le. rewrite /tag_included.
  by destruct tg; simpl; intros ?; [lia..|done].
Qed.

Lemma retag_ref_nxtp_mono h α cids nxtp l bor T kind bar bor' α' nxtp' :
  retag_ref h α cids nxtp l bor T kind bar = Some (bor', α', nxtp') →
  (nxtp ≤ nxtp')%nat.
Proof.
  rewrite /retag_ref.
  case tsize => ?; [by intros; simplify_eq|].
  case reborrow eqn:Eqb; [simpl|done]. intros. simplify_eq. lia.
Qed.

Lemma retag_ref_nxtp_bor_mono h α cids nxtp l bor T kind bar bor' α' nxtp' :
  retag_ref h α cids nxtp l bor T kind bar = Some (bor', α', nxtp') →
  bor <t nxtp → bor' <t nxtp'.
Proof.
  rewrite /retag_ref.
  case tsize => ?; [by intros; simplify_eq|].
  case reborrow eqn:Eqb; [simpl|done]. intros. simplify_eq.
  destruct kind; simpl; [lia..|done].
Qed.

Lemma item_insert_dedup_non_empty stk new n :
  stk ≠ [] → item_insert_dedup stk new n ≠ [].
Proof.
  intros. destruct n; simpl.
  - destruct stk; [done|by case decide].
  - case lookup => [?|]; case lookup => [?|].
    + case decide => ?; [done|]. case decide => ?; [done|].
      move => ?. by eapply app_cons_not_nil.
    + case decide => ?; [done|]. move => ?. by eapply app_cons_not_nil.
    + case decide => ?; [done|]. move => ?. by eapply app_cons_not_nil.
    + move => ?. by eapply app_cons_not_nil.
Qed.

Lemma item_insert_dedup_subseteq stk new n :
  item_insert_dedup stk new n ⊆ new :: stk.
Proof.
  intros. destruct n; simpl.
  - destruct stk; [done|case decide => [<-|_]]; set_solver.
  - have ?: take (S n) stk ++ new :: drop (S n) stk ⊆ new :: stk.
    { intros x.
      rewrite elem_of_app elem_of_cons -or_assoc (or_comm _ (x = new))
              or_assoc -elem_of_app take_drop. set_solver. }
    by case lookup => [?|]; case lookup => [?|];
      [case decide => ?; [set_solver|]..|]; [case decide => ?; [set_solver|]|..].
Qed.

Lemma grant_non_empty stk bor new cids stk':
  grant stk bor new cids = Some stk' →
  stk ≠ [] → stk' ≠ [].
Proof.
  rewrite /grant. case find_granting as [[n pm]|]; [|done].
  cbn -[item_insert_dedup].
  destruct new.(perm). (* TODO: duplicated proofs *)
  - case access1 as [[n1 stk1]|]; [|done].
    simpl. intros ? _. simplify_eq. destruct stk1; [done|by case decide].
  - case find_first_write_incompatible as [n1|]; [|done].
    simpl. intros. simplify_eq. by apply item_insert_dedup_non_empty.
  - case access1 as [[n1 stk1]|]; [|done].
    simpl. intros ? _. simplify_eq. destruct stk1; [done|by case decide].
  - case access1 as [[n1 stk1]|]; [|done].
    simpl. intros ? _. simplify_eq. destruct stk1; [done|by case decide].
Qed.

Lemma tagged_sublist_stack_item_included stk stk' nxtp nxtc  :
  tagged_sublist stk' stk →
  stack_item_included stk nxtp nxtc → stack_item_included stk' nxtp nxtc.
Proof. by move => SF HI si /SF [? [/HI ? [-> ->]]]. Qed.

Lemma subseteq_stack_item_included stk stk' nxtp nxtc  :
  stk' ⊆ stk →
  stack_item_included stk nxtp nxtc → stack_item_included stk' nxtp nxtc.
Proof. by move => SF HI si /SF /HI. Qed.

Lemma subseteq_tagged_sublist stk stk' :
  stk' ⊆ stk → tagged_sublist stk' stk.
Proof. move => SUB ? /SUB. naive_solver. Qed.

Lemma tagged_sublist_cons stk new:
  tagged_sublist stk (new :: stk).
Proof. intros ??. setoid_rewrite elem_of_cons. naive_solver. Qed.

Lemma grant_tagged_sublist stk bor new cids stk':
  grant stk bor new cids = Some stk' → tagged_sublist stk' (new :: stk).
Proof.
  rewrite /grant.
  case find_granting as [[n pm]|]; [|done].
  cbn -[item_insert_dedup]. destruct new.(perm). (* TODO: duplicated proofs *)
  - case access1 as [[n1 stk1]|] eqn:Eq1; [|done]. cbn -[item_insert_dedup].
    intros. simplify_eq. apply access1_tagged_sublist in Eq1. etrans.
    + apply subseteq_tagged_sublist, item_insert_dedup_subseteq.
    + by apply (tagged_sublist_app [new] [new]).
  - case find_first_write_incompatible as [n1|]; [|done].
    simpl. intros. simplify_eq.
    by apply subseteq_tagged_sublist, item_insert_dedup_subseteq.
  - case access1 as [[n1 stk1]|] eqn:Eq1; [|done]. cbn -[item_insert_dedup].
    intros. simplify_eq. apply access1_tagged_sublist in Eq1. etrans.
    + apply subseteq_tagged_sublist, item_insert_dedup_subseteq.
    + by apply (tagged_sublist_app [new] [new]).
  - case access1 as [[n1 stk1]|] eqn:Eq1; [|done]. cbn -[item_insert_dedup].
    intros. simplify_eq. apply access1_tagged_sublist in Eq1. etrans.
    + apply subseteq_tagged_sublist, item_insert_dedup_subseteq.
    + by apply (tagged_sublist_app [new] [new]).
Qed.

Lemma for_each_grant α cids l n tg new α' :
  for_each α l n false (λ stk, grant stk tg new cids) = Some α' →
  ∀ (l: loc) stk', α' !! l = Some stk' → ∃ stk, α !! l = Some stk ∧
    tagged_sublist stk' (new :: stk) ∧ (stk ≠ [] → stk' ≠ []).
Proof.
  intros EQ. destruct (for_each_lookup  _ _ _ _ _ EQ) as [EQ1 [EQ2 EQ3]].
  intros l1 stk1 Eq1.
  case (decide (l1.1 = l.1)) => [Eql|NEql];
    [case (decide (l.2 ≤ l1.2 < l.2 + n)) => [[Le Lt]|NIN]|].
  - have Eql2: l1 = l +ₗ Z.of_nat (Z.to_nat (l1.2 - l.2)). {
      destruct l, l1. move : Eql Le => /= -> ?.
      rewrite /shift_loc /= Z2Nat.id; [|lia]. f_equal. lia. }
    destruct (EQ2 (Z.to_nat (l1.2 - l.2)) stk1)
      as [stk [Eq Eq0]];
      [rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; lia|by rewrite -Eql2|].
    exists stk. split; [by rewrite Eql2|]. simplify_eq.
    split; [by eapply grant_tagged_sublist|by eapply grant_non_empty].
  - exists stk1. split; last split; [..|by apply tagged_sublist_cons|done].
    rewrite -EQ3; [done|]. intros i Lt Eq. apply NIN. rewrite Eq /=. lia.
  - exists stk1. split; last split; [..|by apply tagged_sublist_cons|done].
    rewrite -EQ3; [done|]. intros i Lt Eq. apply NEql. by rewrite Eq.
Qed.

Lemma for_each_grant_non_empty α cids l n tg new α' :
  for_each α l n false (λ stk, grant stk tg new cids) = Some α' →
  wf_non_empty α → wf_non_empty α'.
Proof.
  move => /for_each_grant EQ1 WF ?? /EQ1 [? [? [? NE]]]. by eapply NE, WF.
Qed.

Lemma grant_stack_item_tagged_NoDup stk bor new cids stk'
  (NEW: match new.(tg) with
        | Tagged t => ∀ it, it ∈ stk → it.(tg) ≠ new.(tg)
        | _ => True
        end) :
  grant stk bor new cids = Some stk' →
  stack_item_tagged_NoDup stk → stack_item_tagged_NoDup stk'.
Proof.
  rewrite /grant.
  case find_granting as [[n pm]|]; [|done].
  cbn -[item_insert_dedup]. destruct new.(perm). (* TODO: duplicated proofs *)
  - case access1 as [[n1 stk1]|] eqn:Eq1; [|done]. cbn -[item_insert_dedup].
    intros. simplify_eq.
    admit.
  - case find_first_write_incompatible as [n1|]; [|done].
    simpl. intros. simplify_eq.
    admit.
  - case access1 as [[n1 stk1]|] eqn:Eq1; [|done]. cbn -[item_insert_dedup].
    intros. simplify_eq.
    admit.
  - case access1 as [[n1 stk1]|] eqn:Eq1; [|done]. cbn -[item_insert_dedup].
    intros. simplify_eq.
    admit.
Admitted.

Lemma for_each_grant_stack_item α nxtc cids nxtp l n bor new α'
  (PR: match new.(protector) with Some c => (c < nxtc)%nat | _ => True end)
  (TG2: new.(tg) <t nxtp)
  (NEW: match new.(tg) with
        | Tagged t => ∀ (i: nat) stk, (i < n)%nat → α !! (l +ₗ i) = Some stk →
                    ∀ it, it ∈ stk → it.(tg) ≠ new.(tg)
        | _ => True
        end) :
  for_each α l n false (λ stk, grant stk bor new cids) = Some α' →
  wf_stack_item α nxtp nxtc → wf_stack_item α' nxtp nxtc.
Proof.
  intros ACC WF l' stk' Eq'.
  destruct (for_each_grant _ _ _ _ _ _ _ ACC _ _ Eq') as [stk [Eq [SUB ?]]].
  split.
  - eapply tagged_sublist_stack_item_included; [eauto|].
    move => it /elem_of_cons [-> //|] / (proj1 (WF _ _ Eq)) [Lt ?].
    split; [|done]. move : Lt. destruct it.(tg); [lia|done].
  - destruct (for_each_lookup_case _ _ _ _ _ ACC _ _ _ Eq Eq')
      as [?|[Eqf [i [[Le Lt] ?]]]].
    { subst. by apply (WF _ _ Eq). }
    eapply grant_stack_item_tagged_NoDup; eauto.
    + destruct new.(tg); [|done].
      subst l'. intros it. apply (NEW (Z.to_nat i)).
      * rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; by lia.
      * by rewrite Z2Nat.id.
    + by apply (WF _ _ Eq).
Qed.

Lemma reborrowN_wf_stack α nxtc cids nxtp l n old new pm bar α'
  (PR: match bar with Some c => (c < nxtc)%nat | _ => True end)
  (TG2: new <t nxtp)
  (NEW: match new with
        | Tagged t => ∀ (i: nat) stk, (i < n)%nat → α !! (l +ₗ i) = Some stk →
                    ∀ it, it ∈ stk → it.(tg) ≠ new
        | _ => True
        end) :
  reborrowN α cids l n old new pm bar = Some α' →
  wf_stack_item α nxtp nxtc ∧ wf_non_empty α →
  dom (gset loc) α ≡ dom (gset loc) α' ∧
  wf_stack_item α' nxtp nxtc ∧ wf_non_empty α'.
Proof.
  intros RB [WF1 WF2]. split; last split.
  - eapply for_each_dom; eauto.
  - move : WF1. eapply for_each_grant_stack_item; [..|eauto]; done.
  - move : WF2. eapply for_each_grant_non_empty; [..|eauto]; done.
Qed.

Lemma unsafe_action_wf_stack
  (f: stacks → _ → _ → _ → _) α l (last fs us: nat) α' l' c' nxtp nxtc
  (P: stacks → loc → nat → Prop) :
  (∀ α l sz1 sz2, P α l (sz1 + sz2)%nat →
    P α l sz1 ∧ ∀ α',
    (∀ i:nat, (i < sz2)%nat → α' !! (l +ₗ sz1 +ₗ i) = α !! (l +ₗ sz1 +ₗ i)) →
    P α' (l +ₗ sz1) sz2) →
  (∀ α1 α2 l n b, f α1 l n b = Some α2 →
    ∀ l', (∀ (i : nat), (i < n)%nat → l' ≠ l +ₗ i) → α2 !! l' = α1 !! l') →
  (∀ α1 α2 l n b,
    P α1 l n →
    f α1 l n b = Some α2 →
    wf_stack_item α1 nxtp nxtc ∧ wf_non_empty α1 →
    dom (gset loc) α1 ≡ dom (gset loc) α2 ∧
    wf_stack_item α2 nxtp nxtc ∧ wf_non_empty α2) →
  P α (l +ₗ last) (l' - last)%nat →
  unsafe_action f α l last fs us = Some (α', (l', c')) →
  wf_stack_item α nxtp nxtc ∧ wf_non_empty α →
  dom (gset loc) α ≡ dom (gset loc) α' ∧
  wf_stack_item α' nxtp nxtc ∧ wf_non_empty α'.
Proof.
  intros HP Hf0 Hf. rewrite /unsafe_action.
  case f as [α1|] eqn:Eq1; [simpl|done].
  case (f α1) as [α2|] eqn:Eq2; [simpl|done]. intros HP1 Eq WF. simplify_eq.
  rewrite (_: (last + fs + us - last)%nat = (fs + us)%nat) in HP1; [|lia].
  destruct (HP _ _ _ _ HP1) as [HP2 HP3].
  destruct (Hf _ _ _ _ _ HP2 Eq1) as (EqD1 & ?); [done|].
  have HP4: P α1 (l +ₗ last +ₗ fs) us.
  { apply HP3. intros i Lt. apply (Hf0 _ _ _ _ _ Eq1).
    intros j Ltj. rewrite shift_loc_assoc. intros ?%shift_loc_inj. lia. }
  move : HP4. rewrite shift_loc_assoc -Nat2Z.inj_add => HP4.
  destruct (Hf _ _ _ _ _ HP4 Eq2) as [EqD2 ?]; [done|].
  split; [|done]. by rewrite EqD1 EqD2.
Qed.


Lemma unsafe_action_offsets {A}
  (f: A → _ → nat → _ → _) a l (last fsz usz: nat) a' last' cur_dist' :
  unsafe_action f a l last fsz usz = Some (a', (last', cur_dist')) →
  (last' = last + fsz + usz ∧ cur_dist' = O)%nat.
Proof.
  rewrite /unsafe_action. do 2 (case f => ?; [simpl|done]).
  intros. by simplify_eq.
Qed.

Lemma visit_freeze_sensitive'_offsets {A}
  h l (f: A → _ → nat → _ → _) a (last cur_dist: nat) T a' last' cur_dist' :
  let HA (oalc: option (A * (nat * nat))) l1 c1 T1 a2 l2 c2 :=
    (oalc = Some (a2, (l2, c2)) →
      (l1 ≤ l2 ∧ l2 + c2 = l1 + c1 + tsize T1)%nat) in
  HA (visit_freeze_sensitive' h l f a last cur_dist T)
     last cur_dist T a' last' cur_dist'.
Proof.
  intros HA.
  apply (visit_freeze_sensitive'_elim
    (* general goal P *)
    (λ _ _ _ _ l1 c1 T1 oalc, ∀ a2 l2 c2, HA oalc l1 c1 T1 a2 l2 c2)
    (λ _ _ _ _ _ _ _ _ l1 c1 Ts oalc, ∀ a2 l2 c2,
      HA oalc l1 c1 (Product Ts) a2 l2 c2)
    (λ _ _ _ _ l1 c1 _ Ts i oalc, ∀ a2 l2 c2,
      oalc = Some (a2, (l2, c2)) → ∃ T1, Ts !! i = Some T1 ∧
      (l1 ≤ l2 ∧ l2 + c2 = l1 + S c1 + tsize T1)%nat)); rewrite /HA.
  - intros. simplify_eq. simpl. lia.
  - intros. simplify_eq. simpl. lia.
  - clear. intros _ ????????? [??]%unsafe_action_offsets. subst. simpl. lia.
  - clear. intros _ ?????????. case is_freeze.
    + intros. simplify_eq. lia.
    + intros [??]%unsafe_action_offsets. subst. lia.
  - clear. intros ??????? IH ???.
    case is_freeze; [intros; simplify_eq; lia|by move => /IH].
  - clear. intros ???? l1 c1 ? IH ???.
    case is_freeze; [intros; simplify_eq; lia|].
    case lookup => [[//|i|//|//]|//].
    case decide => [Ge0|//].
    case visit_freeze_sensitive'_clause_6_visit_lookup
      as [[? [l3 c3]]|] eqn:Eq1; [simpl|done].
    intros. simplify_eq.
    destruct (IH ScPoison _ Ge0 _ _ _ Eq1) as (T1&HL&Le&Eq).
    split; [done|]. rewrite le_plus_minus_r; [done|].
    etrans; [apply (le_plus_l _ c3)|]. rewrite Eq.
    rewrite (_: l1 + S c1 + tsize T1 = l1 + c1 + S (tsize T1))%nat; [|lia].
    by eapply plus_le_compat_l, tsize_subtype_of_sum, elem_of_list_lookup_2.
  - naive_solver.
  - clear. intros h l f a1 l1 c1 Ts a2 l2 c2 T Ts' IH1 IH2 a4 l4 c4.
    case visit_freeze_sensitive' as [[a3 [l3 c3]]|] eqn:Eq3; [|done].
    cbn -[tsize].
    destruct (IH2 a3 l3 c3) as [Le3 EqO3]; [done|].
    intros Eq4. destruct (IH1 (a3, (l3, c3)) a4 l4 c4 Eq4) as [Le4 EqO4].
    clear -Le3 EqO3 Le4 EqO4. simpl in Le4. rewrite EqO4. cbn -[tsize].
    rewrite EqO3 tsize_product_cons. lia.
  - naive_solver.
  - naive_solver.
  - naive_solver.
Qed.

Lemma unsafe_action_stacks_unchanged
  (f: stacks → _ → nat → _ → _) α l (last fsz usz: nat) α' ln cn
  (HF: ∀ α1 α2 l n b, f α1 l n b = Some α2 →
      ∀ l', (∀ (i : nat), (i < n)%nat → l' ≠ l +ₗ i) → α2 !! l' = α1 !! l') :
  unsafe_action f α l last fsz usz = Some (α', (ln, cn)) →
  (last ≤ ln)%nat ∧
  (∀ l', (∀ (i : nat), (last ≤ i < ln)%nat → l' ≠ l +ₗ i) → α' !! l' = α !! l').
Proof.
  rewrite /unsafe_action.
  case f as [α1|] eqn:Eqf1; [simpl|done]. case (f α1) eqn:Eqf2; [simpl|done].
  intros ?. simplify_eq. split; [lia|].
  intros ? NEQ.
  rewrite (HF _ _ _ _ _ Eqf2); last first.
  { intros i Lt.
    rewrite shift_loc_assoc -Nat2Z.inj_add. apply NEQ. lia. }
  rewrite (HF _ _ _ _ _ Eqf1) //.
  intros ??. rewrite shift_loc_assoc -Nat2Z.inj_add. apply NEQ. lia.
Qed.

Lemma visit_freeze_sensitive'_stacks_unchanged h l (f: stacks → _ → _ → _ → _)
  α α' last cur T l' c' :
  let HF (f: stacks → loc → nat → bool → option stacks) :=
    (∀ α1 α2 l n b, f α1 l n b = Some α2 →
      ∀ l', (∀ (i : nat), (i < n)%nat → l' ≠ l +ₗ i) → α2 !! l' = α1 !! l') in
  let UC α1 α2 (l: loc) (lo ln: nat) :=
    (lo ≤ ln)%nat ∧
    (∀ l', (∀ (i : nat), (lo ≤ i < ln)%nat → l' ≠ l +ₗ i) → α2 !! l' = α1 !! l') in
  HF f →
  visit_freeze_sensitive' h l f α last cur T = Some (α', (l', c')) →
  UC α α' l last l'.
Proof.
  intros HF UC.
  apply (visit_freeze_sensitive'_elim
    (* general goal P *)
    (λ _ l f α l1 c1 T oalc, ∀ α' l' c',
      HF f → oalc = Some (α', (l', c')) → UC α α' l l1 l')
    (λ _ l f _ _ _ Ts1 α l1 c1 Ts2 oalc, ∀ α' l' c',
      HF f → oalc = Some (α', (l', c')) →
          UC α α' l l1 l')
    (λ _ l f α l1 c1 Ts1 Ts2 _ oalc, ∀ α' l' c',
      HF f → oalc = Some (α', (l', c')) →
          UC α α' l l1 l')); rewrite /HF /UC.
  - naive_solver.
  - naive_solver.
  - (* Unsafe case *)
    clear. intros _ ?? α l1 c1 ? α2 l2 c2 HF0.
    eapply unsafe_action_stacks_unchanged; eauto.
  - (* Union case *)
    intros _???????? HF0. case is_freeze; [by intros; simplify_eq|].
    intros UN. eapply unsafe_action_stacks_unchanged; eauto.
  - clear. intros ??????? IH ??? HF0.
    case is_freeze; [by intros ?; simplify_eq|]. intros VS.
    eapply (IH _ _ _ HF0); eauto.
  - clear. intros ??????? IH ??? HF0. case is_freeze; [by intros; simplify_eq|].
    case lookup => [[//|i|//|//]|//].
    case decide => [Ge0|//].
    case visit_freeze_sensitive'_clause_6_visit_lookup
      as [[? []]|] eqn:Eq1; [simpl|done].
    intros. simplify_eq. eapply (IH ScPoison); eauto.
  - naive_solver.
  - (* Product case *)
    clear. intros ???????????? IH1 IH2 ??? HF0.
    case visit_freeze_sensitive' as [alc|] eqn:Eqa; [|done].
    intros VS. destruct alc as [a1 [l1 c1]]. simpl in VS.
    destruct (IH2 a1 l1 c1 HF0 eq_refl) as [Le2 IH2'].
    destruct (IH1 (a1, (l1,c1)) α' l' c') as [Le1 IH1'];
      [done..|simpl in Le1; split]; [lia|].
    intros ? NC. simpl in IH1', IH2'. rewrite IH1'; [rewrite IH2' //|].
    + intros ??. apply NC. lia.
    + intros ??. apply NC. lia.
  - naive_solver.
  - naive_solver.
  - naive_solver.
Qed.

Lemma visit_freeze_sensitive'_wf_stack h l (f: stacks → _ → _ → _ → _)
  α α' last cur T l' c' nxtp nxtc (P: stacks → loc → nat → Prop) :
  let Hα α1 α2 l n :=
    (P α1 l n → wf_stack_item α1 nxtp nxtc ∧ wf_non_empty α1 →
      dom (gset loc) α1 ≡ dom (gset loc) α2 ∧
      wf_stack_item α2 nxtp nxtc ∧ wf_non_empty α2) in
  let HP :=
    (∀ α l sz1 sz2, P α l (sz1 + sz2)%nat → P α l sz1 ∧ ∀ α',
    (∀ i:nat, (i < sz2)%nat → α' !! (l +ₗ sz1 +ₗ i) = α !! (l +ₗ sz1 +ₗ i)) →
    P α' (l +ₗ sz1) sz2) in
  let HF0 (f: stacks → loc → nat → bool → option stacks) :=
    (∀ α1 α2 l n b, f α1 l n b = Some α2 →
      ∀ l', (∀ (i : nat), (i < n)%nat → l' ≠ l +ₗ i) → α2 !! l' = α1 !! l') in
  let HF f := (∀ α1 α2  l n b, f α1 l n b = Some α2 → Hα α1 α2 l n) in
  HP → HF0 f → HF f →
  visit_freeze_sensitive' h l f α last cur T = Some (α', (l', c')) →
  Hα α α' (l +ₗ last) (l' - last)%nat.
Proof.
  intros Hα HP HF0 HF HP1.
  apply (visit_freeze_sensitive'_elim
    (* general goal P *)
    (λ _ l f α l1 c1 T oalc, ∀ α' l' c',
      HF0 f → HF f → oalc = Some (α', (l', c')) → Hα α α' (l +ₗ l1) (l' - l1)%nat)
    (λ _ l f _ _ _ Ts1 α l1 c1 Ts2 oalc, ∀ α' l' c',
      HF0 f → HF f → oalc = Some (α', (l', c')) →
          Hα α α' (l +ₗ l1) (l' - l1)%nat)
    (λ _ l f α l1 c1 Ts Ts2 _ oalc, ∀ α' l' c',
      HF0 f → HF f → oalc = Some (α', (l', c')) →
          Hα α α' (l +ₗ l1) (l' - l1)%nat)); rewrite /HF /HF0 /Hα.
  - naive_solver.
  - naive_solver.
  - (* Unsafe case *)
    clear -HP1.
    intros _ ????????? HF0 HF UN HP2. eapply unsafe_action_wf_stack; eauto.
  - (* Union case *)
    clear -HP1.
    intros _????????? HF0 HF. case is_freeze; [by intros; simplify_eq|].
    intros UN HP2. eapply unsafe_action_wf_stack; eauto.
  - clear -HP1. intros ??????? IH ??? HF0 HF.
    case is_freeze; [by intros ?; simplify_eq|]. intros VS HP2.
    eapply (IH _ _ _ HF0 HF); eauto.
  - clear. intros ??????? IH ??? HF0 HF. case is_freeze; [by intros; simplify_eq|].
    case lookup => [[//|i|//|//]|//].
    case decide => [Ge0|//].
    case visit_freeze_sensitive'_clause_6_visit_lookup
      as [[? []]|] eqn:Eq1; [simpl|done].
    intros. simplify_eq. eapply (IH ScPoison); eauto.
  - naive_solver.
  - (* Product case *)
    clear -HP1. intros h l f α1 l1 c1 Ts1 α0 l0 c0 T Ts IH1 IH2 α' l' c' HF0 HF.
    case visit_freeze_sensitive' as [alc|] eqn:Eqa; [|done].
    intros VS HP2 WF. simpl in VS. destruct alc as [α2 [l2 c2]].
    destruct (visit_freeze_sensitive'_offsets _ _ _ _ _ _ _ _ _ _ Eqa) as [Le2 Eq2].
    destruct (visit_freeze_sensitive'_stacks_unchanged _ _ _ _ _ _ _ _ _ _ HF0 Eqa)
      as [Le NC].
    destruct (HP1 α0 (l +ₗ l0) (l2 - l0)%nat (l' - l2)%nat) as [HP3 HP4].
    { rewrite (_: (l2  - l0 + (l' - l2))%nat = l' - l0)%nat //. SearchAbout l' l2. }
    (* rewrite (_: (l2 + c2 - l0 = c0 + tsize T)%nat) in HP3; [|lia].
    specialize (IH2 α2 (l2,c2) HF0 HF eq_refl HP3 WF) as [EqD WF1]. rewrite EqD.
    apply (IH1 (α2, (l2,c2)) _ _ HF0 HF VS); [|done].
    move : (HP4 α2). simpl.
    simpl.
  - naive_solver.
  - admit.
  - admit. *)
Admitted.

Lemma visit_freeze_sensitive_wf_stack h l T (f: stacks → _ → _ → _ → _)
  nxtp nxtc α α' :
  (∀ α1 α2 l n b, f α1 l n b = Some α2 →
    wf_stack_item α1 nxtp nxtc ∧ wf_non_empty α1 →
    dom (gset loc) α1 ≡ dom (gset loc) α2 ∧
   wf_stack_item α2 nxtp nxtc ∧ wf_non_empty α2) →
  visit_freeze_sensitive h l T f α = Some α' →
  wf_stack_item α nxtp nxtc ∧ wf_non_empty α →
  dom (gset loc) α ≡ dom (gset loc) α' ∧
  wf_stack_item α' nxtp nxtc ∧ wf_non_empty α'.
Proof.
  intros Hf. rewrite /visit_freeze_sensitive.
  case visit_freeze_sensitive' as [[α1 [last cur]]|] eqn:Eq; [|done].
  move => Eqf WF.
  move : Eq => /visit_freeze_sensitive'_wf_stack WF'.
  (* destruct (WF' _ _ Hf WF) as [EqD WF1]. rewrite EqD.
  by eapply Hf; eauto. *)
Admitted.

Lemma reborrow_wf_stack h α nxtc cids nxtp l old T kind new bar α'
  (TG2: new <t nxtp)
  (BAR : match bar with Some c => (c < nxtc)%nat | _ => True end)
  (NEW: match new with
        | Tagged t => ∀ (i: nat) stk, (i < tsize T)%nat → α !! (l +ₗ i) = Some stk →
                    ∀ it, it ∈ stk → it.(tg) ≠ new
        | _ => True
        end) :
  reborrow h α cids l old T kind new bar = Some α' →
  wf_stack_item α nxtp nxtc ∧ wf_non_empty α →
  dom (gset loc) α ≡ dom (gset loc) α' ∧
  wf_stack_item α' nxtp nxtc ∧ wf_non_empty α'.
Proof.
  rewrite /reborrow. destruct kind as [[]| |].
  - by eapply reborrowN_wf_stack; eauto.
  - by eapply reborrowN_wf_stack; eauto.
  - SearchAbout visit_freeze_sensitive.
    apply visit_freeze_sensitive_wf_stack.
    intros ???????. admit.
    (* by eapply reborrowN_wf_stack. *)
  - destruct mutable.
    + by eapply reborrowN_wf_stack; eauto.
    + apply visit_freeze_sensitive_wf_stack.
      intros ?????. admit.
      (*  by eapply reborrowN_wf_stack. *)
Admitted.

Lemma retag_ref_wf_stack h α nxtc cids nxtp x l old T kind bar bor' α' nxtp'
  (BAR : match bar with Some c => (c < nxtc)%nat | _ => True end)
  (Eqx: h !! x = Some (ScPtr l old)) :
  retag_ref h α cids nxtp l old T kind bar = Some (bor', α', nxtp') →
  wf_mem_tag h nxtp →
  wf_stack_item α nxtp nxtc → wf_non_empty α →
  dom (gset loc) h ≡ dom (gset loc) (<[x:=(ScPtr l bor')]> h) ∧
  wf_mem_tag (<[x:=(ScPtr l bor')]> h) nxtp' ∧
  dom (gset loc) α ≡ dom (gset loc) α' ∧
  wf_stack_item α' nxtp' nxtc ∧ wf_non_empty α'.
Proof.
  intros RE WF1 WF2 WF3. split; last split.
  { symmetry; apply dom_map_insert_is_Some; by eexists. }
  { intros  x' l' t'. case (decide (x' = x)) => ?; [subst x'|].
    - rewrite lookup_insert => ?. simplify_eq.
      move : RE => /retag_ref_nxtp_bor_mono LT. apply LT.
      destruct old; [by eapply WF1|done].
    - rewrite lookup_insert_ne; [|done].
      move => /WF1. apply (tag_value_included_trans (Tagged t')).
      by eapply retag_ref_nxtp_mono. }
  move : RE WF2 WF3.
  rewrite /retag_ref. case tsize eqn:Eq; [by intros; simplify_eq|].
  case reborrow as [α1|] eqn:Eq1; [simpl|done].
  intros ?. simplify_eq. intros WF2 WF3.
  eapply reborrow_wf_stack; eauto; [..|].
  - destruct kind; simpl; [lia..|done].
  - admit.
  - split; [|done]. eapply wf_stack_item_mono; [..|done|exact WF2]. by lia.
Admitted.

Definition borrow_barrier_Some nxtc kind c : Prop :=
  match kind with FnEntry => (c < nxtc)%nat | _ => True end.


Lemma retag_wf_stack h α nxtp nxtc cids c l kind T h' α' nxtp' :
  let Hα h h' α α' nxtp nxtp' cids c kind :=
    (borrow_barrier_Some nxtc kind c →
      wf_mem_tag h nxtp →
      wf_stack_item α nxtp nxtc → wf_non_empty α →
      dom (gset loc) h ≡ dom (gset loc) h' ∧
      wf_mem_tag h' nxtp' ∧ dom (gset loc) α ≡ dom (gset loc) α' ∧
      wf_stack_item α' nxtp' nxtc ∧ wf_non_empty α') in
  retag h α nxtp cids c l kind T = Some (h', α', nxtp') →
  Hα h h' α α' nxtp nxtp' cids c kind.
Proof.
  intros Hα.
  eapply (retag_elim
    (* general goal P *)
    (λ h α nxtp cids c _ kind _ ohac, ∀ h' α' nxtp',
        ohac = Some (h', α', nxtp') → Hα h h' α α' nxtp nxtp' cids c kind)
    (* invariant for Product's where P1 *)
    (λ _ _ _ cids c _ kind _ h α nxtp _ _ ohac, ∀ h' α' nxtp',
        ohac = Some (h', α', nxtp') → Hα h h' α α' nxtp nxtp' cids c kind)
    (* invariant for Sum's where P3 *)
    (λ h _ _ α nxtp cids c kind _ _ _ ohac, ∀ h' α' nxtp',
        ohac = Some (h', α', nxtp') → Hα h h' α α' nxtp nxtp' cids c kind)); rewrite /Hα.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - (* Reference cases *)
    clear. intros h ?? bor α nxtp cids c rt_kind p_kind T Eq h' α' nxtp'.
    destruct p_kind as [[]|[]|];
      [| |destruct rt_kind; try by (intros; simplify_eq)..|];
      (case retag_ref as [[[new α1] nxtp1]|] eqn:Eq1; [simpl|done]);
      intros ???; simplify_eq; eapply retag_ref_wf_stack; eauto; [| |done..];
      by destruct rt_kind.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - (* Product inner recursive case *)
    intros ?????????????? IH1 IH2 ???.
    case retag as [hac|]; [|done]. move => /= /IH1 WF BS WF1 WF2 WF3.
    destruct hac as [[h2 α2] c2].
    destruct (IH2 _ _ _ eq_refl) as (Eq1&?&Eq2&?&?); [done..|].
    destruct (WF BS) as (? & ? & ? & ?); [done..|].
    split; last split; last split; [by rewrite Eq1|done|by rewrite Eq2|done..].
  - naive_solver.
  - (* Sum case *)
    intros ????????? IH Eq ???. case decide => Le; [|done]. by apply IH.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
Qed.

Lemma retag_wf h α nxtp nxtc c cids l kind T h' α' nxtp' :
  retag h α nxtp (c::cids) c l kind T = Some (h', α', nxtp') →
  Wf (mkState h α (c::cids) nxtp nxtc) → Wf (mkState h' α' (c::cids) nxtp' nxtc).
Proof.
  move => /retag_wf_stack WF' WF.
  have ?: borrow_barrier_Some nxtc kind c.
  { destruct kind; [|done..]. apply WF. by left. }
  destruct (WF' nxtc) as (Eq1 & ? & Eq2 & ? & ?); [done|apply WF..|].
  constructor; simpl; [|done..|apply WF|apply WF].
  by rewrite -Eq1 -Eq2; apply WF.
Qed.

Lemma retag_step_wf σ σ' e e' h0 l T kind :
  mem_expr_step σ.(shp) e (RetagEvt l T kind) h0 e' →
  bor_step h0 σ.(sst) σ.(scs) σ.(snp) σ.(snc)
                    (RetagEvt l T kind)
                  σ'.(shp) σ'.(sst) σ'.(scs) σ'.(snp) σ'.(snc) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α cids nxtp nxtc].
  destruct σ' as [h' α' cids' nxtp' nxtc']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  by eapply retag_wf.
Qed.

(** SysCall step *)
(* Lemma syscall_step_wf σ σ' e e' id efs h0 :
  mem_expr_step FNs e σ.(shp) (SysCallEvt id) e' h0 efs →
  bor_step h0 σ.(sst) σ.(snc) σ.(snp)
                    (SysCallEvt id)
                  σ'.(shp) σ'.(sst) σ'.(snc) σ'.(snp) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α nxtp nxtc]. destruct σ' as [h' α' nxtc' nxtp']. simpl.
  intros BS IS WF.
  inversion BS; clear BS; simplify_eq;
  inversion IS; clear IS; simplify_eq; apply WF.
Qed. *)

Lemma head_step_wf fns σ σ' e e' obs efs :
  head_step fns e σ obs e' σ' efs → Wf σ → Wf σ'.
Proof.
  intros HS WF. inversion HS; [by subst|]. simplify_eq. destruct ev.
  - eapply alloc_step_wf; eauto.
  - eapply dealloc_step_wf; eauto.
  - eapply copy_step_wf; eauto.
  - eapply write_step_wf; eauto.
  - by inversion ExprStep.
  - eapply initcall_step_wf; eauto.
  - eapply endcall_step_wf; eauto.
  - eapply retag_step_wf; eauto.
  - by inversion ExprStep.
  (* - eapply syscall_step_wf; eauto. *)
Qed.
Lemma tstep_wf fns eσ1 eσ2 :
  eσ1 ~{fns}~> eσ2 → Wf eσ1.2 → Wf eσ2.2.
Proof. inversion 1. inversion PRIM. by eapply (head_step_wf fns). Qed.
Lemma rtc_tstep_wf fns eσ1 eσ2 :
  eσ1 ~{fns}~>* eσ2 → Wf eσ1.2 → Wf eσ2.2.
Proof.
  intros SS. induction SS; [done|]. intros WF1. apply IHSS. revert WF1.
  by apply (tstep_wf fns).
Qed.

Lemma retag_nxtp_mono h α nxtp cids c l kind T h' α' nxtp' :
  retag h α nxtp cids c l kind T = Some (h', α', nxtp') →
  (nxtp ≤ nxtp')%nat.
Proof.
  eapply (retag_elim
    (* general goal P *)
    (λ h α nxtp _ _ _ _ _ ohac, ∀ h' α' nxtp',
        ohac = Some (h', α', nxtp') → (nxtp ≤ nxtp')%nat)
    (* invariant for Product's where P1 *)
    (λ _ _ _ _ _ _ _ _ h α nxtp _ _ ohac, ∀ h' α' nxtp',
        ohac = Some (h', α', nxtp') → (nxtp ≤ nxtp')%nat)
    (* invariant for Sum's where P3 *)
    (λ h _ _ α nxtp _ _ _ _ _ _ ohac, ∀ h' α' nxtp',
        ohac = Some (h', α', nxtp') → (nxtp ≤ nxtp')%nat)).
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - (* Reference cases *)
    clear. intros h ?? bor α nxtp cids c rt_kind p_kind T Eq h' α' nxtp'. simpl.
    destruct p_kind as [[]|[]|];
      [| |destruct rt_kind; try by (intros; simplify_eq)..|];
      (case retag_ref as [[[new α1] nxtp1]|] eqn:Eq1; [simpl|done]);
      intros; simplify_eq; eapply retag_ref_nxtp_mono; eauto.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - (* Product inner recursive case *)
    intros ?????????????? IH1 IH2 ???.
    case retag as [hac|]; [|done]. move => /= /IH1 Le. destruct hac as [[]].
    etrans; [|exact Le]. by eapply IH2.
  - naive_solver.
  - (* Sum case *)
    intros ????????? IH Eq ???. case decide => Le; [|done]. by apply IH.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
Qed.

Lemma head_step_nxtp_mono fns σ σ' e e' obs efs :
  head_step fns e σ obs e' σ' efs → (σ.(snp) ≤ σ'.(snp))%nat.
Proof.
  intros HS. inversion HS; [done|]. simplify_eq.
  inversion InstrStep; simplify_eq; simpl; try done; [lia|].
  by eapply retag_nxtp_mono.
Qed.
