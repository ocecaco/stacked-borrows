From stbor Require Import helpers.
From stbor Require Export properties.

(** Steps preserve wellformedness *)

Lemma init_mem_foldr' l n h (m: nat):
  init_mem (l +ₗ m) n h =
  fold_right (λ (i: nat) hi, <[(l +ₗ i):=LitV ☠%V]> hi) h (seq m n).
Proof.
  revert m. induction n as [|n IHn]; intros m; [done|]. simpl. f_equal.
  by rewrite shift_loc_assoc -(Nat2Z.inj_add m 1) Nat.add_1_r IHn.
Qed.
Lemma init_mem_foldr l n h:
  init_mem l n h =
  fold_right (λ (i: nat) hi, <[(l +ₗ i):=LitV ☠%V]> hi) h (seq 0 n).
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

Lemma init_stacks_foldr' l n h si (m: nat):
  init_stacks (l +ₗ m) n h si =
  fold_right (λ (i: nat) hi, <[(l +ₗ i):=mkBorStack [si] None]> hi) h (seq m n).
Proof.
  revert m. induction n as [|n IHn]; intros m; [done|]. simpl. f_equal.
  by rewrite shift_loc_assoc -(Nat2Z.inj_add m 1) Nat.add_1_r IHn.
Qed.
Lemma init_stacks_foldr l n h si:
  init_stacks l n h si =
  fold_right (λ (i: nat) hi, <[(l +ₗ i):=mkBorStack [si] None]> hi) h (seq 0 n).
Proof. by rewrite -init_stacks_foldr' shift_loc_0. Qed.

(** Alloc *)
Lemma alloc_step_wf σ σ' e e' efs h0 l bor T:
  base_step e σ.(cheap) (AllocEvt l bor T) e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (AllocEvt l bor T)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α β clk].
  destruct σ' as [h' α' β' clk']. simpl.
  intros BS IS WF. inversion BS. clear BS. simplify_eq.
  destruct (tsize T) eqn:Eqs.
  - inversion IS; clear IS; simplify_eq; constructor; simpl.
    + rewrite Eqs /=. apply WF.
    + move=> ?? bor /(state_wf_mem_bor _ WF). destruct bor as [|[]]; simpl; lia.
    + rewrite Eqs /= => ? stack /(state_wf_stack_frozen _ WF).
      rewrite /frozen_lt. destruct (stack.(frozen_since)); simpl; lia.
    + rewrite Eqs /= => ?? Eq si In.
      move : (state_wf_stack_item _ WF _ _ Eq _ In).
      destruct si; [simpl; lia|done..].
    + intros ??. rewrite init_stacks_foldr.
      intros [->|Eq]%foldr_gmap_insert_lookup; [done|].
      by apply (state_wf_non_empty _ WF _ _ Eq).
  - inversion IS; clear IS; simplify_eq; constructor; cbn -[ init_mem].
    + rewrite Eqs init_stacks_foldr init_mem_foldr.
      apply foldr_gmap_insert_dom, WF.
    + intros ?? bor. rewrite init_mem_foldr.
      intros [|Eq]%foldr_gmap_insert_lookup; [done|].
      move : (state_wf_mem_bor _ WF _ _ _ Eq).
      destruct bor as [|[]]; simpl; lia.
    + intros ??. rewrite init_stacks_foldr.
      intros [->|Eq]%foldr_gmap_insert_lookup; [done|].
      move : (state_wf_stack_frozen _ WF _ _ Eq).
      rewrite /frozen_lt. destruct stack.(frozen_since); simpl; lia.
    + intros ??. rewrite init_stacks_foldr.
      intros [->|Eq]%foldr_gmap_insert_lookup si.
      * intros ->%elem_of_list_singleton. lia.
      * move => /(state_wf_stack_item _ WF _ _ Eq).
        destruct si; [simpl; lia|done..].
    + intros ??. rewrite init_stacks_foldr.
      intros [->|Eq]%foldr_gmap_insert_lookup; [done|].
      by apply (state_wf_non_empty _ WF _ _ Eq).
Qed.

(** Dealloc *)
Lemma accessN_dealloc_delete' α β l bor n α' (m: nat):
  accessN α β (l +ₗ m) bor n AccessDealloc = Some α' →
  α' = fold_right (λ (i: nat) α, delete (l +ₗ i) α) α (seq m n).
Proof.
  revert α.
  induction n as [|n IHn]; intros α; [by move => [->]|]. simpl.
  case lookup => stack /= ; [|done]. case access1 => stack'; [|done].
  move => /IHn ->. clear. revert m. induction n as [|n IH]; intros m.
  - by rewrite /= shift_loc_0.
  - simpl. f_equal.
    by rewrite shift_loc_assoc -Nat2Z.inj_add -Nat.add_succ_comm Nat2Z.inj_add
               -shift_loc_assoc IH.
Qed.
Lemma accessN_dealloc_delete α β l bor n α':
  accessN α β l bor n AccessDealloc = Some α' →
  α' = fold_right (λ (i: nat) α, delete (l +ₗ i) α) α (seq O n).
Proof. intros. eapply accessN_dealloc_delete'. by rewrite shift_loc_0. Qed.

Lemma dealloc_step_wf σ σ' e e' efs h0 l bor T :
  base_step e σ.(cheap) (DeallocEvt l bor T) e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (DeallocEvt l bor T)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α β clk]. destruct σ' as [h' α' β' clk']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  rewrite (accessN_dealloc_delete α β' l bor (tsize T) α'); [|done].
  constructor; simpl.
  - rewrite free_mem_foldr. apply foldr_gmap_delete_dom, WF.
  - intros ???. rewrite free_mem_foldr.
    intros Eq%foldr_gmap_delete_lookup.
    apply (state_wf_mem_bor _ WF _ _ _ Eq).
  - intros ?? Eq%foldr_gmap_delete_lookup.
    apply (state_wf_stack_frozen _ WF _ _ Eq).
  - intros ?? Eq%foldr_gmap_delete_lookup.
    apply (state_wf_stack_item _ WF _ _ Eq).
  - intros ?? Eq%foldr_gmap_delete_lookup.
    apply (state_wf_non_empty _ WF _ _ Eq).
Qed.

(** Copy *)
Lemma accessN_dom α β l bor n kind α' (ND: kind ≠ AccessDealloc) :
  accessN α β l bor n kind = Some α' →
  dom (gset loc) α ≡ dom (gset loc) α'.
Proof.
  revert α. induction n as [|n IH]; intros α; [by move => /= [-> //]|].
  simpl. destruct (α !! (l +ₗ n)) eqn:Eq; [|done].
  simpl. case access1 => stack' /=; [|done]. intros Eq2.
  have Eq3: dom (gset loc) α' ≡ dom (gset loc) (<[l +ₗ n:=stack']> α).
  { destruct kind; [..|done]; move : Eq2 => /IH <- //. } clear Eq2.
  rewrite Eq3. symmetry. apply dom_map_insert_is_Some. by eexists.
Qed.

Lemma access1'_stack_item stk bor kind β stk' :
  access1' stk bor kind β = Some stk' →
  stk' `suffix_of` stk ∧ (stk ≠ [] → stk' ≠ []).
Proof.
  induction stk as [|si stk IH]; simpl; [done|].
  destruct si; [destruct bor..|].
  - case_match => [|Eq]; [case_match => [[<-//]|//]|].
    destruct (IH Eq) as [??]. split; [by apply suffix_cons_r|intros _].
    destruct stk. done. naive_solver.
  - intros Eq. destruct (IH Eq) as [??].
    split; [by apply suffix_cons_r|intros _]. destruct stk. done. naive_solver.
  - destruct kind; [by move => [<-]|..]; intros Eq; destruct (IH Eq) as [??];
      (split; [by apply suffix_cons_r|intros _]);
      (destruct stk; [done|naive_solver]).
  - destruct kind; [by move => [<-]|..]; case_match => [[->//]|//].
  - case_match => [//|Eq].
    destruct (IH Eq) as [??]; split; [by apply suffix_cons_r|intros _].
    destruct stk; [done|naive_solver].
Qed.

Lemma access1_stack_item β stk stk' bor kind :
  access1 β stk bor kind = Some stk' →
  suffix stk'.(borrows) stk.(borrows) ∧
  (stk.(borrows) ≠ [] → stk'.(borrows) ≠ []) ∧
  stk'.(frozen_since) ⊑ stk.(frozen_since).
Proof.
  rewrite /access1.
  case (frozen_since _) as [t|] eqn:Eqt; rewrite -Eqt;
    [destruct kind|]; [by move => [<-]|..];
    (case access1' as [stk0|] eqn:Eq; [|done]); move => [<-] /=;
    (split; last split; [..|done]); by eapply access1'_stack_item.
Qed.

Lemma accessN_item_lookup α β l bor n kind α' (ND: kind ≠ AccessDealloc) :
  accessN α β l bor n kind = Some α' →
  (∀ (i: nat) stk, (i < n)%nat → α !! (l +ₗ i) = Some stk →
    α' !! (l +ₗ i) = access1 β stk bor kind) ∧
  (∀ (l': loc), (∀ (i: nat), (i < n)%nat → l' ≠ l +ₗ i) → α' !! l' = α !! l').
Proof.
  revert α. induction n as [|n IH]; intros α; simpl.
  { move => [<-]. split; intros ??; by [lia|]. }
  case (α !! (l +ₗ n)) as [stkn|] eqn:Eqn; [|done] => /=.
  case access1 as [stkn'|] eqn: Eqn'; [|done] => /= Eq3'.
  have Eq3 : accessN (<[l +ₗ n:=stkn']> α) β l bor n kind = Some α'
        by destruct kind. clear Eq3'.
  destruct (IH _ Eq3) as [IH1 IH2]. split.
  - intros i stk Lt Eqi. case (decide (i = n)) => Eq'; [subst i|].
    + rewrite Eqi in Eqn. simplify_eq.
      rewrite Eqn' IH2; [by rewrite lookup_insert|].
      move => ?? /shift_loc_inj /Z_of_nat_inj ?. by lia.
    + apply IH1; [lia|]. rewrite lookup_insert_ne; [done|].
      by move => /shift_loc_inj /Z_of_nat_inj ? //.
  - intros l' Lt. rewrite IH2.
    + rewrite lookup_insert_ne; [done|]. move => Eql'. apply (Lt n); by [lia|].
    + move => ??. apply Lt. lia.
Qed.

Lemma accessN_item_dealloc α β l bor n α' :
  accessN α β l bor n AccessDealloc = Some α' →
  (∀ (i: nat), (i < n)%nat → α' !! (l +ₗ i) = None) ∧
  (∀ (l': loc), (∀ (i: nat), (i < n)%nat → l' ≠ l +ₗ i) → α' !! l' = α !! l').
Proof.
  revert α. induction n as [|n IH]; intros α; simpl.
  { move => [<-]. split; intros ??; by [lia|]. }
  case (α !! (l +ₗ n)) as [stkn|] eqn:Eqn; [|done] => /=.
  case access1 as [stkn'|] eqn: Eqn'; [|done] => /= Eq3.
  destruct (IH _ Eq3) as [IH1 IH2]. split.
  - intros i Lt. case (decide (i = n)) => Eq'; [subst i|].
    + rewrite IH2; [by apply lookup_delete|].
      move => ?? /shift_loc_inj /Z_of_nat_inj ?. by lia.
    + apply IH1. by lia.
  - intros l' Lt. rewrite IH2.
    + rewrite lookup_delete_ne; [done|]. move => Eql'. apply (Lt n); by [lia|].
    + move => ??. apply Lt. lia.
Qed.

Lemma accessN_stack α β l bor n kind α' (ND: kind ≠ AccessDealloc) :
  accessN α β l bor n kind = Some α' →
  ∀ (l: loc) stk', α' !! l = Some stk' → ∃ stk, α !! l = Some stk ∧
    stk'.(borrows) `suffix_of` stk.(borrows) ∧
    (stk.(borrows) ≠ [] → stk'.(borrows) ≠ []) ∧
    stk'.(frozen_since) ⊑ stk.(frozen_since).
Proof.
  revert α. induction n as [|n IH]; intros α; [move => /= [->]; naive_solver|].
  simpl. destruct (α !! (l +ₗ n)) as [stk0|] eqn:Eq; [|done].
  simpl. destruct (access1 β stk0 bor kind)  as [stk0'|] eqn: Eq1; [|done].
  simpl. intros Eq2' l' stk'.
  have Eq2: accessN (<[l +ₗ n:=stk0']> α) β l bor n kind = Some α'
      by destruct kind. clear Eq2'.
  case (decide (l' = (l +ₗ n))) => [-> Eq'|?].
  - exists stk0. split; [done|].
    have ?: stk0' = stk'.
    { destruct (accessN_item_lookup _ _ _ _ _ _ _ ND Eq2) as [_ HL].
      move : Eq'. rewrite HL.
      - by rewrite lookup_insert => [[->]].
      - move => ?? /shift_loc_inj /Z_of_nat_inj ?. by lia. } subst stk0'.
    by eapply access1_stack_item.
  - move => /(IH _ Eq2) [stk [Eq' SUFF]]. exists stk. split; [|done].
    move : Eq'. by rewrite lookup_insert_ne.
Qed.

Lemma accessN_wf_non_empty α β l bor n kind α' :
  accessN α β l bor n kind = Some α' → wf_non_empty α → wf_non_empty α'.
Proof.
  revert α. induction n as [|n IH]; intros α; [move => /= [->//]|].
  simpl. destruct (α !! (l +ₗ n)) as [stk0|] eqn:Eq; [|done].
  simpl. destruct (access1 β stk0 bor kind)  as [stk0'|] eqn: Eq1; [|done].
  simpl. intros Eq2' WF l' stk'.
  case (decide (l' = (l +ₗ n))) => [-> Eq'|?].
  - have ND: kind ≠ AccessDealloc.
    { move => ?. subst kind. move : Eq2' => /accessN_item_dealloc [_ HI].
      move : Eq'. rewrite HI; [by rewrite lookup_delete|].
      move => ?? /shift_loc_inj /Z_of_nat_inj ?. by lia. }
    have Eq2: accessN (<[l +ₗ n:=stk0']> α) β l bor n kind = Some α'
      by destruct kind. clear Eq2'.
    have ?: stk0' = stk'.
    { destruct (accessN_item_lookup _ _ _ _ _ _ _ ND Eq2) as [_ HL].
      move : Eq'. rewrite HL.
      - by rewrite lookup_insert => [[->]].
      - move => ?? /shift_loc_inj /Z_of_nat_inj ?. by lia. } subst stk0'.
    destruct kind; simplify_eq; by eapply access1_stack_item; eauto.
  - destruct kind; apply (IH _ Eq2') => l1 ?.
    + case (decide (l1 = l +ₗ n)) => [->|?];
        [rewrite lookup_insert|rewrite lookup_insert_ne;[by apply WF|done]];
      intros; simplify_eq; by eapply access1_stack_item; eauto.
    + case (decide (l1 = l +ₗ n)) => [->|?];
        [rewrite lookup_insert|rewrite lookup_insert_ne;[by apply WF|done]];
      intros; simplify_eq; by eapply access1_stack_item; eauto.
    + case (decide (l1 = l +ₗ n)) => [->|?];
        [by rewrite lookup_delete|rewrite lookup_delete_ne;[by apply WF|done]].
Qed.

Lemma copy_step_wf σ σ' e e' efs h0 l bor T vl :
  base_step e σ.(cheap) (CopyEvt l bor T vl) e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (CopyEvt l bor T vl)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ' ∧ vl <<b σ'.(cclk).
Proof.
  destruct σ as [h α β clk]. destruct σ' as [h' α' β' clk']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq. split; [|done].
  constructor; simpl.
  - rewrite -(accessN_dom α _ l bor (tsize T) AccessRead); [by apply WF|done..].
  - apply WF.
  - intros l' stk'.
    move=> /(accessN_stack α β' l bor (tsize T) AccessRead α' _ _ l' stk') Eq.
    destruct Eq as [stk [Eq [_ [_ Sub2]]]]; [done..|].
    rewrite /frozen_lt. destruct stk'.(frozen_since) as [t'|]; [|done].
    have Eq2 := (state_wf_stack_frozen _ WF _ _ Eq). move : Eq2.
    rewrite /frozen_lt. destruct stk.(frozen_since) as [t|]; [|done].
    intros. eapply le_lt_trans; [by apply Sub2|done].
  - intros l' stk'.
    move=> /(accessN_stack α β' l bor (tsize T) AccessRead α' _ _ l' stk') Eq.
    destruct Eq as [stk [Eq [Sub1 _]]]; [done..|].
    intros si Ini. apply (state_wf_stack_item _ WF _ _ Eq).
    move : Ini. by apply elem_of_list_suffix_proper.
    (* intros l' bor' [i Eqi]%elem_of_list_lookup.
    have Eqbor: h' !! (l +ₗ i) = Some (LitV (LitLoc l' bor')).
    { rewrite -Eqi. by eapply VALUES, lookup_lt_Some. }
    by apply (state_wf_mem_bor _ WF _ _ _ Eqbor). *)
  - intros l' stk'. eapply accessN_wf_non_empty; eauto. by apply WF.
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

Lemma write_step_wf σ σ' e e' efs h0 l bor T vl :
  base_step e σ.(cheap) (WriteEvt l bor T vl) e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (WriteEvt l bor T vl)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α β clk]. destruct σ' as [h' α' β' clk']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl.
  - rewrite -(accessN_dom α β' l bor (tsize T) AccessWrite); [|done..].
    rewrite write_mem_dom; [by apply WF|done].
  - move => l0 l' bor'. destruct (write_mem_lookup l vl h) as [IN OUT].
    case (decide (l0.1 = l.1)) => Eq1.
    + have Eql0: l0 = (l +ₗ (l0.2 - l.2)).
      { rewrite /shift_loc -Eq1. destruct l0; simpl. f_equal. by lia. }
      case (decide (0 ≤ l0.2 - l.2 < length vl)) => [[Le Lt]|NLe].
      * rewrite Eql0 -(Z2Nat.id _ Le) IN.
        intros ?%elem_of_list_lookup_2. by eapply BOR.
        rewrite -(Nat2Z.id (length vl)) -Z2Nat.inj_lt; [done|lia..].
      * rewrite OUT; [by apply (state_wf_mem_bor _ WF)|].
        move => i Lt Eq. rewrite Eql0 in Eq. apply shift_loc_inj in Eq.
        apply NLe. rewrite Eq. lia.
    + rewrite OUT; [by apply (state_wf_mem_bor _ WF)|].
      move => ? _ Eq. apply Eq1. rewrite Eq. by apply shift_loc_block.
  - intros l' stk'.
    move => /(accessN_stack α β' l bor (tsize T) AccessWrite α' _ _ l' stk') Eq.
    destruct Eq as [stk [Eq [_ [_ Sub2]]]]; [done..|].
    move : (state_wf_stack_frozen _ WF _ _ Eq).
    rewrite /frozen_lt. destruct stk'.(frozen_since) as [t'|]; [|done].
    destruct stk.(frozen_since) as [t|]; [|done]. intros.
    eapply le_lt_trans; [by apply Sub2|done].
  - intros l' stk'.
    move => /(accessN_stack α β' l bor (tsize T) AccessWrite α' _ _ l' stk') Eq.
    destruct Eq as [stk [Eq [Sub1 _]]]; [done..|].
    intros si Ini. apply (state_wf_stack_item _ WF _ _ Eq).
    move : Ini. by apply elem_of_list_suffix_proper.
  - intros l' stk'. eapply accessN_wf_non_empty; eauto. by apply WF.
Qed.

(** Deref *)
Lemma deref_step_wf σ σ' e e' efs h0 l bor T mut :
  base_step e σ.(cheap) (DerefEvt l bor T mut) e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (DerefEvt l bor T mut)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α β clk]. destruct σ' as [h' α' β' clk']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl; apply WF.
Qed.

(** NewCall *)
Lemma newcall_step_wf σ σ' e e' efs h0 n :
  base_step e σ.(cheap) (NewCallEvt n) e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (NewCallEvt n)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α β clk]. destruct σ' as [h' α' β' clk']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl; [apply WF..| |apply WF].
  intros ?? Eq ? In. have SI := state_wf_stack_item _ WF _ _ Eq _ In.
  destruct si; [done..|]. rewrite lookup_insert_is_Some'. by right.
Qed.

(** EndCall *)
Lemma endcall_step_wf σ σ' e e' efs h0 n :
  base_step e σ.(cheap) (EndCallEvt n) e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (EndCallEvt n)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α β clk]. destruct σ' as [h' α' β' clk']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl; [apply WF..| |apply WF].
  intros ?? Eq ? In. have SI := state_wf_stack_item _ WF _ _ Eq _ In.
  destruct si; [done..|]. rewrite lookup_insert_is_Some'. by right.
Qed.

(** Retag *)

(* Retag bor *)
Lemma bor_value_included_trans bor :
  Proper ((≤)%nat ==> impl) (bor_value_included bor).
Proof.
  intros clk clk' Le. rewrite /bor_value_included.
  by destruct bor as [|[]]; simpl; intros ?; [lia..|done].
Qed.

Lemma retag_ref_clk_mono h α β clk l bor T mut kind is_2p bor' α' clk' :
  retag_ref h α β clk l bor T mut kind is_2p = Some (bor', α', clk') →
  (clk ≤ clk')%nat.
Proof.
  rewrite /retag_ref.
  case tsize => ?; [by intros; simplify_eq|].
  case reborrow eqn:Eqb; [simpl|done].
  case is_2p; [|intros; simplify_eq; by lia].
  destruct mut as [[]|]; [|done..].
  case visit_freeze_sensitive => ?; [|done]. simpl. intros. simplify_eq. by lia.
Qed.

Lemma retag_ref_clk_bor_mono h α β clk l bor T mut kind is_2p bor' α' clk' :
  retag_ref h α β clk l bor T mut kind is_2p = Some (bor', α', clk') →
  bor <b clk → bor' <b clk'.
Proof.
  rewrite /retag_ref.
  case tsize => ?; [by intros; simplify_eq|].
  case reborrow eqn:Eqb; [simpl|done].
  case is_2p; last first.
  { intros; simplify_eq. by destruct mut as [[]|]; [simpl;lia..|done]. }
  destruct mut as [[]|]; [|done..].
  case visit_freeze_sensitive => ?; [|done]. simpl. intros. simplify_eq.
  simpl. by lia.
Qed.

(* Retag frozen_since *)
Lemma wf_stack_frozen_mono α :
  Proper ((≤)%nat ==> impl) (wf_stack_frozen α).
Proof. move=> ??? WF ?? /WF. rewrite /frozen_lt. by case_match; [lia|done]. Qed.

Lemma add_barrier_frozen_lt stk clk c :
  frozen_lt stk clk → frozen_lt (add_barrier stk c) clk.
Proof.
  rewrite /frozen_lt /add_barrier.
  destruct stk as [[|[t| |c'] ss] [tf|]]; simpl; [done..| |]; by case decide.
Qed.

Lemma suffix_stack_item_included stk stk' β clk  :
  stk'.(borrows) `suffix_of` stk.(borrows) →
  stack_item_included stk β clk → stack_item_included stk' β clk.
Proof. by move => SF HI si /(elem_of_list_suffix_proper _ _ _ SF) /HI. Qed.

Lemma access1_wf_stack β stk bor kind stk' clk :
  access1 β stk bor kind = Some stk' →
  (frozen_lt stk clk → frozen_lt stk' clk) ∧
  (stk.(borrows) ≠ [] → stk'.(borrows) ≠ []) ∧
  (stack_item_included stk β clk → stack_item_included stk' β clk).
Proof.
  rewrite /access1. case frozen_since.
  - case kind; [by intros; simplify_eq|..];
      (case access1' eqn:Eq; [simpl; intros; simplify_eq|done]);
      (split; [done|split]; [by eapply access1'_stack_item
          |by eapply suffix_stack_item_included, access1'_stack_item]).
  - case access1' eqn:Eq; [simpl; intros; simplify_eq|done].
    split; [done|split]; [by eapply access1'_stack_item
          |by eapply suffix_stack_item_included, access1'_stack_item].
Qed.

Lemma create_borrow_wf_stack stk bor kind stk' clk (INCL: bor <b clk):
  create_borrow stk bor kind = Some stk' →
  (frozen_lt stk clk → frozen_lt stk' clk) ∧
  (∀ β, stack_item_included stk β clk → stack_item_included stk' β clk).
Proof.
  rewrite /create_borrow. intros Eq. split.
  - destruct kind, bor as [|[t|]]; simpl; [| | |done| |done|..];
      destruct stk.(frozen_since) as [ft|]; try done; simpl;
      try by intros; simplify_eq.
    move : Eq. case decide; [|done]. intros. by simplify_eq.
  - destruct bor as [|[t|]]; simpl.
    + destruct kind; [|done|]; (destruct stk.(frozen_since); [done|]);
        simplify_eq; by move => β HI si /= /elem_of_cons [->|]; [|apply HI].
    + destruct kind; destruct stk.(frozen_since); try done; simplify_eq;
        [|move : Eq; case decide; [|done]; by intros; simplify_eq|naive_solver|];
        move => β HI si /=;
        (destruct stk.(borrows) as [|[]] eqn:Eq;
          [by move => /elem_of_list_singleton ->|
           rewrite -Eq elem_of_cons => [[->//|]]; by apply HI|
           rewrite -Eq; by apply HI|
           rewrite -Eq elem_of_cons => [[->//|]]; by apply HI]).
    + destruct kind; destruct stk.(frozen_since); try done; simplify_eq;
        move => β HI si /=;
        (destruct stk.(borrows) as [|[]] eqn:Eq;
          [by move => /elem_of_list_singleton ->|
           rewrite -Eq elem_of_cons => [[->//|]]; by apply HI|
           rewrite -Eq; by apply HI|
           rewrite -Eq elem_of_cons => [[->//|]]; by apply HI]).
Qed.

Lemma reborrow1_wf_stack_frozen stk bor bor' kind β bar clk stk':
  bor' <b clk →
  reborrow1 stk bor bor' kind β bar = Some stk' →
  frozen_lt stk clk → frozen_lt stk' clk.
Proof.
  rewrite /reborrow1.
  case (deref1 stk bor kind) as [oi|] eqn:Eq; [|done]. simpl.
  destruct bar as [c|]; [|destruct oi].
  - case access1 as [stk1|] eqn:Eq1; [simpl|done].
    intros; eapply create_borrow_wf_stack; eauto.
    apply add_barrier_frozen_lt. by eapply access1_wf_stack; eauto.
  - case (deref1 stk bor' kind) as [[i'|]|] eqn:Eq'.
    + case decide => ?; [case_match; [|done]; intros; by simplify_eq|].
      case access1 as [stk1|] eqn:Eq1; [simpl|done].
      intros; eapply create_borrow_wf_stack; eauto;
        by eapply access1_wf_stack; eauto.
    + case_match; [by intros; simplify_eq|done].
    + case access1 as [stk1|] eqn:Eq1; [simpl|done].
      intros; eapply create_borrow_wf_stack; eauto;
        by eapply access1_wf_stack; eauto.
  - case (deref1 stk bor' kind) as [[i'|]|] eqn:Eq'.
    + case access1 as [stk1|] eqn:Eq1; [simpl|done].
      intros; eapply create_borrow_wf_stack; eauto;
        by eapply access1_wf_stack; eauto.
    + case_match; [by intros; simplify_eq|done].
    + case access1 as [stk1|] eqn:Eq1; [simpl|done].
      intros; eapply create_borrow_wf_stack; eauto;
        by eapply access1_wf_stack; eauto.
Qed.

(* Retag non empty & stack item *)
Lemma create_borrow_wf_non_empty stk bor kind stk' :
  create_borrow stk bor kind = Some stk' →
  stk.(borrows) ≠ [] → stk'.(borrows) ≠ [].
Proof.
  rewrite /create_borrow.
  destruct kind, bor as [|[t|]]; simpl; [| | |done| |done|..];
    destruct stk.(frozen_since) as [ft|]; try done; simpl;
    try (by intros ?; simplify_eq); [| |case decide => _; [|done] | |];
    intros ?; simplify_eq; [| |done| |];
    by  destruct stk.(borrows) as [|[]].
Qed.

Lemma add_barrier_wf_non_empty stk c :
  stk.(borrows) ≠ [] → (add_barrier stk c).(borrows) ≠ [].
Proof.
  rewrite /add_barrier.
  destruct stk as [[|[t| |c'] ss] [tf|]]; simpl; [done..| |]; by case decide.
Qed.

Lemma reborrow1_wf_non_empty stk bor bor' kind β bar stk':
  reborrow1 stk bor bor' kind β bar = Some stk' →
  stk.(borrows) ≠ [] → stk'.(borrows) ≠ [].
Proof.
  rewrite /reborrow1.
  case (deref1 stk bor kind) as [oi|] eqn:Eq; [|done]. simpl.
  destruct bar as [c|]; [|destruct oi].
  - case access1 as [stk1|] eqn:Eq1; [simpl|done].
    intros; eapply create_borrow_wf_non_empty; eauto.
    apply add_barrier_wf_non_empty. by eapply access1_stack_item.
  (* TODO: duplicated proof *)
  - case (deref1 stk bor' kind) as [[i'|]|] eqn:Eq'.
    + case decide => ?; [case_match; [|done]; intros; by simplify_eq|].
      case access1 as [stk1|] eqn:Eq1; [simpl|done].
      intros; eapply create_borrow_wf_non_empty; eauto;
        by eapply access1_stack_item.
    + case_match; [by intros; simplify_eq|done].
    + case access1 as [stk1|] eqn:Eq1; [simpl|done].
      intros; eapply create_borrow_wf_non_empty; eauto;
        by eapply access1_stack_item.
  - case (deref1 stk bor' kind) as [[i'|]|] eqn:Eq'.
    + case access1 as [stk1|] eqn:Eq1; [simpl|done].
      intros; eapply create_borrow_wf_non_empty; eauto;
        by eapply access1_stack_item.
    + case_match; [by intros; simplify_eq|done].
    + case access1 as [stk1|] eqn:Eq1; [simpl|done].
      intros; eapply create_borrow_wf_non_empty; eauto;
        by eapply access1_stack_item.
Qed.

Lemma wf_stack_item_mono α β :
  Proper ((≤)%nat ==> impl) (wf_stack_item α β).
Proof. move=> ??? WF ?? /WF Hf ? /Hf. case_match; [lia|done..]. Qed.

Lemma add_barrier_stack_item_included stk clk c β :
  stk.(borrows) ≠ [] → is_Some (β !! c) →
  stack_item_included stk β clk → stack_item_included (add_barrier stk c) β clk.
Proof.
  rewrite /stack_item_included /add_barrier.
  destruct stk as [[|[t| |c'] ss] [tf|]]; simpl => // ?? HI si;
    [by move => /elem_of_cons [->|/HI]..| |];
    (case decide => ? ; [subst|]; simpl;
      move => /elem_of_cons [->//|] => In; apply HI; by right).
Qed.

Lemma reborrow1_wf_stack_item stk bor bor' kind β bar clk stk':
  stk.(borrows) ≠ [] →
  match bar with Some c => is_Some (β !! c) | _ => True end →
  bor' <b clk → reborrow1 stk bor bor' kind β bar = Some stk' →
  stack_item_included stk β clk → stack_item_included stk' β clk.
Proof.
  rewrite /reborrow1.
  case (deref1 stk bor kind) as [oi|] eqn:Eq; [|done]. simpl.
  destruct bar as [c|]; [|destruct oi].
  - case access1 as [stk1|] eqn:Eq1; [simpl|done].
    intros; eapply create_borrow_wf_stack; eauto.
    apply add_barrier_stack_item_included; eauto; by eapply access1_wf_stack.
  - case (deref1 stk bor' kind) as [[i'|]|] eqn:Eq'.
    + case decide => ?; [case_match; [|done]; intros; by simplify_eq|].
      case access1 as [stk1|] eqn:Eq1; [simpl|done].
      intros; eapply create_borrow_wf_stack; eauto;
        by eapply access1_wf_stack.
    + case_match; [by intros; simplify_eq|done].
    + case access1 as [stk1|] eqn:Eq1; [simpl|done].
      intros; eapply create_borrow_wf_stack; eauto;
        by eapply access1_wf_stack.
  - case (deref1 stk bor' kind) as [[i'|]|] eqn:Eq'.
    + case access1 as [stk1|] eqn:Eq1; [simpl|done].
      intros; eapply create_borrow_wf_stack; eauto;
        by eapply access1_wf_stack.
    + case_match; [by intros; simplify_eq|done].
    + case access1 as [stk1|] eqn:Eq1; [simpl|done].
      intros; eapply create_borrow_wf_stack; eauto;
        by eapply access1_wf_stack.
Qed.

Lemma reborrowN_wf_stack α β clk l n bor bor' kind bar α'
  (INCL: bor' <b clk)
  (BAR : match bar with Some c => is_Some (β !! c) | _ => True end) :
  reborrowN α β l n bor bor' kind bar = Some α' →
  wf_stack_frozen α clk ∧ wf_stack_item α β clk ∧ wf_non_empty α →
  dom (gset loc) α ≡ dom (gset loc) α' ∧
  wf_stack_frozen α' clk ∧ wf_stack_item α' β clk ∧ wf_non_empty α'.
Proof.
  revert α.
  induction n as [|n IH]; intros α; simpl; [by intros ?; simplify_eq|].
  case lookup as [stk|] eqn:Eqs; [simpl|done].
  case reborrow1 as [stk'|] eqn:Eq1; [simpl|done].
  intros Eq2 [WF1 [WF2 WF3]].
  destruct (IH (<[l +ₗ n:=stk']> α) Eq2) as (EqD & ?);
    [|split; last done]; last first.
  { rewrite -EqD. symmetry. apply dom_map_insert_is_Some. by eexists. }
  split; last split; intros l' stk0;
  (case (decide (l' = l +ₗ n)) => ?;
    [subst l'; rewrite lookup_insert; intros ?; simplify_eq
    |rewrite lookup_insert_ne; [|done]]).
  - eapply reborrow1_wf_stack_frozen; eauto.
  - apply WF1.
  - eapply reborrow1_wf_stack_item; eauto.
  - apply WF2.
  - eapply reborrow1_wf_non_empty; eauto.
  - apply WF3.
Qed.

Lemma reborrowBlock_wf_stack α β clk l n bor bor' kind bar α'
  (INCL: bor' <b clk)
  (BAR : match bar with Some c => is_Some (β !! c) | _ => True end) :
  reborrowBlock α β l n bor bor' kind bar = Some α' →
  wf_stack_frozen α clk ∧ wf_stack_item α β clk ∧ wf_non_empty α →
  dom (gset loc) α ≡ dom (gset loc) α' ∧
  wf_stack_frozen α' clk ∧ wf_stack_item α' β clk ∧ wf_non_empty α'.
Proof.
  rewrite /reborrowBlock. case xorb; [done|by eapply reborrowN_wf_stack].
Qed.

Lemma unsafe_action_wf_stack
  (f: bstacks → _ → _ → _ → _) α l last fs us α' lc' β clk :
  (∀ α1 α2 l n b, f α1 l n b = Some α2 →
    wf_stack_frozen α1 clk ∧ wf_stack_item α1 β clk ∧ wf_non_empty α1 →
    dom (gset loc) α1 ≡ dom (gset loc) α2 ∧
    wf_stack_frozen α2 clk ∧ wf_stack_item α2 β clk ∧ wf_non_empty α2) →
  unsafe_action f α l last fs us = Some (α', lc') →
  wf_stack_frozen α clk ∧ wf_stack_item α β clk ∧ wf_non_empty α →
  dom (gset loc) α ≡ dom (gset loc) α' ∧
  wf_stack_frozen α' clk ∧ wf_stack_item α' β clk ∧ wf_non_empty α'.
Proof.
  intros Hf. rewrite /unsafe_action.
  case f as [α1|] eqn:Eq1; [simpl|done].
  case (f α1) as [α2|] eqn:Eq2; [simpl|done]. intros ? Eq. simplify_eq.
  destruct (Hf _ _ _ _ _ Eq1) as [EqD1 ?]; [done|].
  destruct (Hf _ _ _ _ _ Eq2) as [EqD2 ?]; [done|].
  split; [|done]. by rewrite EqD1 EqD2.
Qed.

Lemma visit_freeze_sensitive'_wf_stack h l (f: bstacks → _ → _ → _ → _)
  α α' last cur T lc' β clk :
  let Hα α1 α2 :=
    (wf_stack_frozen α1 clk ∧ wf_stack_item α1 β clk ∧ wf_non_empty α1 →
      dom (gset loc) α1 ≡ dom (gset loc) α2 ∧
      wf_stack_frozen α2 clk ∧ wf_stack_item α2 β clk ∧ wf_non_empty α2) in
  let HF f α1 α2 := (∀ l n b, f α1 l n b = Some α2 → Hα α1 α2) in
  (∀ α1 α2, HF f α1 α2) →
  visit_freeze_sensitive' h l f α last cur T = Some (α', lc') →
  wf_stack_frozen α clk ∧ wf_stack_item α β clk ∧ wf_non_empty α →
  dom (gset loc) α ≡ dom (gset loc) α' ∧
  wf_stack_frozen α' clk ∧ wf_stack_item α' β clk ∧ wf_non_empty α'.
Proof.
  intros Hα HF.
  apply (visit_freeze_sensitive'_elim
    (* general goal P *)
    (λ _ _ f α _ _ _ oalc, ∀ α' lc',
      (∀ α1 α2, HF f α1 α2) → oalc = Some (α', lc') → Hα α α')
    (λ _ _ f _ _ _ _ α _ _ _ oalc, ∀ α' lc',
      (∀ α1 α2, HF f α1 α2) → oalc = Some (α', lc') → Hα α α')
    (λ _ _ _ _ _ f α _ _ _ oalc, ∀ α' lc',
      (∀ α1 α2, HF f α1 α2) → oalc = Some (α', lc') → Hα α α')); rewrite /HF /Hα.
  - naive_solver.
  - naive_solver.
  - (* Unsafe case *)
    intros _ ????????. by apply unsafe_action_wf_stack.
  - (* Union case *)
    intros _?????????. case is_freeze; [by intros; simplify_eq|].
    by apply unsafe_action_wf_stack.
  - naive_solver.
  - naive_solver.
  - (* Product case *)
    intros ???????????? IH1 IH2 ?? Hf.
    case visit_freeze_sensitive' as [alc|]; [simpl|done]. destruct alc as [[]].
    move => /IH1 IH1' WF.
    destruct (IH1' Hf) as [EqD ?]; [by eapply IH2|]. split; [|done].
    rewrite -EqD. by eapply IH2.
  - naive_solver.
  - naive_solver.
  - (* Sum case *)
    intros ???????? IH Eq ???. case decide => Le; [|done].
    case visit_freeze_sensitive'_clause_6_clause_1_visit_lookup
      as [[]|] eqn:Eq1; [simpl|done].
    intros. simplify_eq. by eapply IH.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
Qed.

Lemma visit_freeze_sensitive_wf_stack h l T (f: bstacks → _ → _ → _ → _)
  clk β α α' :
  (∀ α1 α2 l n b, f α1 l n b = Some α2 →
    wf_stack_frozen α1 clk ∧ wf_stack_item α1 β clk ∧ wf_non_empty α1 →
    dom (gset loc) α1 ≡ dom (gset loc) α2 ∧
    wf_stack_frozen α2 clk ∧ wf_stack_item α2 β clk ∧ wf_non_empty α2) →
  visit_freeze_sensitive h l T f α = Some α' →
  wf_stack_frozen α clk ∧ wf_stack_item α β clk ∧ wf_non_empty α →
  dom (gset loc) α ≡ dom (gset loc) α' ∧
  wf_stack_frozen α' clk ∧ wf_stack_item α' β clk ∧ wf_non_empty α'.
Proof.
  intros Hf. rewrite /visit_freeze_sensitive.
  case visit_freeze_sensitive' as [[α1 [last cur]]|] eqn:Eq; [|done].
  move => Eqf WF.
  move : Eq => /visit_freeze_sensitive'_wf_stack WF'.
  destruct (WF' _ _ Hf WF) as [EqD WF1]. rewrite EqD.
  by eapply Hf; eauto.
Qed.

Lemma reborrow_wf_stack h α β clk l bor T bar bor' α'
  (INCL: bor' <b clk)
  (BAR : match bar with Some c => is_Some (β !! c) | _ => True end) :
  reborrow h α β l bor T bar bor' = Some α' →
  wf_stack_frozen α clk ∧ wf_stack_item α β clk ∧ wf_non_empty α →
  dom (gset loc) α ≡ dom (gset loc) α' ∧
  wf_stack_frozen α' clk ∧ wf_stack_item α' β clk ∧ wf_non_empty α'.
Proof.
  rewrite /reborrow. destruct bor' as [|[]].
  - by eapply reborrowBlock_wf_stack; eauto.
  - apply visit_freeze_sensitive_wf_stack.
    intros ?????? []. by eapply reborrowBlock_wf_stack.
  - by eapply reborrowBlock_wf_stack; eauto.
Qed.

Lemma retag_ref_wf_stack h α β clk x l bor T mut bar is_2p bor' α' clk'
  (BAR : match bar with Some c => is_Some (β !! c) | _ => True end)
  (Eqx: h !! x = Some $ LitV (LitLoc l bor)) :
  retag_ref h α β clk l bor T mut bar is_2p = Some (bor', α', clk') →
  wf_mem_bor h clk → wf_stack_frozen α clk →
  wf_stack_item α β clk → wf_non_empty α →
  dom (gset loc) h ≡ dom (gset loc) (<[x:=LitV (LitLoc l bor')]> h) ∧
  wf_mem_bor (<[x:=LitV (LitLoc l bor')]> h) clk' ∧
  dom (gset loc) α ≡ dom (gset loc) α' ∧ wf_stack_frozen α' clk' ∧
  wf_stack_item α' β clk' ∧ wf_non_empty α'.
Proof.
  intros RE WF1 WF2 WF3 WF4. split; last split.
  { symmetry; apply dom_map_insert_is_Some; by eexists. }
  { intros  x' l' bor1. case (decide (x' = x)) => ?; [subst x'|].
    - rewrite lookup_insert => ?. simplify_eq.
      by eapply retag_ref_clk_bor_mono; eauto.
    - rewrite lookup_insert_ne; [|done].
      move => /WF1. apply bor_value_included_trans.
      by eapply retag_ref_clk_mono. }
  move : RE WF2 WF3 WF4.
  rewrite /retag_ref. case tsize eqn:Eq; [by intros; simplify_eq|].
  case reborrow as [α1|] eqn:Eq1; [simpl|done].
  destruct is_2p; [destruct mut as [[]|]|]; [|done..|].
  - case visit_freeze_sensitive as [α2|] eqn:Eq2; [simpl|done].
    intros ?. simplify_eq. intros ???.
    move : Eq2 => /visit_freeze_sensitive_wf_stack WF.
    have BOR: (UniqB clk) <b S (S clk) by (simpl; lia).
    edestruct (reborrow_wf_stack h α β (S (S clk)) _ _ _ _ _ α1 BOR BAR Eq1)
    as [EqD ?].
    + split; last split; [..|done].
      * eapply wf_stack_frozen_mono; [|eauto]. by lia.
      * eapply wf_stack_item_mono; [|eauto]. by lia.
    + rewrite EqD. apply WF; [|done].
      intros ?????. apply reborrowBlock_wf_stack; [simpl; by lia|done].
  - intros ?. simplify_eq. intros WF2 WF3 WF4.
    eapply reborrow_wf_stack; eauto.
    + by destruct mut as [[]|]; simpl; [lia..|].
    + split; last split; [..|done].
      * eapply wf_stack_frozen_mono; [|exact WF2]. by lia.
      * eapply wf_stack_item_mono; [|exact WF3]. by lia.
Qed.

Lemma retag_wf_stack h α clk β l kind T h' α' clk' :
  let Hα h h' α α' clk clk' β kind :=
    (borrow_barrier_Some β kind →
      wf_mem_bor h clk → wf_stack_frozen α clk →
      wf_stack_item α β clk → wf_non_empty α →
      dom (gset loc) h ≡ dom (gset loc) h' ∧
      wf_mem_bor h' clk' ∧ dom (gset loc) α ≡ dom (gset loc) α' ∧
      wf_stack_frozen α' clk' ∧
      wf_stack_item α' β clk' ∧ wf_non_empty α') in
  retag h α clk β l kind T = Some (h', α', clk') →
  Hα h h' α α' clk clk' β kind.
Proof.
  intros Hα.
  eapply (retag_elim
    (* general goal P *)
    (λ h α clk β _ kind _ ohac, ∀ h' α' clk',
        ohac = Some (h', α', clk') → Hα h h' α α' clk clk' β kind)
    (* invariant for Product's where P1 *)
    (λ _ _ _ β _ kind _ h α clk _ _ ohac, ∀ h' α' clk',
        ohac = Some (h', α', clk') → Hα h h' α α' clk clk' β kind)
    (* invariant for Sum's where P3 *)
    (λ h _ _ α clk β kind _ _ _ ohac, ∀ h' α' clk',
        ohac = Some (h', α', clk') → Hα h h' α α' clk clk' β kind)); rewrite /Hα.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - (* Reference cases *)
    clear. intros h ?? bor α clk β rt_kind p_kind T Eq h' α' clk'.
    destruct p_kind as [mut| |];
      [|destruct rt_kind; try by (intros; simplify_eq)|];
      (case retag_ref as [[[bor' α1] clk1]|] eqn:Eq1; [simpl|done]);
      intros ???; simplify_eq; eapply retag_ref_wf_stack; eauto; [|done..].
      by destruct rt_kind.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - (* Product inner recursive case *)
    intros ????????????? IH1 IH2 ???.
    case retag as [hac|]; [|done]. move => /= /IH1 WF BS WF1 WF2 WF3 WF4.
    destruct hac as [[]].
    destruct (WF BS) as (EqD1 & ? & EqD2 & ?); [by eapply IH2..|].
    split; last split; last split; [|done| |done..];
      [rewrite -EqD1|rewrite -EqD2]; by eapply IH2.
  - naive_solver.
  - naive_solver.
  - (* Sum case *)
    intros ???????? IH Eq ???. case decide => Le; [|done]. by apply IH.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
Qed.

Lemma retag_step_wf σ σ' e e' efs h0 l T kind :
  base_step e σ.(cheap) (RetagEvt l T kind) e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (RetagEvt l T kind)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α β clk]. destruct σ' as [h' α' β' clk']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  have ?: borrow_barrier_Some β' kind by (destruct kind; [eexists|done..]).
  move : RETAG => /retag_wf_stack WF'.
  destruct WF' as (Eq1 & ? & Eq2 & ? & ? & ?); [done|apply WF..|].
  constructor; simpl; [|done..].
  by rewrite -Eq1 -Eq2; apply WF.
Qed.

(** Silent step *)
Lemma silent_step_wf σ σ' e e' efs h0 :
  base_step e σ.(cheap) SilentEvt e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    SilentEvt
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α β clk]. destruct σ' as [h' α' β' clk']. simpl.
  intros BS IS WF.
  inversion BS; clear BS; simplify_eq;
  inversion IS; clear IS; simplify_eq; apply WF.
Qed.

(** SysCall step *)
Lemma syscall_step_wf σ σ' e e' id efs h0 :
  base_step e σ.(cheap) (SysCallEvt id) e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (SysCallEvt id)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α β clk]. destruct σ' as [h' α' β' clk']. simpl.
  intros BS IS WF.
  inversion BS; clear BS; simplify_eq;
  inversion IS; clear IS; simplify_eq; apply WF.
Qed.

Lemma head_step_wf σ σ' e e' obs efs :
  head_step e σ obs e' σ' efs → Wf σ → Wf σ'.
Proof.
  intros HS WF. inversion HS. simplify_eq. destruct ev.
  - eapply alloc_step_wf; eauto.
  - eapply dealloc_step_wf; eauto.
  - eapply copy_step_wf; eauto.
  - eapply write_step_wf; eauto.
  - eapply deref_step_wf; eauto.
  - eapply newcall_step_wf; eauto.
  - eapply endcall_step_wf; eauto.
  - eapply retag_step_wf; eauto.
  - eapply syscall_step_wf; eauto.
  - eapply silent_step_wf; eauto.
Qed.

Lemma retag_clk_mono h α clk β l kind T h' α' clk' :
  retag h α clk β l kind T = Some (h', α', clk') →
  (clk ≤ clk')%nat.
Proof.
  eapply (retag_elim
    (* general goal P *)
    (λ h α clk _ _ _ _ ohac, ∀ h' α' clk',
        ohac = Some (h', α', clk') → (clk ≤ clk')%nat)
    (* invariant for Product's where P1 *)
    (λ _ _ _ _ _ _ _ h α clk _ _ ohac, ∀ h' α' clk',
        ohac = Some (h', α', clk') → (clk ≤ clk')%nat)
    (* invariant for Sum's where P3 *)
    (λ h _ _ α clk β _ _ _ _ ohac, ∀ h' α' clk',
        ohac = Some (h', α', clk') → (clk ≤ clk')%nat)).
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - (* Reference cases *)
    clear. intros h ?? bor α clk β rt_kind p_kind T Eq h' α' clk'.
    destruct p_kind as [mut| |];
      [|destruct rt_kind; try by (intros; simplify_eq)|];
      (case retag_ref as [[[bor' α1] clk1]|] eqn:Eq1; [simpl|done]);
      intros; simplify_eq; eapply retag_ref_clk_mono; eauto.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - (* Product inner recursive case *)
    intros ????????????? IH1 IH2 ???.
    case retag as [hac|]; [|done]. move => /= /IH1 Le. destruct hac as [[]].
    etrans; [|exact Le]. by eapply IH2.
  - naive_solver.
  - naive_solver.
  - (* Sum case *)
    intros ???????? IH Eq ???. case decide => Le; [|done]. by apply IH.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
Qed.

Lemma head_step_clk_mono σ σ' e e' obs efs :
  head_step e σ obs e' σ' efs → (σ.(cclk) ≤ σ'.(cclk))%nat.
Proof.
  intros HS. inversion HS. simplify_eq.
  inversion InstrStep; simplify_eq; simpl; try done; [lia|].
  by eapply retag_clk_mono.
Qed.

Definition future_barrier (β β': barriers) :=
  ∀ c b, β !! c = Some b → ∃ b', β' !! c = Some b' ∧ (b = false → b' = false).

Instance future_state_preorder: PreOrder future_barrier.
Proof.
  constructor.
  - intros ???. naive_solver.
  - move => ??? H1 H2 ?? /H1 [? [/H2 ?]]. naive_solver.
Qed.

Lemma head_step_barriers_mono σ σ' e e' obs efs :
  head_step e σ obs e' σ' efs → future_barrier σ.(cbar) σ'.(cbar).
Proof.
  intros HS. inversion HS. simplify_eq.
  inversion InstrStep; simplify_eq; simpl; try done.
  - intros c b Eq. exists b. split; [|done]. rewrite lookup_insert_ne; [done|].
    intros ?. subst c. apply (elem_of_dom_2 (D:= gset nat)) in Eq.
    move : Eq. apply is_fresh.
  - intros c' b Eq. case (decide (c' = call)) => ?; [subst c'|].
    + exists false. by rewrite lookup_insert.
    + exists b. by rewrite lookup_insert_ne.
Qed.
