From Equations Require Import Equations.
From stbor Require Export lang notation.

Class Wellformed A := Wf : A → Prop.
Existing Class Wf.

Definition wf_mem_bor (h: mem) (clock: time) :=
  ∀ l l' bor, h !! l = Some (LitV (LitLoc l' bor)) → bor <b clock.

Definition frozen_lt (stk: bstack) (clk: time) :=
  match frozen_since stk with
  | Some t => (t < clk)%nat
  | None => True
  end.
Definition wf_stack_frozen (α: bstacks) (clock: time) :=
  ∀ l stack, α !! l = Some stack → frozen_lt stack clock.

Definition stack_item_included (stk: bstack) (β: barriers) (clock: time) :=
  ∀ si, si ∈ stk.(borrows) → match si with
                              | Uniq t => (t < clock)%nat
                              | FnBarrier c => is_Some (β !! c)
                              | _ => True
                              end.
Definition wf_stack_item (α: bstacks) (β: barriers) (clock: time) :=
  ∀ l stack, α !! l = Some stack → stack_item_included stack β clock.

Record state_wf' σ := {
  state_wf_dom : dom (gset loc) σ.(cheap) ≡ dom (gset loc) σ.(cstk);
  state_wf_mem_bor: wf_mem_bor σ.(cheap) σ.(cclk);
  state_wf_stack_frozen: wf_stack_frozen σ.(cstk) σ.(cclk);
  state_wf_stack_item: wf_stack_item σ.(cstk) σ.(cbar) σ.(cclk);
  (* TODO: add stacks to be non-empty *)
}.

Instance state_wf : Wellformed state :=  state_wf'.

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

Lemma foldr_gmap_insert_dom `{Countable K} {A B C: Type}
  (ma: gmap K A) (mb: gmap K B) (a: A) (b: B) (cs: list C) (f: C → K):
  dom (gset K) ma ≡ dom (gset K) mb →
  dom (gset K) (foldr (λ (c: C) ma, <[f c := a]> ma) ma cs)
  ≡ dom (gset K) (foldr (λ (c: C) mb, <[f c := b]> mb) mb cs).
Proof.
  intros. induction cs; simpl; [done|].
  by rewrite 2!dom_insert IHcs.
Qed.

Lemma foldr_gmap_insert_lookup `{Countable K} {A C: Type}
  (ma: gmap K A) (a ka: A) (cs: list C) (f: C → K) (k: K):
  (foldr (λ (c: C) ma, <[f c := a]> ma) ma cs) !! k = Some ka →
  ka = a ∨ ma !! k = Some ka.
Proof.
  induction cs as [|a' ? IHm]; simpl; [naive_solver|].
  case (decide (f a' = k)) => [->|?].
  - rewrite lookup_insert. naive_solver.
  - by rewrite lookup_insert_ne.
Qed.

Lemma foldr_gmap_insert_lookup_neq `{Countable K} {A C: Type}
  (ma: gmap K A) (a ka: A) (cs: list C) (f: C → K) (k: K) (NEq: ka ≠ a):
  (foldr (λ (c: C) ma, <[f c := a]> ma) ma cs) !! k = Some ka →
  ma !! k = Some ka.
Proof.
  intros Eq. by destruct (foldr_gmap_insert_lookup _ _ _ _ _ _ Eq).
Qed.

(** Alloc *)
Lemma alloc_step_wf σ σ' e e' obs efs h0 l bor T:
  base_step e σ.(cheap) (Some $ AllocEvt l bor T) obs e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ AllocEvt l bor T)
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
Qed.

Lemma foldr_gmap_delete_lookup `{Countable K} {A C: Type}
  (ma: gmap K A) (ka: A) (cs: list C) (f: C → K) (k: K):
  (foldr (λ (c: C) ma, delete (f c) ma) ma cs) !! k = Some ka →
  ma !! k = Some ka.
Proof.
  induction cs as [|a' ? IHm]; simpl; [naive_solver|].
  case (decide (f a' = k)) => [->|?].
  - by rewrite lookup_delete.
  - by rewrite lookup_delete_ne.
Qed.

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

Lemma foldr_gmap_delete_dom `{Countable K} {A B C: Type}
  (ma: gmap K A) (mb: gmap K B) (cs: list C) (f: C → K):
  dom (gset K) ma ≡ dom (gset K) mb →
  dom (gset K) (foldr (λ (c: C) ma, delete (f c) ma) ma cs)
  ≡ dom (gset K) (foldr (λ (c: C) mb, delete (f c) mb) mb cs).
Proof.
  intros. induction cs; simpl; [done|].
  by rewrite 2!dom_delete IHcs.
Qed.

(** Dealloc *)
Lemma dealloc_step_wf σ σ' e e' obs efs h0 l bor T :
  base_step e σ.(cheap) (Some $ DeallocEvt l bor T) obs e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ DeallocEvt l bor T)
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
Qed.

(** Copy *)

Lemma dom_map_insert_is_Some `{FinMapDom K M D} {A} (m : M A) i x :
  is_Some (m !! i) → dom D (<[i:=x]>m) ≡ dom D m.
Proof.
  intros IS. rewrite dom_insert. apply (anti_symm (⊆)).
  - apply union_least; [|done]. by apply elem_of_subseteq_singleton, elem_of_dom.
  - by apply union_subseteq_r.
Qed.

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

(** SqSubsetEq for option *)
Instance option_sqsubseteq `{SqSubsetEq A} : SqSubsetEq (option A) :=
  λ o1 o2, if o1 is Some x1 return _ then
              if o2 is Some x2 return _ then x1 ⊑ x2 else False
           else True.
Instance option_sqsubseteq_preorder `{SqSubsetEq A} `{!@PreOrder A (⊑)} :
  @PreOrder (option A) (⊑).
Proof.
  split.
  - move=>[x|] //. apply (@reflexivity A (⊑) _).
  - move=>[x|] [y|] [z|] //. apply (@transitivity A (⊑) _).
Qed.
Instance option_sqsubseteq_po `{SqSubsetEq A} `{!@PartialOrder A (⊑)} :
  @PartialOrder (option A) (⊑).
Proof.
  split; [apply _|].
  move => [?|] [?|] ??; [|done|done|done]. f_equal. by apply : anti_symm.
Qed.

Instance nat_sqsubseteq : SqSubsetEq nat := le.
Instance nat_sqsubseteq_po : @PartialOrder nat (⊑) := _.

Lemma access1'_item_stack stk bor kind β stk' :
  access1' stk bor kind β = Some stk' → stk' `suffix_of` stk.
Proof.
  revert bor. induction stk as [|si stk IH]; intros bor; simpl; [done|].
  destruct si; [destruct bor..|].
  - case_match => [|/IH]; [|by apply suffix_cons_r].
    case_match => [[<-//]|//].
  - move => /IH. by apply suffix_cons_r.
  - destruct kind; [by move => [<-]|..]; move => /IH; by apply suffix_cons_r.
  - destruct kind; [by move => [<-]|..]; case_match => [[->//]|//].
  - case_match => [//|/IH]. by apply suffix_cons_r.
Qed.

Lemma access1_stack β stk stk' bor kind :
  access1 β stk bor kind = Some stk' →
  suffix stk'.(borrows) stk.(borrows) ∧ stk'.(frozen_since) ⊑ stk.(frozen_since).
Proof.
  rewrite /access1.
  case (frozen_since _) as [t|] eqn:Eqt; rewrite -Eqt;
    [destruct kind|]; [by move => [<-]|..];
    (case access1' as [stk0|] eqn:Eq; [|done]); move => [<-] /=; (split; [|done]);
    by eapply access1'_item_stack.
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

Lemma accessN_stack α β l bor n kind α' (ND: kind ≠ AccessDealloc) :
  accessN α β l bor n kind = Some α' →
  ∀ (l: loc) stk', α' !! l = Some stk' → ∃ stk, α !! l = Some stk ∧
    stk'.(borrows) `suffix_of` stk.(borrows) ∧ stk'.(frozen_since) ⊑ stk.(frozen_since).
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
    by eapply access1_stack.
  - move => /(IH _ Eq2) [stk [Eq' SUFF]]. exists stk. split; [|done].
    move : Eq'. by rewrite lookup_insert_ne.
Qed.

Instance elem_of_list_suffix_proper {A : Type} (x:A) :
  Proper ((suffix) ==> impl) (x ∈).
Proof. intros l1 l2 [? ->] ?. rewrite elem_of_app. by right. Qed.

Lemma copy_step_wf σ σ' e e' obs efs h0 l bor T vl :
  base_step e σ.(cheap) (Some $ CopyEvt l bor T vl) obs e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ CopyEvt l bor T vl)
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
    destruct Eq as [stk [Eq [_ Sub2]]]; [done..|].
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
Qed.

(** Write *)
Lemma write_mem_dom l vl h
  (DEFINED: ∀ i : nat, (i < strings.length vl)%nat → is_Some (h !! (l +ₗ i))) :
  dom (gset loc) (write_mem l vl h) ≡ dom (gset loc) h.
Proof.
  revert l h DEFINED. induction vl as [|v vl IH]; intros l h DEFINED; [done|].
  rewrite /= IH.
  - apply dom_map_insert_is_Some. rewrite -(shift_loc_0_nat l).
    apply DEFINED. simpl. lia.
  - intros i Lt. rewrite lookup_insert_is_Some'. right.
    rewrite (shift_loc_assoc_nat l 1). apply DEFINED. simpl. lia.
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

Lemma write_step_wf σ σ' e e' obs efs h0 l bor T vl :
  base_step e σ.(cheap) (Some $ WriteEvt l bor T vl) obs e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ WriteEvt l bor T vl)
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
    destruct Eq as [stk [Eq [_ Sub2]]]; [done..|].
    move : (state_wf_stack_frozen _ WF _ _ Eq).
    rewrite /frozen_lt. destruct stk'.(frozen_since) as [t'|]; [|done].
    destruct stk.(frozen_since) as [t|]; [|done]. intros.
    eapply le_lt_trans; [by apply Sub2|done].
  - intros l' stk'.
    move => /(accessN_stack α β' l bor (tsize T) AccessWrite α' _ _ l' stk') Eq.
    destruct Eq as [stk [Eq [Sub1 _]]]; [done..|].
    intros si Ini. apply (state_wf_stack_item _ WF _ _ Eq).
    move : Ini. by apply elem_of_list_suffix_proper.
Qed.

(** Deref *)
Lemma deref_step_wf σ σ' e e' obs efs h0 l bor T mut :
  base_step e σ.(cheap) (Some $ DerefEvt l bor T mut) obs e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ DerefEvt l bor T mut)
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
Lemma newcall_step_wf σ σ' e e' obs efs h0 n :
  base_step e σ.(cheap) (Some $ NewCallEvt n) obs e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ NewCallEvt n)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α β clk]. destruct σ' as [h' α' β' clk']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl; [apply WF..|].
  intros ?? Eq ? In. have SI := state_wf_stack_item _ WF _ _ Eq _ In.
  destruct si; [done..|]. rewrite lookup_insert_is_Some'. by right.
Qed.

(** EndCall *)
Lemma endcall_step_wf σ σ' e e' obs efs h0 n :
  base_step e σ.(cheap) (Some $ EndCallEvt n) obs e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ EndCallEvt n)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α β clk]. destruct σ' as [h' α' β' clk']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl; [apply WF..|].
  intros ?? Eq ? In. have SI := state_wf_stack_item _ WF _ _ Eq _ In.
  destruct si; [done..|]. rewrite lookup_insert_is_Some'. by right.
Qed.

(** Retag *)

(* Retag dom *)
Lemma reborrowN_dom α β l n bor bor' kind' bar α' :
  reborrowN α β l n bor bor' kind' bar = Some α' →
  dom (gset loc) α ≡ dom (gset loc) α'.
Proof.
  revert α. induction n as [|n IH]; simpl; intros α; [by intros; simplify_eq|].
  case lookup as [stk|] eqn:Eq; [simpl|done].
  case reborrow1 as [stk'|] eqn:Eq'; [simpl|done].
  move => /IH <-. symmetry. apply dom_map_insert_is_Some. by eexists.
Qed.

Lemma reborrowBlock_dom α β l n bor bor' kind' bar α':
  reborrowBlock α β l n bor bor' kind' bar = Some α' →
  dom (gset loc) α ≡ dom (gset loc) α'.
Proof. rewrite /reborrowBlock. case_match; [done|by apply reborrowN_dom]. Qed.

Lemma unsafe_action_dom (f: bstacks → _ → _ → _ → _) α l last fs us α' lc' :
  (∀ α1 α2 l n b, f α1 l n b = Some α2 → dom (gset loc) α1 ≡ dom (gset loc) α2) →
  unsafe_action f α l last fs us = Some (α', lc') →
  dom (gset loc) α ≡ dom (gset loc) α'.
Proof.
  intros Hf. rewrite /unsafe_action.
  case f as [α1|] eqn:Eq1; [simpl|done]. case (f α1) eqn:Eq2; [simpl|done].
  intros. simplify_eq. by rewrite (Hf _ _ _ _ _ Eq1) (Hf _ _ _ _ _ Eq2).
Qed.

Lemma visit_freeze_sensitive'_stack_dom h l (f: bstacks → _ → _ → _ → _)
  α α' last cur T lc' :
  (∀ α1 α2 l n b, f α1 l n b = Some α2 → dom (gset loc) α1 ≡ dom (gset loc) α2) →
  visit_freeze_sensitive' h l f α last cur T = Some (α', lc') →
  dom (gset loc) α ≡ dom (gset loc) α'.
Proof.
  eapply (visit_freeze_sensitive'_elim
            (* general goal P *)
            (λ _ _ f α _ _ _ oalc, ∀ α' lc',
              (∀ α1 α2 l n b, f α1 l n b = Some α2 → dom (gset loc) α1 ≡ dom (gset loc) α2) →
                oalc = Some (α', lc') → dom (gset loc) α ≡ dom (gset loc) α')
            (λ _ _ f _ _ _ _ α _ _ _ oalc, ∀ α' lc',
              (∀ α1 α2 l n b, f α1 l n b = Some α2 → dom (gset loc) α1 ≡ dom (gset loc) α2) →
                oalc = Some (α', lc') → dom (gset loc) α ≡ dom (gset loc) α')
            (λ _ _ _ f α _ _ _ _ _ oalc, ∀ α' lc',
              (∀ α1 α2 l n b, f α1 l n b = Some α2 → dom (gset loc) α1 ≡ dom (gset loc) α2) →
                oalc = Some (α', lc') → dom (gset loc) α ≡ dom (gset loc) α')).
  - naive_solver.
  - naive_solver.
  - (* Unsafe case *)
    naive_solver eauto using unsafe_action_dom.
  - (* Union case *)
    intros ??????????. case is_freeze; [by intros; simplify_eq|].
    by apply unsafe_action_dom.
  - naive_solver.
  - naive_solver.
  - (* Product case *)
    intros ???????????? IH1 IH2 ???.
    case visit_freeze_sensitive' as [alc|]; [simpl|done].
    move => /IH1 <-; [|done]. destruct alc. by eapply IH2.
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

Lemma visit_freeze_sensitive_stack_dom h l T (f: bstacks → _ → _ → _ → _) α α' :
  (∀ α1 α2 l n b, f α1 l n b = Some α2 → dom (gset loc) α1 ≡ dom (gset loc) α2) →
  visit_freeze_sensitive h l T f α = Some α' →
  dom (gset loc) α ≡ dom (gset loc) α'.
Proof.
  intros Hf. rewrite /visit_freeze_sensitive.
  case visit_freeze_sensitive' as [[α1 [last cur]]|] eqn:Eq; [|done].
  move => /Hf <-. move : Eq. by apply visit_freeze_sensitive'_stack_dom.
Qed.

Lemma reborrow_dom h α β l bor T bar bor' α' :
  reborrow h α β l bor T bar bor' = Some α' →
  dom (gset loc) α ≡ dom (gset loc) α'.
Proof.
  rewrite /reborrow. destruct bor' as [t|[t|]].
  - by move => /reborrowBlock_dom ->.
  - apply visit_freeze_sensitive_stack_dom.
    intros ?????. by apply reborrowBlock_dom.
  - by move => /reborrowBlock_dom ->.
Qed.

Lemma retag_ref_dom h α β clk l bor T mut bar kind bor' α' clk' :
  retag_ref h α β clk l bor T mut bar kind = Some (bor', α', clk') →
  dom (gset loc) α ≡ dom (gset loc) α'.
Proof.
  rewrite /retag_ref. case tsize eqn:Eq; [by intros; simplify_eq|].
  case reborrow as [α1|] eqn:Eq1; [simpl|done].
  destruct kind.
  - destruct mut as [[]|]; [|done..].
    case visit_freeze_sensitive as [α2|] eqn:Eq2; [|done]. move => /= ?.
    simplify_eq. move : Eq1 => /reborrow_dom ->.
    move : Eq2. apply visit_freeze_sensitive_stack_dom.
    intros ?????. by apply reborrowBlock_dom.
  - intros. simplify_eq. by move : Eq1 => /reborrow_dom ->.
Qed.

Lemma retag_dom h α clk β x kind T h' α' clk' :
  retag h α clk β x kind T = Some (h', α', clk') →
  dom (gset loc) h ≡ dom (gset loc) h' ∧ dom (gset loc) α ≡ dom (gset loc) α'.
Proof.
  eapply (retag_elim
            (* general goal P *)
            (λ h α clk β l kind T r, ∀ h' α' clk', r = Some (h', α', clk') →
                dom (gset loc) h ≡ dom (gset loc) h' ∧
                dom (gset loc) α ≡ dom (gset loc) α')
            (* invariant for Product's where P1 *)
            (λ _ _ _ _ _ _ _ h α _ _ _ ohac, ∀ h' α' clk',
                ohac = Some (h', α', clk') →
                dom (gset loc) h ≡ dom (gset loc) h' ∧
                dom (gset loc) α ≡ dom (gset loc) α')
            (* invariant for Sum's where P3 *)
            (λ h _ _ α _ _ _ _ _ _ ohac, ∀ h' α' clk',
                ohac = Some (h', α', clk') →
                dom (gset loc) h ≡ dom (gset loc) h' ∧
                dom (gset loc) α ≡ dom (gset loc) α')).
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - (* Reference cases *)
    clear. move => h x l tag α clk β rt_kind [mut| |] T Eq h' α' clk' /=;
      [|destruct rt_kind; try by (intros; simplify_eq)|];
      (case retag_ref as [[[bor' α1] clk1]|] eqn:Eq1; [simpl|done]);
      intros; simplify_eq;
      (split; [symmetry; apply dom_map_insert_is_Some; by eexists
              |by eapply retag_ref_dom]).
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - (* Product inner recursive case *)
    intros ????????????? IH1 IH2 ???.
    case retag eqn:Eq1; [|done]. move => /= Eq.
    destruct (IH1 _ _ _ _ Eq) as [Dh Da]. rewrite -Dh -Da.
    destruct p as [[??]?]. by eapply IH2.
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

Lemma retag_ref_wf_mem_bor h α β clk x l bor T mut kind is_2p bor' α' clk'
  (Eq: h !! x = Some $ LitV (LitLoc l bor)) :
  retag_ref h α β clk l bor T mut kind is_2p = Some (bor', α', clk') →
  wf_mem_bor h clk → wf_mem_bor (<[x:=LitV (LitLoc l bor')]> h) clk'.
Proof.
  intros Eqr WF x' l' bor1. case (decide (x' = x)) => Eqx; [subst x'|].
  - rewrite lookup_insert => ?. simplify_eq.
    by eapply retag_ref_clk_bor_mono; eauto.
  - rewrite lookup_insert_ne; [|done].
    move => /WF. apply bor_value_included_trans. by eapply retag_ref_clk_mono.
Qed.

Lemma retag_wf_mem_bor h α clk β l kind T h' α' clk':
  retag h α clk β l kind T = Some (h', α', clk') →
  wf_mem_bor h clk → wf_mem_bor h' clk'.
Proof.
  eapply (retag_elim
            (* general goal P *)
            (λ h α clk β l kind T r, ∀ h' α' clk', r = Some (h', α', clk') →
                wf_mem_bor h clk → wf_mem_bor h' clk')
            (* invariant for Product's where P1 *)
            (λ _ _ _ _ _ _ _ h α clk _ _ ohac, ∀ h' α' clk',
                ohac = Some (h', α', clk') →
                wf_mem_bor h clk → wf_mem_bor h' clk')
            (* invariant for Sum's where P3 *)
            (λ h _ _ α clk _ _ _ _ _ ohac, ∀ h' α' clk',
                ohac = Some (h', α', clk') →
                wf_mem_bor h clk → wf_mem_bor h' clk')).
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
      intros ?; simplify_eq; by eapply retag_ref_wf_mem_bor; eauto.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - (* Product inner recursive case *)
    intros ????????????? IH1 IH2 ???.
    case retag as [hac|]; [|done]. move => /= /IH1 WF ?. apply WF.
    destruct hac as [[]]. by eapply IH2.
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
  (stack_item_included stk β clk → stack_item_included stk' β clk).
Proof.
  rewrite /access1. case frozen_since.
  - case kind; [by intros; simplify_eq|..];
      (case access1' eqn:Eq; [simpl; intros; simplify_eq|done]);
      (split; [done|]);
      by eapply suffix_stack_item_included, access1'_item_stack.
  - case access1' eqn:Eq; [simpl; intros; simplify_eq|done].
    split; [done|]. by eapply suffix_stack_item_included, access1'_item_stack.
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
  bor' <b clk → reborrow1 stk bor bor' kind β bar = Some stk' →
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

Lemma reborrowBlock_wf_stack_frozen α β clk l n bor bor' kind bar α'
  (INCL: bor' <b clk) :
  reborrowBlock α β l n bor bor' kind bar = Some α' →
  wf_stack_frozen α clk → wf_stack_frozen α' clk.
Proof.
  rewrite /reborrowBlock. case_match; [done|].
  clear -INCL. revert α.
  induction n as [|n IH]; intros α; simpl.
  { intros ?; simplify_eq. apply wf_stack_frozen_mono. by lia. }
  case lookup as [stk|] eqn:Eqs; [simpl|done].
  case reborrow1 as [stk'|] eqn:Eq1; [simpl|done].
  intros Eq2 WF. apply (IH _ Eq2).
  intros l' stk0. case (decide (l' = l +ₗ n)) => ?; [subst l'|].
  - rewrite lookup_insert. intros ?. simplify_eq.
    by eapply reborrow1_wf_stack_frozen; eauto.
  - rewrite lookup_insert_ne; [|done]. by apply WF.
Qed.

Lemma unsafe_action_wf_stack_frozen
  (f: bstacks → _ → _ → _ → _) α l last fs us α' lc' clk :
  (∀ α1 α2 l n b, f α1 l n b = Some α2 →
    wf_stack_frozen α1 clk → wf_stack_frozen α2 clk) →
  unsafe_action f α l last fs us = Some (α', lc') →
  wf_stack_frozen α clk → wf_stack_frozen α' clk.
Proof.
  intros Hf. rewrite /unsafe_action.
  case f as [α1|] eqn:Eq1; [simpl|done]. case (f α1) eqn:Eq2; [simpl|done].
  naive_solver.
Qed.

Lemma visit_freeze_sensitive'_wf_stack_frozen h l (f: bstacks → _ → _ → _ → _)
  α α' last cur T lc' clk :
  (∀ α1 α2 l n b, f α1 l n b = Some α2 →
    wf_stack_frozen α1 clk → wf_stack_frozen α2 clk) →
  visit_freeze_sensitive' h l f α last cur T = Some (α', lc') →
  wf_stack_frozen α clk → wf_stack_frozen α' clk.
Proof.
  eapply (visit_freeze_sensitive'_elim
            (* general goal P *)
            (λ _ _ f α _ _ _ oalc, ∀ α' lc',
              (∀ α1 α2 l n b, f α1 l n b = Some α2 →
                wf_stack_frozen α1 clk → wf_stack_frozen α2 clk) →
              oalc = Some (α', lc') →
              wf_stack_frozen α clk → wf_stack_frozen α' clk)
            (λ _ _ f _ _ _ _ α _ _ _ oalc, ∀ α' lc',
              (∀ α1 α2 l n b, f α1 l n b = Some α2 →
                wf_stack_frozen α1 clk → wf_stack_frozen α2 clk) →
              oalc = Some (α', lc') →
              wf_stack_frozen α clk → wf_stack_frozen α' clk)
            (λ _ _ _ f α _ _ _ _ _ oalc, ∀ α' lc',
              (∀ α1 α2 l n b, f α1 l n b = Some α2 →
                wf_stack_frozen α1 clk → wf_stack_frozen α2 clk) →
              oalc = Some (α', lc') →
              wf_stack_frozen α clk → wf_stack_frozen α' clk)).
  - naive_solver.
  - naive_solver.
  - (* Unsafe case *)
    naive_solver eauto using unsafe_action_wf_stack_frozen.
  - (* Union case *)
    intros ??????????. case is_freeze; [by intros; simplify_eq|].
    by apply unsafe_action_wf_stack_frozen.
  - naive_solver.
  - naive_solver.
  - (* Product case *)
    intros ???????????? IH1 IH2 ???.
    case visit_freeze_sensitive' as [alc|]; [simpl|done].
    move => /IH1 IH1' WF. apply IH1'; [done|]. move : WF.
    destruct alc. by eapply IH2.
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

Lemma visit_freeze_sensitive_wf_stack_frozen h l T (f: bstacks → _ → _ → _ → _)
  clk α α' :
  (∀ α1 α2 l n b, f α1 l n b = Some α2 →
    wf_stack_frozen α1 clk → wf_stack_frozen α2 clk) →
  visit_freeze_sensitive h l T f α = Some α' →
  wf_stack_frozen α clk → wf_stack_frozen α' clk.
Proof.
  intros Hf. rewrite /visit_freeze_sensitive.
  case visit_freeze_sensitive' as [[α1 [last cur]]|] eqn:Eq; [|done].
  move => Eqf WF. eapply Hf; eauto.
  by eapply visit_freeze_sensitive'_wf_stack_frozen; eauto.
Qed.

Lemma reborrow_wf_stack_frozen h α β clk l bor T kind bor' α'
  (INCL: bor' <b clk) :
  reborrow h α β l bor T kind bor' = Some α' →
  wf_stack_frozen α clk → wf_stack_frozen α' clk.
Proof.
  rewrite /reborrow. destruct bor' as [|[]].
  - by eapply reborrowBlock_wf_stack_frozen; eauto.
  - apply visit_freeze_sensitive_wf_stack_frozen.
    intros ?????. by apply reborrowBlock_wf_stack_frozen.
  - by eapply reborrowBlock_wf_stack_frozen; eauto.
Qed.

Lemma retag_ref_wf_stack_frozen h α β clk l bor T mut kind is_2p bor' α' clk' :
  retag_ref h α β clk l bor T mut kind is_2p = Some (bor', α', clk') →
  wf_stack_frozen α clk → wf_stack_frozen α' clk'.
Proof.
  rewrite /retag_ref. case tsize eqn:Eq; [by intros; simplify_eq|].
  case reborrow as [α1|] eqn:Eq1; [simpl|done].
  destruct is_2p; [destruct mut as [[]|]|]; [|done..|].
  - case visit_freeze_sensitive as [α2|] eqn:Eq2; [simpl|done].
    intros ?. simplify_eq. intros WF.
    eapply visit_freeze_sensitive_wf_stack_frozen; [|exact Eq2|].
    + move => ????? /=. apply reborrowBlock_wf_stack_frozen. simpl. by lia.
    + eapply reborrowBlock_wf_stack_frozen; eauto; [by simpl; lia|].
      eapply wf_stack_frozen_mono; [|exact WF]. by lia.
  - intros ?. simplify_eq. intros WF.
    have WF': wf_stack_frozen α (S clk).
    { eapply wf_stack_frozen_mono; [|exact WF]. by lia. }
    eapply reborrow_wf_stack_frozen; eauto.
    by destruct mut as [[]|]; simpl; [lia..|done].
Qed.

Lemma retag_wf_stack_frozen h α clk β l kind T h' α' clk':
  retag h α clk β l kind T = Some (h', α', clk') →
  wf_stack_frozen α clk → wf_stack_frozen α' clk'.
Proof.
  eapply (retag_elim
            (* general goal P *)
            (λ h α clk β l kind T r, ∀ h' α' clk', r = Some (h', α', clk') →
                wf_stack_frozen α clk → wf_stack_frozen α' clk')
            (* invariant for Product's where P1 *)
            (λ _ _ _ _ _ _ _ h α clk _ _ ohac, ∀ h' α' clk',
                ohac = Some (h', α', clk') →
                wf_stack_frozen α clk → wf_stack_frozen α' clk')
            (* invariant for Sum's where P3 *)
            (λ h _ _ α clk _ _ _ _ _ ohac, ∀ h' α' clk',
                ohac = Some (h', α', clk') →
                wf_stack_frozen α clk → wf_stack_frozen α' clk')).
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
      intros ?; simplify_eq ; by eapply retag_ref_wf_stack_frozen; eauto.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - (* Product inner recursive case *)
    intros ????????????? IH1 IH2 ???.
    case retag as [hac|]; [|done]. move => /= /IH1 WF ?. apply WF.
    destruct hac as [[]]. by eapply IH2.
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

(* Retag stack item *)

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

Lemma access1'_non_nil stk bor kind β stk' :
  access1' stk bor kind β = Some stk' → stk ≠ [] → stk' ≠ [].
Proof.
  intros Eq ?. induction stk as [|[] stk]; [done|..];
    move : Eq; simpl; [destruct bor..|].
  - case decide => ?; simpl; [case_match|]; [by intros; simplify_eq|done|].
    admit.
  - admit.
  - case kind; [by intros; simplify_eq|..].
    admit. admit.
  - case kind; [by intros; simplify_eq|..];
      (case_match; [by intros; simplify_eq|done]).
Admitted.

Lemma access1_non_nil β stk bor kind stk' :
  access1 β stk bor kind = Some stk' → stk.(borrows) ≠ [] → stk'.(borrows) ≠ [].
Proof.
  rewrite /access1.
  case frozen_since as [?|]; [destruct kind|]; [intros; by simplify_eq|..];
    (case access1' eqn:Eq; [simpl|done]); intros; simplify_eq;
    by eapply access1'_non_nil.
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
    apply add_barrier_stack_item_included; eauto.
    + by eapply access1_non_nil.
    + by eapply access1_wf_stack.
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

Lemma reborrowBlock_wf_stack_item α β clk l n bor bor' kind bar α'
  (INCL: bor' <b clk)
  (BAR : match bar with Some c => is_Some (β !! c) | _ => True end) :
  reborrowBlock α β l n bor bor' kind bar = Some α' →
  wf_stack_item α β clk → wf_stack_item α' β clk.
Proof.
  rewrite /reborrowBlock. case xorb; [done|].
  clear -INCL. revert α.
  induction n as [|n IH]; intros α; simpl.
  { intros ?; simplify_eq. apply wf_stack_item_mono. by lia. }
  case lookup as [stk|] eqn:Eqs; [simpl|done].
  case reborrow1 as [stk'|] eqn:Eq1; [simpl|done].
  intros Eq2 WF. apply (IH _ Eq2).
  intros l' stk0. case (decide (l' = l +ₗ n)) => ?; [subst l'|].
  - rewrite lookup_insert. intros ?. simplify_eq.
     eapply reborrow1_wf_stack_item; eauto. admit. admit.
  - rewrite lookup_insert_ne; [|done]. by apply WF.
Admitted.

Lemma reborrow_wf_stack_item h α β clk l bor T kind bor' α'
  (INCL: bor' <b clk) :
  reborrow h α β l bor T kind bor' = Some α' →
  wf_stack_item α β clk → wf_stack_item α' β clk.
Proof.
  rewrite /reborrow. destruct bor' as [|[]].
  - by eapply reborrowBlock_wf_stack_item; eauto.
  - (* apply visit_freeze_sensitive_wf_stack_frozen.
    intros ?????. by apply reborrowBlock_wf_stack_frozen. *)
    admit.
  - by eapply reborrowBlock_wf_stack_item; eauto.
Admitted.

Lemma retag_ref_wf_stack_item h α β clk l bor T mut kind is_2p bor' α' clk' :
  retag_ref h α β clk l bor T mut kind is_2p = Some (bor', α', clk') →
  wf_stack_item α β clk → wf_stack_item α' β clk'.
Proof.
  rewrite /retag_ref. case tsize eqn:Eq; [by intros; simplify_eq|].
  case reborrow as [α1|] eqn:Eq1; [simpl|done].
  destruct is_2p; [destruct mut as [[]|]|]; [|done..|].
  - case visit_freeze_sensitive as [α2|] eqn:Eq2; [simpl|done].
    intros ?. simplify_eq.
    admit.
  - intros ?. simplify_eq. intros WF.
    have WF': wf_stack_item α β (S clk).
    { eapply wf_stack_item_mono; [|exact WF]. by lia. }
    eapply reborrow_wf_stack_item; eauto.
    by destruct mut as [[]|]; simpl; [lia..|done].
Admitted.

Lemma retag_wf_stack_item h α clk β l kind T h' α' clk':
  retag h α clk β l kind T = Some (h', α', clk') →
  wf_stack_item α β clk → wf_stack_item α' β clk'.
Proof.
  eapply (retag_elim
            (* general goal P *)
            (λ h α clk β l kind T r, ∀ h' α' clk', r = Some (h', α', clk') →
                wf_stack_item α β clk → wf_stack_item α' β clk')
            (* invariant for Product's where P1 *)
            (λ _ _ _ β _ _ _ h α clk _ _ ohac, ∀ h' α' clk',
                ohac = Some (h', α', clk') →
                wf_stack_item α β clk → wf_stack_item α' β clk')
            (* invariant for Sum's where P3 *)
            (λ h _ _ α clk β _ _ _ _ ohac, ∀ h' α' clk',
                ohac = Some (h', α', clk') →
                wf_stack_item α β clk → wf_stack_item α' β clk')).
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
      intros ?; simplify_eq; by eapply retag_ref_wf_stack_item; eauto.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - (* Product inner recursive case *)
    intros ????????????? IH1 IH2 ???.
    case retag as [hac|]; [|done]. move => /= /IH1 WF ?. apply WF.
    destruct hac as [[]]. by eapply IH2.
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

Lemma retag_step_wf σ σ' e e' obs efs h0 l T kind :
  base_step e σ.(cheap) (Some $ RetagEvt l T kind) obs e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ RetagEvt l T kind) 
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h α β clk]. destruct σ' as [h' α' β' clk']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl.
  - move : RETAG => /retag_dom [<- <-]. by apply WF.
  - eapply retag_wf_mem_bor; eauto. by apply WF.
  - eapply retag_wf_stack_frozen; eauto. by apply WF.
  - eapply retag_wf_stack_item; eauto. by apply WF.
Qed.

(** None event step *)
Lemma None_step_wf σ σ' e e' obs efs h0 :
  base_step e σ.(cheap) None obs e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    None
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
  intros HS WF. inversion HS. simplify_eq. destruct oevent as [[]|].
  - eapply alloc_step_wf; eauto.
  - eapply dealloc_step_wf; eauto.
  - eapply copy_step_wf; eauto.
  - eapply write_step_wf; eauto.
  - eapply deref_step_wf; eauto.
  - eapply newcall_step_wf; eauto.
  - eapply endcall_step_wf; eauto.
  - eapply retag_step_wf; eauto.
  - eapply None_step_wf; eauto.
Qed.
