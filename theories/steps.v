From stbor Require Import lang notation.

Class Wellformed A := Wf : A → Prop.
Existing Class Wf.

Definition wf_stack_item (stack: bstack) (clock: time) (β: barriers)
  : Prop := ∀ si, si ∈ stack.(borrows) →  match si with
                                          | Uniq t => (t < clock)%nat
                                          | FnBarrier c => is_Some (β !! c)
                                          | _ => True
                                          end.

Definition wf_bor_value (bor: borrow) (clock: time) : Prop :=
  match bor with
  | UniqB t | AliasB (Some t) => (t < clock)%nat
  | _ => True
  end.
Definition wf_bor_values (vl: list immediate) σ :=
  ∀ l bor, (LitV (LitLoc l bor)) ∈ vl → wf_bor_value bor σ.(cclk).

Record state_wf' σ := {
  state_wf_dom : dom (gset loc) σ.(cheap) ≡ dom (gset loc) σ.(cstk);
  state_wf_mem_bor:
    ∀ l l' bor, σ.(cheap) !! l = Some (LitV (LitLoc l' bor)) → wf_bor_value bor σ.(cclk);
  state_wf_stack_frozen:
    ∀ l stack, σ.(cstk) !! l = Some stack →
      match stack.(frozen_since) with Some t => (t < σ.(cclk))%nat | _ => True end;
  state_wf_stack_item:
    ∀ l stack, σ.(cstk) !! l = Some stack → wf_stack_item stack σ.(cclk) σ.(cbar)
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
      destruct (stack.(frozen_since)); simpl; lia.
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
      destruct stack.(frozen_since); simpl; lia.
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
  Wf σ → Wf σ' ∧ wf_bor_values vl σ'.
Proof.
  destruct σ as [h α β clk]. destruct σ' as [h' α' β' clk']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq. split.
  - constructor; simpl.
    + rewrite -(accessN_dom α _ l bor (tsize T) AccessRead); [by apply WF|done..].
    + apply WF.
    + intros l' stk'.
      move=> /(accessN_stack α β' l bor (tsize T) AccessRead α' _ _ l' stk') Eq.
      destruct Eq as [stk [Eq [_ Sub2]]]; [done..|].
      destruct stk'.(frozen_since) as [t'|]; [|done].
      have Eq2 := (state_wf_stack_frozen _ WF _ _ Eq).
      destruct stk.(frozen_since) as [t|]; [|done].
      eapply le_lt_trans; [by apply Sub2|done].
    + intros l' stk'.
      move=> /(accessN_stack α β' l bor (tsize T) AccessRead α' _ _ l' stk') Eq.
      destruct Eq as [stk [Eq [Sub1 _]]]; [done..|].
      intros si Ini. apply (state_wf_stack_item _ WF _ _ Eq).
      move : Ini. by apply elem_of_list_suffix_proper.
  - intros l' bor' [i Eqi]%elem_of_list_lookup.
    have Eqbor: h' !! (l +ₗ i) = Some (LitV (LitLoc l' bor')).
    { rewrite -Eqi. by eapply VALUES, lookup_lt_Some. }
    by apply (state_wf_mem_bor _ WF _ _ _ Eqbor).
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
  revert l h. induction vl as [|v vl IH]; move => l h; simpl; split;
    [intros ?; by lia|done|..].
  - intros i Lt. admit.
  - intros l' Lt. destruct (IH (l +ₗ 1) (<[l:=v]> h)) as [IH1 IH2].
    rewrite IH2.
    + admit.
    + admit.
Abort.

Lemma write_step_wf σ σ' e e' obs efs h0 l bor T vl :
  base_step e σ.(cheap) (Some $ WriteEvt l bor T vl) obs e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ WriteEvt l bor T vl)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → wf_bor_values vl σ → Wf σ'.
Proof.
  destruct σ as [h α β clk]. destruct σ' as [h' α' β' clk']. simpl.
  intros BS IS WF WFvl.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl.
  - rewrite -(accessN_dom α β' l bor (tsize T) AccessWrite); [|done..].
    rewrite write_mem_dom; [by apply WF|done].
  - admit. (* only true if whatever in el is bound in the memory *)
  - intros l' stk'.
    move => /(accessN_stack α β' l bor (tsize T) AccessWrite α' _ _ l' stk') Eq.
    destruct Eq as [stk [Eq [_ Sub2]]]; [done..|].
    destruct stk'.(frozen_since) as [t'|]; [|done].
    have Eq2 := (state_wf_stack_frozen _ WF _ _ Eq).
    destruct stk.(frozen_since) as [t|]; [|done].
    eapply le_lt_trans; [by apply Sub2|done].
  - intros l' stk'.
    move => /(accessN_stack α β' l bor (tsize T) AccessWrite α' _ _ l' stk') Eq.
    destruct Eq as [stk [Eq [Sub1 _]]]; [done..|].
    intros si Ini. apply (state_wf_stack_item _ WF _ _ Eq).
    move : Ini. by apply elem_of_list_suffix_proper.
Abort.

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
  - admit. (* no change in dom of h' stk' *)
  - admit. (* new bor comes from increasing clk *)
  - admit. (* new frozen comes from increasing clk *)
  - admit. (* new bor comes from increasing clk, barrier must be in memory *)
Abort.

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
  - admit.
  - eapply deref_step_wf; eauto.
  - eapply newcall_step_wf; eauto.
  - eapply endcall_step_wf; eauto.
  - admit.
  - eapply None_step_wf; eauto.
Abort.
