From Coq Require Import ssreflect.
From stdpp Require Export list gmap.

Set Default Proof Using "Type".

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

Lemma foldr_gmap_delete_dom `{Countable K} {A B C: Type}
  (ma: gmap K A) (mb: gmap K B) (cs: list C) (f: C → K):
  dom (gset K) ma ≡ dom (gset K) mb →
  dom (gset K) (foldr (λ (c: C) ma, delete (f c) ma) ma cs)
  ≡ dom (gset K) (foldr (λ (c: C) mb, delete (f c) mb) mb cs).
Proof.
  intros. induction cs; simpl; [done|].
  by rewrite 2!dom_delete IHcs.
Qed.

Lemma dom_map_insert_is_Some `{FinMapDom K M D} {A} (m : M A) i x :
  is_Some (m !! i) → dom D (<[i:=x]>m) ≡ dom D m.
Proof.
  intros IS. rewrite dom_insert. apply (anti_symm (⊆)).
  - apply union_least; [|done]. by apply elem_of_subseteq_singleton, elem_of_dom.
  - by apply union_subseteq_r.
Qed.

Lemma foldl_fun_ext {A B} (f g: A → B → A) (a: A) (lb : list B):
  (∀ a b, b ∈ lb → f a b = g a b) → foldl f a lb = foldl g a lb.
Proof.
  revert a. induction lb as [|b lb IH]; [done|].
  intros a HB. simpl. rewrite HB; [by left|].
  apply IH. intros ???. apply HB. by right.
Qed.

Lemma foldl_fmap_shift_init {A B : Type}
  (f: A → B → A) (g: A → A) (a: A) (lb : list B) :
  (∀ a b, b ∈ lb → f (g a) b = g (f a b)) →
  g (foldl f a lb) = foldl f (g a) lb.
Proof.
  revert a. induction lb as [|b lb IH]; [done|].
  intros a HB. simpl. rewrite HB; [by left|].
  apply IH. intros ???. apply HB. by right.
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

Instance elem_of_list_suffix_proper {A : Type} (x:A) :
  Proper ((suffix) ==> impl) (x ∈).
Proof. intros l1 l2 [? ->] ?. rewrite elem_of_app. by right. Qed.

Instance elem_of_list_sublist_proper {A : Type} (x:A) :
  Proper ((sublist) ==> impl) (x ∈).
Proof.
  intros l1 l2 SUB. induction SUB; [done|..].
  - rewrite 2!elem_of_cons. intros []; [by left|right; auto].
  - intros ?. right. auto.
Qed.

Lemma list_find_None_inv {A} (P : A → Prop) `{∀ x, Decision (P x)} l :
  Forall (λ x, ¬ P x) l → list_find P l = None.
Proof.
  induction l as [|x l IHl]; [eauto|]. simpl. intros FA.
  rewrite decide_False; [apply (Forall_inv FA)|]. rewrite IHl; [|done].
  by eapply Forall_cons_1.
Qed.

Lemma list_find_Some_not_earlier {A} (P : A → Prop) `{∀ x, Decision (P x)} l i x:
  list_find P l = Some (i, x) ↔
  l !! i = Some x ∧ P x ∧ ∀ j y, (j < i)%nat → l !! j = Some y → ¬ P y.
Proof.
  revert i x.
  induction l as [|a l IH]; simpl; [naive_solver|]. intros i x.
  case decide => HP; split.
  - intros. simplify_eq. split; last split; [done..|intros; lia].
  - simpl. destruct i as [|i]; [naive_solver|]. simpl.
    intros [_ [_ Lt]]. exfalso. apply (Lt O a); [lia|done..].
  - move => /fmap_Some [[i' x'] [Eq1 Eq2]]. simpl in Eq2. simplify_eq.
    apply IH in Eq1 as [? [? Eq2]]. split; last split; [done..|].
    intros [|j] y Lt; simpl; [intros; by simplify_eq|apply Eq2; lia].
  - destruct i as [|i]; [naive_solver|].
    move => /= [Eq1 [HP1 Lt1]].
    rewrite (_: list_find P l = Some (i, x)); [|done].
    apply IH. split; last split; [done..|]. intros j y Lt Eq.
    apply (Lt1 (S j) y); [lia|done].
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

Lemma reserve_lookup {A: Type} (l: list A) (i : nat) (a: A) :
  l !! i = Some a → ∃ j, reverse l !! j = Some a ∧ (i + j + 1)%nat = length l.
Proof.
  revert i. induction l as [|b l IH]; simpl; intros i; [naive_solver|].
  rewrite reverse_cons.
  destruct i.
  - simpl. intros. simplify_eq. exists (length l). split; [|lia].
    rewrite lookup_app_r; rewrite reverse_length //.
    by rewrite Nat.sub_diag.
  - simpl. intros Eqi. have Lt := lookup_lt_Some _ _ _ Eqi.
    move : Eqi => /IH [j [Eqj Eql]].
    exists j. rewrite Eql. split; [|done]. rewrite lookup_app_l //.
    rewrite reverse_length. lia.
Qed.

Lemma list_find_fmap {A B : Type} (P : A → Prop) `{!∀ x, Decision (P x)}
      (f : B → A) (l : list B) :
  list_find P (f <$> l) = prod_map id f <$> list_find (P ∘ f) l.
Proof.
  induction l as [|x y IH]; [done|]. simpl.
  case_decide; [done|].
  change (list_fmap B A f y) with (f <$> y). (* FIXME it simplified too much *)
  rewrite IH. by destruct (list_find (P ∘ f) y).
Qed.

Lemma list_find_proper {A : Type}  (P Q : A → Prop)
      `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)} l :
  (∀ x, P x ↔ Q x) →
  list_find P l = list_find Q l.
Proof.
  intros HPQ. induction l as [|x y IH]; [done|]. simpl.
  erewrite decide_iff by done. by rewrite IH.
Qed.

Lemma list_fmap_omap {A B C : Type} (f : A → option B) (g : B → C) (l : list A) :
  g <$> omap f l = omap (λ x, g <$> (f x)) l.
Proof.
  induction l as [|x y IH]; [done|]. simpl.
  destruct (f x); [|done]. simpl. by f_equal.
Qed.

Lemma omap_ext' {A B C : Type} (f : A → option C) (g : B → option C) l1 l2 :
  Forall2 (λ a b, f a = g b) l1 l2 →
  omap f l1 = omap g l2.
Proof.
  induction 1 as [|x y l l' Hfg ? IH]; first done.
  simpl. rewrite Hfg. destruct (g y); last done.
  by f_equal.
Qed.
