From Coq Require Import ssreflect.
From stdpp Require Export list gmap.

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
