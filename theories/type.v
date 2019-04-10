From Coq Require Import Program.
From Coq Require Import ssreflect.
From stdpp Require Export list countable.

From stbor Require Export helpers.

Set Default Proof Using "Type".

Inductive mutability := Mutable | Immutable.
Inductive ref_kind :=
  | UniqueRef (* &mut *)
  | FrozenRef (* & *)
  | RawRef    (* * (raw) or & to UnsafeCell, or Box *)
  .
Definition is_unique_ref (kind: ref_kind) : bool :=
  match kind with UniqueRef => true | _ => false end.
Inductive pointer_kind := RefPtr (mut: mutability) | RawPtr | BoxPtr.

Inductive type :=
  | Scalar (sz: nat)
  | Reference (kind: pointer_kind) (T: type)
  | Unsafe (T: type)
  | Union (Ts: list type)
  | Product (Ts: list type)
  | Sum (Ts: list type)
  .
Bind Scope lrust_type with type.
Delimit Scope lrust_type with RustT.

(** Types that don't contain UnsafeCells. *)
Fixpoint is_freeze (T: type) : bool :=
  match T with
  | Scalar _ | Reference _ _ => true
  | Unsafe _ => false
  | Union Ts | Product Ts | Sum Ts => forallb is_freeze Ts
  end.

(** Physical size of types *)
Fixpoint list_nat_max (ns: list nat) (d: nat) :=
  match ns with
  | [] => d
  | n :: ns => n `max` ((list_nat_max ns) d)
  end.

Lemma list_nat_max_spec ns :
  ns = [] ∧ list_nat_max ns O = O ∨
  list_nat_max ns O ∈ ns ∧ ∀ (i: nat), i ∈ ns → (i ≤ list_nat_max ns O)%nat.
Proof.
  induction ns as [|i ns IHi]; simpl; [rewrite elem_of_nil; naive_solver|].
  right. destruct IHi as [[]|[In MAX]].
  - subst. rewrite /= Nat.max_0_r elem_of_list_singleton.
    setoid_rewrite elem_of_list_singleton. naive_solver.
  - split.
    + apply Max.max_case; [by left|by right].
    + move => i' /elem_of_cons [->|In']. apply Nat.le_max_l.
      etrans; first by apply MAX. apply Nat.le_max_r.
Qed.

Fixpoint tsize (T: type) : nat :=
  match T with
  | Scalar sz => sz
  | Reference _ _ => 1%nat     (* We do not go beyond pointers *)
  | Unsafe T => tsize T
  | Union Ts => list_nat_max (tsize <$> Ts) O
  | Product Ts => foldl (λ sz T, sz + tsize T)%nat O Ts
  | Sum Ts => 1 + list_nat_max (tsize <$> Ts) O
  end.

(** Tree size of types *)
Fixpoint tnode_size (T: type) : nat :=
  match T with
  | Scalar sz => 1%nat
  | Reference _ T => 1 + tnode_size T
  | Unsafe T => 1 + tnode_size T
  | Union Ts | Product Ts | Sum Ts => 1 + list_nat_max (tnode_size <$> Ts) O
  end.

Lemma tnode_size_elem_of T Ts:
  T ∈ Ts → (tnode_size T < 1 + list_nat_max (tnode_size <$> Ts) O)%nat.
Proof.
  intros IN.
  destruct (list_nat_max_spec (tnode_size <$> Ts)) as [[EMP ?]|[? MAX]].
  - move : EMP IN => /fmap_nil_inv ->. by intros ?%not_elem_of_nil.
  - eapply le_lt_trans.
    + by apply MAX, elem_of_list_fmap_1.
    + lia.
Qed.
Lemma tnode_size_elem_of_union T Ts :
  T ∈ Ts → (tnode_size T < tnode_size (Union Ts))%nat.
Proof. by apply tnode_size_elem_of. Qed.
Lemma tnode_size_elem_of_product T Ts :
  T ∈ Ts → (tnode_size T < tnode_size (Product Ts))%nat.
Proof. by apply tnode_size_elem_of. Qed.
Lemma tnode_size_elem_of_sum T Ts :
  T ∈ Ts → (tnode_size T < tnode_size (Sum Ts))%nat.
Proof. by apply tnode_size_elem_of. Qed.

Section type_general_ind.
Variable (P : type → Prop)
         (F1: ∀ sz, P (Scalar sz))
         (F2: ∀ kind T, P T → P (Reference kind T))
         (F3: ∀ T, P T → P (Unsafe T))
         (F4: ∀ Ts, (∀ T, T ∈ Ts → P T) → P (Union Ts))
         (F5: ∀ Ts, (∀ T, T ∈ Ts → P T) → P (Product Ts))
         (F6: ∀ Ts, (∀ T, T ∈ Ts → P T) → P (Sum Ts)).
Program Fixpoint type_elim
         (T: type) {measure (tnode_size T)} : P T :=
    match T with
    | Scalar sz => F1 sz
    | Reference kind T => F2 kind T (type_elim T)
    | Unsafe T => F3 T (type_elim T)
    | Union Ts => F4 Ts (λ T (IN: T ∈ Ts), type_elim T)
    | Product Ts => F5 Ts (λ T (IN: T ∈ Ts), type_elim T)
    | Sum Ts => F6 Ts (λ T (IN: T ∈ Ts), type_elim T)
    end.
Next Obligation. move=> ? _ ?? <- /=. lia. Qed.
Next Obligation. move=> ? _ ? <- /=. lia. Qed.
Next Obligation. naive_solver eauto using tnode_size_elem_of_union. Qed.
Next Obligation. naive_solver eauto using tnode_size_elem_of_product. Qed.
Next Obligation. naive_solver eauto using tnode_size_elem_of_sum. Qed.
Next Obligation. apply well_founded_ltof. Qed.
End type_general_ind.

(** Decidability *)

Instance type_inhabited : Inhabited type := populate (Scalar 0).

Instance mutability_eq_dec : EqDecision mutability.
Proof. solve_decision. Defined.
Instance mutability_countable : Countable mutability.
Proof.
  refine (inj_countable'
    (λ m, match m with Mutable => 0 | Immutable => 1 end)
    (λ x, match x with 0 => Mutable | _ => Immutable end) _); by intros [].
Qed.

Instance pointer_kind_eq_dec : EqDecision pointer_kind.
Proof. solve_decision. Defined.
Instance pointer_kind_countable : Countable pointer_kind.
Proof.
  refine (inj_countable
          (λ k, match k with
              | RefPtr mut => inl $ inl mut
              | RawPtr => inl $ inr ()
              | BoxPtr => inr ()
              end)
          (λ s, match s with
              | inl (inl mut) => Some $ RefPtr mut
              | inl (inr _) => Some  RawPtr
              | inr _ => Some BoxPtr
              end) _); by intros [].
Qed.

Fixpoint type_beq (T T': type) : bool :=
  let fix type_list_beq Ts Ts' :=
    match Ts, Ts' with
    | [], [] => true
    | T::Ts, T'::Ts' => type_beq T T' && type_list_beq Ts Ts'
    | _, _ => false
    end
  in
  match T, T' with
  | Scalar n, Scalar n' => bool_decide (n = n')
  | Reference k T, Reference k' T' => bool_decide (k = k') && type_beq T T'
  | Unsafe T, Unsafe T' => type_beq T T'
  | Union Ts, Union Ts' | Product Ts, Product Ts' | Sum Ts, Sum Ts' =>
      type_list_beq Ts Ts'
  | _, _ => false
  end.
Lemma type_beq_correct (T1 T2 : type) : type_beq T1 T2 ↔ T1 = T2.
Proof.
  revert T1 T2; fix FIX 1;
    destruct T1 as [| | |Ts1|Ts1|Ts1],
             T2 as [| | |Ts2|Ts2|Ts2];
    simpl; try done;
    rewrite ?andb_True ?bool_decide_spec ?FIX;
    try (split; intro; [destruct_and?|split_and?]; congruence).
  - match goal with |- context [?F Ts1 Ts2] => assert (F Ts1 Ts2 ↔ Ts1 = Ts2) end.
    { revert Ts2. induction Ts1 as [|Ts1h Ts1q]; destruct Ts2; try done.
      specialize (FIX Ts1h). naive_solver. }
    clear FIX. naive_solver.
  - match goal with |- context [?F Ts1 Ts2] => assert (F Ts1 Ts2 ↔ Ts1 = Ts2) end.
    { revert Ts2. induction Ts1 as [|Ts1h Ts1q]; destruct Ts2; try done.
      specialize (FIX Ts1h). naive_solver. }
    clear FIX. naive_solver.
  - match goal with |- context [?F Ts1 Ts2] => assert (F Ts1 Ts2 ↔ Ts1 = Ts2) end.
    { revert Ts2. induction Ts1 as [|Ts1h Ts1q]; destruct Ts2; try done.
      specialize (FIX Ts1h). naive_solver. }
    clear FIX. naive_solver.
Qed.
Instance type_eq_dec : EqDecision type.
Proof.
  refine (λ T1 T2, cast_if (decide (type_beq T1 T2))); by rewrite -type_beq_correct.
Defined.
Instance type_countable : Countable type.
Proof.
  refine (inj_countable'
    (fix go T := match T with
     | Scalar sz => GenNode 0 [GenLeaf $ inl sz]
     | Reference kind T => GenNode 1 [GenLeaf $ inr kind; go T]
     | Unsafe T => GenNode 2 [go T]
     | Union Ts => GenNode 3 (go <$> Ts)
     | Product Ts => GenNode 4 (go <$> Ts)
     | Sum Ts => GenNode 5 (go <$> Ts)
     end)
    (fix go s := match s with
     | GenNode 0 [GenLeaf (inl sz)] => Scalar sz
     | GenNode 1 [GenLeaf (inr kind); T] => Reference kind (go T)
     | GenNode 2 [T] => Unsafe (go T)
     | GenNode 3 Ts => Union (go <$> Ts)
     | GenNode 4 Ts => Product (go <$> Ts)
     | GenNode 5 Ts => Sum (go <$> Ts)
     | _ => Scalar 0
     end) _).
  fix FIX 1. intros []; f_equal=>//; revert Ts; clear -FIX.
  - fix FIX_INNER 1. intros []; [done|]. by simpl; f_equal.
  - fix FIX_INNER 1. intros []; [done|]. by simpl; f_equal.
  - fix FIX_INNER 1. intros []; [done|]. by simpl; f_equal.
Qed.

(** Syntactical subtyping *)
Fixpoint subtype' (Tc T : type) (cur: nat) : list nat :=
  let base: list nat := if bool_decide (Tc = T) then [cur] else [] in
  match T with
  | Unsafe T => base ++ subtype' Tc T cur
  | Union Ts => foldl (λ ns T, ns ++ subtype' Tc T cur) base Ts
  | Sum Ts => foldl (λ ns T, ns ++ subtype' Tc T (cur + 1)) base Ts
  | Product Ts =>
      (foldl (λ sns T, ((sns.1 + tsize T)%nat, sns.2 ++ subtype' Tc T sns.1))
             (cur, base) Ts).2
  | _ => base
  end.
Definition subtype Tc T := subtype' Tc T O.

Lemma subtype_O_elem_of T : O ∈ subtype T T.
Proof.
  rewrite /subtype. destruct T; simpl; (rewrite bool_decide_true; [done|]).
  - by apply elem_of_list_singleton.
  - by apply elem_of_list_singleton.
  - rewrite elem_of_app elem_of_list_singleton. by left.
  - remember ((Union Ts)) as Tl. clear HeqTl. remember [0%nat] as nl.
    have IN: 0%nat ∈ nl by rewrite Heqnl elem_of_list_singleton. clear Heqnl.
    revert Tl nl IN. induction Ts as [|?? IH]; intros Tl nl IN; [done|].
    apply IH. rewrite elem_of_app. by left.
  - remember ((Product Ts)) as Tl. clear HeqTl. remember 0%nat as n.
    rewrite {1}Heqn. remember [n] as nl.
    have IN: 0%nat ∈ nl by rewrite Heqnl elem_of_list_singleton. clear Heqnl Heqn.
    revert n Tl nl IN. induction Ts as [|?? IH]; intros n Tl nl IN; [done|].
    apply IH. rewrite /= elem_of_app. by left.
  - remember ((Sum Ts)) as Tl. clear HeqTl. remember [0%nat] as nl.
    have IN: 0%nat ∈ nl by rewrite Heqnl elem_of_list_singleton. clear Heqnl.
    revert Tl nl IN. induction Ts as [|?? IH]; intros Tl nl IN; [done|].
    apply IH. rewrite elem_of_app. by left.
Qed.

Lemma foldl_inner_app_elem_of {A B} (f: B → list A) la0 lb :
  ∀ a, a ∈ foldl (λ la b, la ++ f b) la0 lb → a ∈ la0 ∨ ∃ b, b ∈ lb ∧ a ∈ f b.
Proof.
  revert la0. induction lb as [|b lb IH]; move => la0 a; [by left|].
  move => /IH [/elem_of_app[|]|[b' [? ?]]]; [by left|right..].
  - exists b. split; [by left|done].
  - exists b'. split; [by right|done].
Qed.

Lemma foldl_inner_app_not_nil {A B} (f: B → list A) lb :
  foldl (λ la b, la ++ f b) [] lb ≠ [] → ∃ b, b ∈ lb ∧ f b ≠ [].
Proof.
  destruct (foldl (λ la b, la ++ f b) [] lb) as [|a la] eqn:Eq; [done|].
  move => _.
  destruct (foldl_inner_app_elem_of f [] lb a) as [IN|[b [? ?%elem_of_not_nil]]].
  - rewrite Eq. by left.
  - exfalso. move : IN. by apply not_elem_of_nil.
  - by exists b.
Qed.

Lemma foldl_inner_app_elem_of_2 {A B C}
  (fL: C → B → C) (fR: B → C → list A) c0 la0 lb :
  ∀ a, a ∈ (foldl (λ cla b, (fL cla.1 b, cla.2 ++ fR b cla.1)) (c0, la0) lb).2 →
  a ∈ la0 ∨ ∃ b c, b ∈ lb ∧ a ∈ fR b c.
Proof.
  revert c0 la0. induction lb as [|b lb IH]; move => c0 la0 a; [by left|].
  move => /IH [/elem_of_app[|]|[b' [c' [? ?]]]]; [by left|right..].
  - exists b, c0. split; [by left|done].
  - exists b', c'. split; [by right|done].
Qed.

Lemma foldl_inner_app_not_nil_2 {A B C}
  (fL: C → B → C) (fR: B → C → list A) c lb :
  (foldl (λ cla b, (fL cla.1 b, cla.2 ++ fR b cla.1)) (c, []) lb).2 ≠ [] →
  ∃ b c, b ∈ lb ∧ fR b c ≠ [].
Proof.
  destruct ((foldl (λ cla b, (fL cla.1 b, cla.2 ++ fR b cla.1)) (c, []) lb).2)
    as [|a la] eqn:Eq; [done|]. move => _.
  destruct (foldl_inner_app_elem_of_2 fL fR c [] lb a)
    as [IN|[b [c' [? ?%elem_of_not_nil]]]].
  - rewrite Eq. by left.
  - exfalso. move : IN. by apply not_elem_of_nil.
  - by exists b, c'.
Qed.

Lemma foldl_inner_app_fmap {A B} (f: B → list A) (g: A → A) la0 lb :
  g <$> (foldl (λ la b, la ++ f b) la0 lb)
  = foldl (λ la b, la ++ (g <$> f b)) (g <$> la0) lb.
Proof.
  revert la0. induction lb as [|b lb IH]; move => la0; [done|].
  by rewrite /= IH fmap_app.
Qed.

Lemma subtype'_shift Tc T n m:
  subtype' Tc T (n + m) = (λ n, n + m)%nat <$> subtype' Tc T n.
Proof.
  revert n.
  apply (type_elim (λ T, ∀ n, subtype' _ T _ = _ <$> subtype' _ T _)).
  - intros ??. simpl. by case_bool_decide.
  - intros ???. simpl. by case_bool_decide.
  - intros ?. simpl. case_bool_decide; [|done].
    intros IH ?. by rewrite fmap_app IH.
  - intros ? IH n. simpl.
    rewrite (foldl_fun_ext
              (λ ns T0, ns ++ subtype' Tc T0 (n + m))
              (λ ns T0, ns ++ ((λ n, n + m)%nat <$> subtype' Tc T0 n))).
    + by move => ?? /IH ->.
    + rewrite foldl_inner_app_fmap. by case_bool_decide.
  - intros ? IH n. simpl.
    set g : nat * list nat → nat * list nat :=
      λ sns, ((λ n, n + m)%nat sns.1, (λ n, n + m)%nat <$> sns.2).
    rewrite (_: ((n + m)%nat,
                if bool_decide (Tc = Product Ts) then [(n + m)%nat] else [])
              = g (n, if bool_decide (Tc = Product Ts) then [n] else []));
      first by (rewrite /g /=; case_bool_decide).
    rewrite -foldl_fmap_shift_init; [|done].
    move => ?? /IH IH1. rewrite /g /=. f_equal; [lia|by rewrite fmap_app IH1].
  - intros ? IH n. simpl.
    rewrite (foldl_fun_ext
              (λ ns T0, ns ++ subtype' Tc T0 (n + m + 1))
              (λ ns T0, ns ++ ((λ n, n + m)%nat <$> subtype' Tc T0 (n + 1)))).
    + move => ?? /IH IH1. rewrite (_: (n + m + 1) = (n + 1) + m)%nat; [lia|].
      by rewrite IH1.
    + rewrite foldl_inner_app_fmap. by case_bool_decide.
Qed.

Lemma subtype_ne T Ts :
  subtype T Ts ≠ [] → T = Ts ∨
  match Ts with
  | Unsafe Ts => subtype T Ts ≠ []
  | Union Ts | Sum Ts | Product Ts => ∃ Tc, Tc ∈ Ts ∧ subtype T Tc ≠ []
  | _ => True
  end.
Proof.
  destruct Ts.
  - rewrite /subtype /=. case_bool_decide; [by left|done].
  - rewrite /subtype /=. case_bool_decide; [by left|done].
  - rewrite /subtype /=. case_bool_decide; [by left|].
      rewrite app_nil_l. by right.
  - rewrite /subtype /=. case_bool_decide; [by left|].
    move => /foldl_inner_app_not_nil. by right.
  - rewrite /subtype /=. case_bool_decide; [by left|].
    move => /(foldl_inner_app_not_nil_2 (λ n T0, (n + tsize T0))%nat (subtype' T))
      [Tc [c [?]]]. rewrite -(Nat.add_0_l c) subtype'_shift.
    move => NE. right. exists Tc. split; [done|].
    move => NIL. apply NE. by rewrite NIL.
  - rewrite /subtype /=. case_bool_decide; [by left|].
    move => /foldl_inner_app_not_nil [Tc [IN]].
    rewrite -(Nat.add_0_l 1) subtype'_shift => NE.
    right. exists Tc. split; [done|] => NIL. apply NE. by rewrite NIL.
Qed.

Lemma subtype_tnoze_size T1 T2 :
  subtype T1 T2 ≠ [] → (tnode_size T1 ≤ tnode_size T2)%nat.
Proof.
  apply (type_elim (λ T, subtype _ T ≠ [] → (_ ≤ tnode_size T)%nat)).
  - intros ?. rewrite /subtype /=. case_bool_decide; [|done]. by subst.
  - intros ?? _. rewrite /subtype /=. case_bool_decide; [|done]. by subst.
  - move => ? IH /subtype_ne [->//|/IH /=]. lia.
  - move => Ts IH /subtype_ne [->//|[Tc [IN NE]]].
    eapply Nat.lt_le_incl, le_lt_trans; [apply (IH _ IN NE)|].
    by apply tnode_size_elem_of_union.
  - move => Ts IH /subtype_ne [->//|[Tc [IN NE]]].
    eapply Nat.lt_le_incl, le_lt_trans; [apply (IH _ IN NE)|].
    by apply tnode_size_elem_of_product.
  - move => Ts IH /subtype_ne [->//|[Tc [IN NE]]].
    eapply Nat.lt_le_incl, le_lt_trans; [apply (IH _ IN NE)|].
    by apply tnode_size_elem_of_sum.
Qed.


(*
Lemma subtype_union_cons T Tc Ts :
  T ≠ Union (Tc :: Ts) →
  subtype T (Union (Tc :: Ts)) = subtype T Tc ++ subtype T (Union Ts).
Proof.
  rewrite /subtype. remember O as n. clear Heqn.
  revert n. induction Ts as [|Tc' Ts IH]; intros n.
  - intros ?. simpl. rewrite decide_False; [|done]. admit.
  -
Lemma tsize_product_cons T Ts :
  (tsize (Product (T :: Ts)) = tsize T + tsize (Product Ts))%nat.
Proof.
  rewrite /= -{1}(Nat.add_0_r (tsize T)). remember O as n. clear Heqn.
  revert n. induction Ts as [|Tc Ts IH]; intros n; [done|].
  by rewrite /= -Nat.add_assoc IH.
Qed.

Lemma subtype_product_here T Tc Ts :
  ∀ n, n ∈ subtype T Tc → n ∈ subtype T (Product (Tc :: Ts)).
Proof.
  intros n. rewrite /subtype. simpl.
Abort. *)

Lemma tsize_product_cons T Ts :
  (tsize (Product (T :: Ts)) = tsize T + tsize (Product Ts))%nat.
Proof.
  rewrite /= -{1}(Nat.add_0_r (tsize T)). remember O as n. clear Heqn.
  revert n. induction Ts as [|Tc Ts IH]; intros n; [done|].
  by rewrite /= -Nat.add_assoc IH.
Qed.

Lemma tsize_subtype_of_product T Ts :
  T ∈ Ts → (tsize T ≤ tsize (Product Ts))%nat.
Proof.
  induction Ts as [|Tc Ts IH]; [by intros ?%not_elem_of_nil|].
  rewrite tsize_product_cons. move => /elem_of_cons [->|/IH]; lia.
Qed.
