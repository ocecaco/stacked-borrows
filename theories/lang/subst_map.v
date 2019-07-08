From stbor.lang Require Import expr_semantics.

(** Induction scheme for expressions *)
Lemma expr_ind (P : expr → Prop):
  (∀ v, P (Val v)) →
  (∀ x, P (Var x)) →
  (∀ e el, P e → Forall P el → P (Call e el)) →
  (∀ e, P e → P (InitCall e)) →
  (∀ e, P e → P (EndCall e)) →
  (∀ e1 e2, P e1 → P e2 → P (Proj e1 e2)) →
  (∀ e1 e2, P e1 → P e2 → P (Conc e1 e2)) →
  (∀ o e1 e2, P e1 → P e2 → P (BinOp o e1 e2)) →
  (∀ l tg ty, P (Place l tg ty)) →
  (∀ e ty, P e → P (Deref e ty)) →
  (∀ e, P e → P (Ref e)) →
  (∀ e, P e → P (Copy e)) →
  (∀ e1 e2, P e1 → P e2 → P (Write e1 e2)) →
  (∀ ty, P (Alloc ty)) →
  (∀ e, P e → P (Free e)) →
  (∀ e k, P e → P (Retag e k)) →
  (∀ b e1 e2, P e1 → P e2 → P (Let b e1 e2)) →
  (∀ e el, P e → Forall P el → P (Case e el)) →
  ∀ e, P e.
Proof.
  intros. revert e. fix REC 1. destruct e; try
  (* Find head symbol, then find lemma for that symbol.
     We have to be this smart because we can't use the unguarded [REC]! *)
  match goal with
  | |- P (?head _ _ _) =>
    match goal with H : context[head] |- _ => apply H; try done end
  | |- P (?head _ _) =>
    match goal with H : context[head] |- _ => apply H; try done end
  | |- P (?head _) =>
    match goal with H : context[head] |- _ => apply H; try done end
  end.
  (* 2 remaining cases: The [Forall]. *)
  induction el; eauto using Forall.
  induction el; eauto using Forall.
Qed.

(** Parallel Substitution. *)
Definition binder_delete {T} (b: binder) (xs: gmap string T) :=
  if b is BNamed x then delete x xs else xs.
Definition binder_insert {T} (b: binder) (r: T) (xs: gmap string T) :=
  if b is BNamed x then <[x:=r]> xs else xs.
Fixpoint subst_map (xs : gmap string result) (e : expr) : expr :=
  match e with
  | Var y => if xs !! y is Some v then of_result v else Var y
  | Val v => Val v
  | Call e el => Call (subst_map xs e) (fmap (subst_map xs) el)
  | InitCall e => InitCall (subst_map xs e)
  | EndCall e => EndCall (subst_map xs e)
  | Place l tag T => Place l tag T
  | BinOp op e1 e2 => BinOp op (subst_map xs e1) (subst_map xs e2)
  | Proj e1 e2 => Proj (subst_map xs e1) (subst_map xs e2)
  | Conc e1 e2 => Conc (subst_map xs e1) (subst_map xs e2)
  | Copy e => Copy (subst_map xs e)
  | Write e1 e2 => Write (subst_map xs e1) (subst_map xs e2)
  | Alloc T => Alloc T
  | Free e => Free (subst_map xs e)
  | Deref e T => Deref (subst_map xs e) T
  | Ref e => Ref (subst_map xs e)
  | Retag e kind => Retag (subst_map xs e) kind
  | Let x1 e1 e2 =>
      Let x1
        (subst_map xs e1)
        (subst_map (binder_delete x1 xs) e2)
  | Case e el => Case (subst_map xs e) (fmap (subst_map xs) el)
  end.

Lemma subst_map_empty e :
  subst_map ∅ e = e.
Proof.
  induction e using expr_ind; simpl; f_equal; eauto.
  - induction H; first done. simpl. by f_equal.
  - destruct b; first done. simpl. rewrite delete_empty. done.
  - induction H; first done. simpl. by f_equal.
Qed.

Lemma subst_map_subst map x (r: value) (e: expr) :
  subst_map map (subst x r e) = subst_map (<[x:=ValR r]>map) e.
Proof.
  revert x r map; induction e using expr_ind; intros xx r map; simpl;
  try (f_equal; eauto).
  - case_bool_decide.
    + simplify_eq/=. rewrite lookup_insert. destruct r; done.
    + rewrite lookup_insert_ne //.
  - induction H; first done. simpl. f_equal; done.
  - destruct b; simpl. done.
    case_bool_decide.
    + rewrite IHe2. f_equal. rewrite delete_insert_ne //.
      intros ?. apply H. f_equal. done.
    + simplify_eq/=. rewrite delete_insert_delete //.
  - induction H; first done. simpl. f_equal; done.
Qed.

(** Turning list-subst into par-subst while preserving a pointwise property.
FIXME: There probably is a way to do this with a lemma that talks about
just one list... *)
Lemma subst_l_map (xbs : list binder) (xes xet : list value)
  (ebs ebt es et : expr) (R : result → result → Prop) :
  subst_l xbs (Val <$> xes) ebs = Some es →
  subst_l xbs (Val <$> xet) ebt = Some et →
  Forall2 R (ValR <$> xes) (ValR <$> xet) →
  ∃ map : gmap string (result * result),
  es = subst_map (fst <$> map) ebs ∧ et = subst_map (snd <$> map) ebt ∧
  map_Forall (λ _ '(s, t), R s t) map.
Proof.
  revert xes xet ebs ebt es et; induction xbs;
  intros xes xet ebs ebt es et Hsubst1 Hsubst2 HR; simplify_eq/=.
  - exists ∅. rewrite !fmap_empty !subst_map_empty.
    destruct xes; last done. destruct xet; last done. simplify_eq/=.
    split; first done. split; first done.
    apply map_Forall_empty.
  - destruct xes as [|ees xes]; first done. destruct xet as [|eet xet]; first done.
    inversion HR. simplify_eq/=. destruct a.
    + eapply IHxbs; eauto.
    + edestruct (IHxbs xes xet) as (map & ? & ? & ?); [done..|].
      exists (<[s:=(ValR ees, ValR eet)]> map). simplify_eq/=.
      rewrite !subst_map_subst !fmap_insert.
      split; first done. split; first done.
      apply map_Forall_insert_2; done.
Qed.

Lemma subst_subst_map x (r: result) map e :
  subst x r (subst_map (delete x map) e) =
  subst_map (<[x:=r]>map) e.
Proof.
  revert map r x; induction e using expr_ind; intros map r xx; simpl;
  try (f_equal; eauto).
  - destruct (decide (xx=x)) as [->|Hne].
    + rewrite lookup_delete // lookup_insert //. simpl.
      rewrite bool_decide_true //.
    + rewrite lookup_delete_ne // lookup_insert_ne //.
      destruct (map !! x) as [rr|].
      * by destruct rr.
      * simpl. rewrite bool_decide_false //.
  - induction H; first done. simpl. by f_equal.
  - destruct b; simpl; first by auto.
    case_bool_decide.
    + rewrite delete_insert_ne //. { intros [=EQ]. apply H. f_equal. done. }
      rewrite delete_commute. apply IHe2.
    + simplify_eq. rewrite delete_idemp delete_insert_delete. done.
  - induction H; first done. simpl. by f_equal.
Qed.

Lemma subst'_subst_map b (r: result) map e :
  subst' b r (subst_map (binder_delete b map) e) =
  subst_map (binder_insert b r map) e.
Proof.
  destruct b; first done.
  exact: subst_subst_map.
Qed.

Lemma binder_insert_map {T U: Type} b (r: T) (f : T → U) map :
  binder_insert b (f r) (f <$> map) =
  f <$> binder_insert b r map.
Proof.
  destruct b; first done. simpl.
  rewrite fmap_insert. done.
Qed.
