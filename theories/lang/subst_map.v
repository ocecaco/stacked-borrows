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

(** Substitution with a list of pairs instead of a pair of lists.
This lets us do a total operation. *)

Definition is_var {T: Type} (y: string) (x: string * T) :=
  x.1 = y.
Global Instance is_var_dec {T: Type} y x : Decision (@is_var T y x).
Proof. rewrite /is_var /=. apply _. Qed.

Definition subst_map_delete {T: Type} (b: binder) (xs : list (string * T)) :=
  if b is BNamed s then list_filter (λ x, ¬is_var s x) _ xs else xs.

Fixpoint subst_map (xs : list (string * result)) (e : expr) : expr :=
  match e with
  | Var y => if snd <$> list_find (is_var y) xs is Some (_, v) then of_result v else Var y
  | Val v => Val v
  | Call e el => Call (subst_map xs e) (map (subst_map xs) el)
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
        (subst_map (subst_map_delete x1 xs) e2)
  | Case e el => Case (subst_map xs e) (map (subst_map xs) el)
  end.

Lemma subst_map_empty e :
  subst_map [] e = e.
Proof.
  induction e using expr_ind; simpl; f_equal; eauto.
  - induction H; first done. simpl. by f_equal.
  - destruct b; done.
  - induction H; first done. simpl. by f_equal.
Qed.

Lemma subst_map_cons x rx xs e :
  subst_map ((x,rx)::xs) e = subst_map xs (subst x rx e).
Proof.
  revert x rx xs; induction e using expr_ind; intros xx rx xs; try (simpl; f_equal; eauto).
  - destruct (decide (x=xx)) as [<-|ne].
    + rewrite decide_True //. rewrite bool_decide_true //.
      destruct rx; done.
    + rewrite decide_False. { intros ?. apply ne. done. }
      rewrite bool_decide_false //.
      simpl. destruct (list_find (is_var x) xs); last done.
      simpl. destruct p as [? [? ?]]. done.
  - induction H; first done. simpl. f_equal; done.
  - destruct b; simpl. done.
    destruct (decide (s=xx)) as [<-|ne].
    + rewrite decide_False //. { intros HH. apply HH. done. }
      rewrite bool_decide_false //. intros ?. done.
    + rewrite decide_True //. { intros ?. apply ne. done. }
      rewrite bool_decide_true //. intros [= HH]. done.
  - induction H; first done. simpl. f_equal; done.
Qed.

Definition fn_lists_to_subst {T: Type} (xbs : list binder) (xes : list T) :=
  omap (λ '(x, e), if x is BNamed s then Some (s, e) else None) (zip xbs xes).

Lemma subst_l_map (xbs : list binder) (xes : list value) (e es : expr) :
  subst_l xbs (Val <$> xes) e = Some es →
  es = subst_map (fn_lists_to_subst xbs (ValR <$> xes)) e.
Proof.
  revert xes es e; induction xbs; intros xes es e; destruct xes; try done.
  - intros [= ->]. simpl.
    by rewrite subst_map_empty.
  - simpl.
    set eo := subst_l _ _ _. destruct eo eqn:EQ; last done.
    subst eo. intros [=<-].
    specialize (IHxbs _ _ _ EQ).
    destruct a.
    + done.
    + rewrite subst_map_cons. done.
Qed.

Lemma list_find_delete_None {T: Type} xb b (xs : list (string * T)) :
  list_find (is_var xb) xs = None →
  list_find (is_var xb) (subst_map_delete b xs) = None.
Proof.
  rewrite /subst_map_delete.
  induction xs; simpl.
  - by destruct b.
  - destruct b; simpl; first done.
    destruct a as [??]. case_decide; first done.
    intros Hfind. case_decide; simpl.
    + rewrite decide_False //. rewrite IHxs //.
      destruct (list_find (is_var xb) xs); done.
    + rewrite IHxs //.
      destruct (list_find (is_var xb) xs); done.
Qed.

Lemma list_find_delete_ne {T: Type} xb b (xs : list (string * T)) p :
  (if b is BNamed b then xb ≠ b else True) →
  snd <$> list_find (is_var xb) xs = Some p →
  snd <$> list_find (is_var xb) (subst_map_delete b xs) = Some p.
Proof.
  destruct b; first done. intros Hne.
  induction xs; simpl; first done.
  destruct p as [y ?].
  case_decide.
  - rewrite decide_True. { intros ?. apply Hne. etrans; done. }
    simpl. rewrite decide_True //.
  - case_decide; simpl; intros Heq.
    + rewrite decide_False //.
      destruct (list_find (is_var xb) xs) as [[i' [y' ?]]|]; last done.
      simpl in Heq. rewrite -IHxs. done.
      rewrite /subst_map_delete /filter.
      destruct (list_find _ _); done.
    + destruct (list_find (is_var xb) xs) as [[i' [y' ?]]|]; last done.
      simpl in Heq. rewrite -IHxs. done.
      rewrite /subst_map_delete /filter.
      destruct (list_find _ _); done.
Qed.

Lemma subst_subst_map_delete b (r : result) (xs : list (string * result)) e :
  list_find (is_var b) xs = None →
  subst b r (subst_map xs e) =
  subst_map ((b,r)::xs) e.
Proof.
  revert xs b r; induction e using expr_ind; intros xs xb xr Hfind;
  try (simpl; f_equal; by eauto).
  - destruct (decide (x=xb)) as [<-|ne]; simpl.
    + rewrite decide_True //. rewrite Hfind /=.
      rewrite bool_decide_true //.
    + rewrite decide_False //. { intros ?. apply ne. done. }
      destruct (list_find (is_var x) xs); simpl.
      * destruct p as [?[??]]. simpl. by destruct r.
      * rewrite bool_decide_false //.
  - simpl. f_equal; first by auto.
    induction H; first done. simpl. f_equal; by auto.
  - simpl. case_bool_decide.
    + f_equal; first by auto. rewrite IHe2.
      * apply list_find_delete_None. done.
      * rewrite /subst_map_delete /=.
        destruct b; try done.
        rewrite decide_True //. { intros ?. apply H. f_equal. done. }
    + f_equal; first by auto. subst b. simpl.
      rewrite decide_False //. intros HH. apply HH. done.
  - simpl. f_equal; first by auto.
    induction H; first done. simpl. f_equal; by auto.
Qed.

Definition subst_map_eq (xs1 xs2 : list (string * result)) :=
  ∀ x, snd <$> list_find (is_var x) xs1 = snd <$> list_find (is_var x) xs2.

Lemma subst_map_delete_proper (xs1 xs2 : list (string * result)) b :
  subst_map_eq xs1 xs2 →
  subst_map_eq (subst_map_delete b xs1) (subst_map_delete b xs2).
Proof.
  rewrite /subst_map_eq /subst_map_delete=>Heq x.
  destruct b; first by auto.
  specialize (Heq x). revert Heq; induction xs1; simpl.
  - intros Heq. rewrite (list_find_delete_None _ s) //.
    by destruct (list_find (is_var x) xs2).
  - 
    case_decide; simpl.
    + intros Heq.
      case_decide; simpl.
      * rewrite decide_True //. simpl. symmetry.
        apply (list_find_delete_ne _ (BNamed s)); last done.
        intros [=->]. done.
      * apply IHxs1.
      * 
    + rewrite decide_False //.
      rewrite (list_find_delete_None _ s); auto.
      by destruct (list_find (is_var x) xs2).
    + rewrite (list_find_delete_None _ s); auto.
      by destruct (list_find (is_var x) xs2).
  - 

Lemma subst_map_proper (xs1 xs2 : list (string * result)) e :
  subst_map_eq xs1 xs2 →
  subst_map xs1 e = subst_map xs2 e.
Proof.
  revert xs1 xs2; induction e using expr_ind; intros xs1 xs2 Heq; simpl;
  try (f_equal; by eauto).
  - rewrite Heq. case_match; done.
  - f_equal; first by auto.
    induction H; first done. simpl. f_equal; by auto.
  - f_equal; first by auto.
    apply IHe2.

Lemma subst'_subst_map_delete b (r : result) (xs : list (string * result)) e :
  subst' b r (subst_map (subst_map_delete b xs) e) =
  subst_map (if b is BNamed s then (s,r)::xs else xs) e.
Proof.
  destruct b; first done. simpl.
  rewrite subst_subst_map_delete.
  - admit.
  - 
