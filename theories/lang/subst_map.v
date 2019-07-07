From stbor.lang Require Import expr_semantics.

Definition is_var {T: Type} (y: string) (x: string * T) :=
  x.1 = y.
Global Instance is_var_dec {T: Type} y x : Decision (@is_var T y x).
Proof. rewrite /is_var /=. apply _. Qed.

(** Substitution with a list of pairs instead of a pair of lists.
This lets us do a total operation. *)
Fixpoint subst_map (xs : list (string * result)) (e : expr) : expr :=
  match e with
  | Var y => if list_find (is_var y) xs is Some (_, (_, v)) then of_result v else Var y
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
        (subst_map (if x1 is BNamed s then list_filter (λ x, ¬is_var s x) _ xs else xs) e2)
  | Case e el => Case (subst_map xs e) (map (subst_map xs) el)
  end.

Lemma subst_map_empty e :
  subst_map [] e = e.
Proof.
  induction e; simpl; f_equal; eauto.
  - admit.
  - destruct x; done.
  - admit.
Admitted.

Lemma subst_map_cons x rx xs e :
  subst_map ((x,rx)::xs) e = subst_map xs (subst x rx e).
Proof.
  revert x rx xs; induction e; intros xx rx xs; try (simpl; f_equal; eauto).
  - destruct (decide (x=xx)) as [<-|ne].
    + rewrite decide_True //. rewrite bool_decide_true //.
      destruct rx; done.
    + rewrite decide_False. { intros ?. apply ne. done. }
      rewrite bool_decide_false //.
      simpl. destruct (list_find (is_var x) xs); last done.
      simpl. destruct p as [? [? ?]]. done.
  - admit.
  - destruct x; simpl. done.
    destruct (decide (s=xx)) as [<-|ne].
    + rewrite decide_False //. { intros HH. apply HH. done. }
      rewrite bool_decide_false //. intros ?. done.
    + rewrite decide_True //. { intros ?. apply ne. done. }
      rewrite bool_decide_true //. intros [= HH]. done.
  - admit.
Admitted.

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
