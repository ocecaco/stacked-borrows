From stdpp Require Import fin_maps.
From stbor Require Export lang.
Set Default Proof Using "Type".

(** We define an alternative representation of expressions in which the
embedding of values and closed expressions is explicit. By reification of
expressions into this type we can implement substitution, closedness
checking, atomic checking, and conversion into values, by computation. *)
Module W.
Inductive expr :=
| Val (v : val) (e : bor_lang.expr) (H : to_val e = Some v)
| ClosedExpr (e : bor_lang.expr) `{!Closed [] e}
| Lit (l : lit)
| Var (x : string)
| App (e : expr) (el : list expr)
| Rec (f : binder) (xl : list binder) (e : expr)
| BinOp (op : bin_op) (e1 e2 : expr)
| TVal (el: list expr)
| Proj (e1 e2: expr)
| Conc (e1 e2: expr)
| Place (l : loc) (tag : borrow) (T: type)
| Deref (e : expr) (T : type) (mut : option mutability)
| Ref (e : expr)
| Field (e : expr) (path: list nat)
| Copy (e : expr)
| Write (e1 e2 : expr)
| Alloc (T : type)
| Free (e : expr)
| CAS (e0 e1 e2 : expr)
| AtomWrite (e1 e2: expr)
| AtomRead (e: expr)
| NewCall
| EndCall (e : expr)
| Retag (e : expr) (kind : retag_kind)
| Case (e : expr) (el : list expr)
| Fork (e : expr).

Fixpoint to_expr (e : expr) : bor_lang.expr :=
  match e with
  | Val v e' _ => e'
  | ClosedExpr e => e
  | Lit l => bor_lang.Lit l
  | Var x => bor_lang.Var x
  | Rec f xl e => bor_lang.Rec f xl (to_expr e)
  | App e el => bor_lang.App (to_expr e) (map to_expr el)
  | BinOp op e1 e2 => bor_lang.BinOp op (to_expr e1) (to_expr e2)
  | TVal el => bor_lang.TVal (map to_expr el)
  | Proj e1 e2 => bor_lang.Proj (to_expr e1) (to_expr e2)
  | Conc e1 e2 => bor_lang.Conc (to_expr e1) (to_expr e2)
  | Place l tag T => bor_lang.Place l tag T
  | Deref e T mut => bor_lang.Deref (to_expr e) T mut
  | Ref e => bor_lang.Ref (to_expr e)
  | Field e path => bor_lang.Field (to_expr e) path
  | Copy e => bor_lang.Copy (to_expr e)
  | Write e1 e2 => bor_lang.Write (to_expr e1) (to_expr e2)
  | Alloc T => bor_lang.Alloc T
  | Free e => bor_lang.Free (to_expr e)
  | CAS e0 e1 e2 => bor_lang.CAS (to_expr e0) (to_expr e1) (to_expr e2)
  | AtomRead e => bor_lang.AtomRead (to_expr e)
  | AtomWrite e1 e2 => bor_lang.AtomWrite (to_expr e1) (to_expr e2)
  | NewCall => bor_lang.NewCall
  | EndCall e => bor_lang.EndCall (to_expr e)
  | Retag e kind => bor_lang.Retag (to_expr e) kind
  | Case e el => bor_lang.Case (to_expr e) (map to_expr el)
  | Fork e => bor_lang.Fork (to_expr e)
  end.

Ltac of_expr e :=
  lazymatch e with
  | bor_lang.Lit ?l => constr:(Lit l)
  | bor_lang.Var ?x => constr:(Var x)
  | bor_lang.Rec ?f ?xl ?e => let e := of_expr e in constr:(Rec f xl e)
  | bor_lang.App ?e ?el =>
      let e := of_expr e in let el := of_expr el in constr:(App e el)
  | bor_lang.BinOp ?op ?e1 ?e2 =>
      let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(BinOp op e1 e2)
  | bor_lang.TVal ?el => let el := of_expr el in constr:(TVal el)
  | bor_lang.Place ?l ?tag ?T => constr:(Place l tag T)
  | bor_lang.Proj ?e1 ?e2 =>
      let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Proj e1 e2)
  | bor_lang.Conc ?e1 ?e2 =>
      let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Conc e1 e2)
  | bor_lang.Deref ?e ?T ?mut => let e := of_expr e in constr:(Deref e T mut)
  | bor_lang.Ref ?e => let e := of_expr e in constr:(Ref e)
  | bor_lang.Field ?e ?path => let e := of_expr e in constr:(Field e path)
  | bor_lang.Copy ?e => let e := of_expr e in constr:(Copy e)
  | bor_lang.Write ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Write e1 e2)
  | bor_lang.Alloc ?T => constr:(Alloc T)
  | bor_lang.Free ?e => let e := of_expr e in constr:(Free e)
  | bor_lang.CAS ?e0 ?e1 ?e2 =>
     let e0 := of_expr e0 in let e1 := of_expr e1 in let e2 := of_expr e2 in
     constr:(CAS e0 e1 e2)
  | bor_lang.AtomRead ?e => let e := of_expr e in constr:(AtomRead e)
  | bor_lang.AtomWrite ?e1 ?e2 =>
      let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(AtomWrite e1 e2)
  | bor_lang.NewCall => constr:(NewCall)
  | bor_lang.EndCall ?e => let e := of_expr e in constr:(EndCall e)
  | bor_lang.Retag ?e ?kind => let e := of_expr e in constr:(Retag e kind)
  | bor_lang.Case ?e ?el =>
     let e := of_expr e in let el := of_expr el in constr:(Case e el)
  | bor_lang.Fork ?e => let e := of_expr e in constr:(Fork e)
  | @nil bor_lang.expr => constr:(@nil expr)
  | @cons bor_lang.expr ?e ?el =>
      let e := of_expr e in let el := of_expr el in constr:(e::el)
  | to_expr ?e => e
  | of_val ?v => constr:(Val v (of_val v) (to_of_val v))
  | _ => match goal with
         | H : to_val e = Some ?v |- _ => constr:(Val v e H)
         | H : Closed [] e |- _ => constr:(@ClosedExpr e H)
         end
  end.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Val _ _ _ | ClosedExpr _ => true
  | Lit _ | Place _ _ _ | Alloc _ | NewCall => true
  | Var x => bool_decide (x ∈ X)
  | Rec f xl e => is_closed (f :b: xl +b+ X) e
  | BinOp _ e1 e2 | Write e1 e2 | AtomWrite e1 e2
      | Proj e1 e2 | Conc e1 e2 => is_closed X e1 && is_closed X e2
  | TVal el => forallb (is_closed X) el
  | App e el | Case e el => is_closed X e && forallb (is_closed X) el
  | Copy e | AtomRead e| Free e | Fork e | Field e _
    | Deref e _ _ | Ref e | EndCall e | Retag e _ => is_closed X e
  | CAS e0 e1 e2 => is_closed X e0 && is_closed X e1 && is_closed X e2
  end.
Lemma is_closed_correct X e : is_closed X e → bor_lang.is_closed X (to_expr e).
Proof.
  revert e X. fix FIX 1; destruct e=>/=;
    try naive_solver eauto using is_closed_to_val, is_closed_weaken_nil.
  - induction el=>/=; naive_solver.
  - induction el=>/=; naive_solver.
  - induction el=>/=; naive_solver.
Qed.

Definition to_immediate (e: expr): option immediate :=
  match e with
  | Rec f xl e =>
    if decide (is_closed (f :b: xl +b+ []) e) is left H
    then Some (@RecV f xl (to_expr e) (is_closed_correct _ _ H)) else None
  | Lit l => Some (LitV l)
  | _ => None
  end.
Definition to_immediates (vl : list immediate) (el: list expr)
  : option (list immediate) :=
  foldl (λ acc e, vl ← acc; v ← to_immediate e; Some (vl ++ [v])) (Some vl) el.
Lemma to_immediate_Some e v :
  to_immediate e = Some v → of_val (ImmV v) = W.to_expr e.
Proof.
  revert v. induction e; intros; simplify_option_eq; auto using of_to_val.
Qed.
Lemma to_immediates_cons vl e el:
  to_immediates vl (e :: el) = v ← to_immediate e; to_immediates (vl ++ [v]) el.
Proof.
  rewrite /to_immediates /=. destruct (to_immediate e); simpl; [done|].
  by induction el.
Qed.
Lemma to_immediates_Some vl' el vl :
  to_immediates vl' el = Some vl →
  of_val (TValV vl) = bor_lang.TVal ((of_immediate <$> vl') ++ map to_expr el).
Proof.
  revert vl' vl. induction el as [|e el IH]; intros vl' vl.
  - rewrite /to_immediates /= => [[<-]]. by rewrite app_nil_r.
  - rewrite to_immediates_cons.
    destruct (to_immediate e) as [v|] eqn:Eq; [|done].
    move => /= /IH /= ->. f_equal.
    rewrite fmap_app -(to_immediate_Some _ _ Eq) /= -app_assoc //.
Qed.
Lemma to_immediates_Some'  el vl :
  to_immediates [] el = Some vl →
  of_val (TValV vl) = bor_lang.TVal (map to_expr el).
Proof. by move => /to_immediates_Some -> /=. Qed.

(* We define [to_val (ClosedExpr _)] to be [None] since [ClosedExpr]
constructors are only generated for closed expressions of which we know nothing
about apart from being closed. Notice that the reverse implication of
[to_val_Some] thus does not hold. *)
Definition to_val (e : expr) : option val :=
  match e with
  | Val v _ _ => Some v
  | Rec _ _ _ | Lit _ => ImmV <$> (to_immediate e)
  | Place l tag T => Some (PlaceV l tag T)
  | TVal el => vl ← to_immediates [] el; Some (TValV vl)
  | _ => None
  end.

Lemma to_val_Some e v :
  to_val e = Some v → of_val v = W.to_expr e.
Proof.
  revert v. induction e; intros; simplify_option_eq; auto using of_to_val.
  by apply to_immediates_Some'.
Qed.
Lemma to_val_is_Some e :
  is_Some (to_val e) → ∃ v, of_val v = to_expr e.
Proof. intros [v ?]; exists v; eauto using to_val_Some. Qed.
Lemma to_val_is_Some' e :
  is_Some (to_val e) → is_Some (bor_lang.to_val (to_expr e)).
Proof. intros [v ?]%to_val_is_Some. exists v. rewrite -to_of_val. by f_equal. Qed.

Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | Val v e H => Val v e H
  | ClosedExpr e => ClosedExpr e
  | Lit l => Lit l
  | Var y => if bool_decide (y = x) then es else Var y
  | Rec f xl e =>
    Rec f xl $ if bool_decide (BNamed x ≠ f ∧ BNamed x ∉ xl) then subst x es e else e
  | App e el => App (subst x es e) (map (subst x es) el)
  | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
  | TVal el => TVal (map (subst x es) el)
  | Proj e1 e2 => Proj (subst x es e1) (subst x es e2)
  | Conc e1 e2 => Conc (subst x es e1) (subst x es e2)
  | Place t tag T => Place t tag T
  | Deref e T mut => Deref (subst x es e) T mut
  | Ref e => Ref (subst x es e)
  | Field e path => Field (subst x es e) path
  | Copy e => Copy (subst x es e)
  | Write e1 e2 => Write (subst x es e1) (subst x es e2)
  | Alloc T => Alloc T
  | Free e => Free (subst x es e)
  | CAS e0 e1 e2 => CAS (subst x es e0) (subst x es e1) (subst x es e2)
  | AtomRead e => AtomRead (subst x es e)
  | AtomWrite e1 e2 => AtomWrite (subst x es e1) (subst x es e2)
  | NewCall => NewCall
  | EndCall e => EndCall (subst x es e)
  | Retag e kind => Retag (subst x es e) kind
  | Case e el => Case (subst x es e) (map (subst x es) el)
  | Fork e => Fork (subst x es e)
  end.
Lemma to_expr_subst x er e :
  to_expr (subst x er e) = bor_lang.subst x (to_expr er) (to_expr e).
Proof.
  revert e x er. fix FIX 1; destruct e=>/= ? er; repeat case_bool_decide;
    f_equal; eauto using is_closed_nil_subst, is_closed_to_val, eq_sym.
  - induction el=>//=. f_equal; auto.
  - induction el=>//=. f_equal; auto.
  - induction el=>//=. f_equal; auto.
Qed.

Definition is_atomic (e: expr) : bool :=
  match e with
  | AtomRead e | Free e => bool_decide (is_Some (to_val e))
  | AtomWrite e1 e2 =>
    bool_decide (is_Some (to_val e1) ∧ is_Some (to_val e2))
  | CAS e0 e1 e2 =>
    bool_decide (is_Some (to_val e0) ∧ is_Some (to_val e1) ∧ is_Some (to_val e2))
  | Alloc _ => true
  | _ => false
  end.
Lemma is_atomic_correct e : is_atomic e → Atomic WeaklyAtomic (to_expr e).
Proof.
  intros He. apply ectx_language_atomic.
  - intros σ e' σ' ef.
    destruct e; simpl; try done; repeat (case_match; try done);
    inversion 1; inversion BaseStep;
    try (apply val_irreducible; rewrite ?language.to_of_val; naive_solver eauto).
  - apply ectxi_language_sub_redexes_are_values=> /= Ki e' Hfill.
    revert He. destruct e; simpl; try done; repeat (case_match; try done);
    rewrite ?bool_decide_spec;
    destruct Ki; inversion Hfill; subst; clear Hfill;
    try naive_solver eauto using to_val_is_Some'.
Qed.
End W.

Ltac solve_closed :=
  match goal with
  | |- Closed ?X ?e =>
     let e' := W.of_expr e in change (Closed X (W.to_expr e'));
     apply W.is_closed_correct; vm_compute; exact I
  end.
Hint Extern 0 (Closed _ _) => solve_closed : typeclass_instances.

Ltac solve_into_val :=
  match goal with
  | |- IntoVal ?e ?v =>
     let e' := W.of_expr e in change (of_val v = W.to_expr e');
     apply W.to_val_Some; simpl; unfold W.to_expr;
     ((unlock; exact eq_refl) || (idtac; exact eq_refl))
  end.
Hint Extern 10 (IntoVal _ _) => solve_into_val : typeclass_instances.

Ltac solve_as_val :=
  match goal with
  | |- AsVal ?e =>
     let e' := W.of_expr e in change (∃ v, of_val v = W.to_expr e');
     apply W.to_val_is_Some, (bool_decide_unpack _); vm_compute; exact I
  end.
Hint Extern 10 (AsVal _) => solve_as_val : typeclass_instances.

Ltac solve_atomic :=
  match goal with
  | |- Atomic ?s ?e =>
     let e' := W.of_expr e in change (Atomic s (W.to_expr e'));
     apply W.is_atomic_correct; vm_compute; exact I
  end.
Hint Extern 0 (Atomic _ _) => solve_atomic : typeclass_instances.

(** Substitution *)
Ltac simpl_subst :=
  unfold subst_v; simpl;
  repeat match goal with
  | |- context [subst ?x ?er ?e] =>
      let er' := W.of_expr er in let e' := W.of_expr e in
      change (subst x er e) with (subst x (W.to_expr er') (W.to_expr e'));
      rewrite <-(W.to_expr_subst x); simpl (* ssr rewrite is slower *)
  end;
  unfold W.to_expr; simpl.
Arguments W.to_expr : simpl never.
Arguments subst : simpl never.

(* (** The tactic [inv_head_step] performs inversion on hypotheses of the
shape [head_step]. The tactic will discharge head-reductions starting
from values, and simplifies hypothesis related to conversions from and
to values, and finite map operations. This tactic is slightly ad-hoc
and tuned for proving our lifting lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : Lit _ = of_val ?v |- _ =>
    apply (f_equal (to_val)) in H; rewrite to_of_val in H;
    injection H; clear H; intro
  | H : context [to_val (of_val _)] |- _ => rewrite to_of_val in H
  | H : head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end. *)

(* (** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_val e tac :=
  let rec go e :=
  match e with
  | of_val ?v => v
  | Lit ?l => constr:(ImmV $ LitV l)
  | Rec ?f ?xl ?e => constr:(ImmV $ RecV f xl e)
  | Place ?l ?tag ?T => constr:(PlaceV l tag T)
  end in let v := go e in tac v.

Ltac reshape_expr e tac :=
  let rec go_fun K f vs es :=
    match es with
    | ?e :: ?es => reshape_val e ltac:(fun v => go_fun K f (v :: vs) es)
    | ?e :: ?es => go (AppRCtx f (reverse vs) es :: K) e
    end
  with go K e :=
  match e with
  | _ => tac K e
  | BinOp ?op ?e1 ?e2 =>
     reshape_val e1 ltac:(fun v1 => go (BinOpRCtx op v1 :: K) e2)
  | BinOp ?op ?e1 ?e2 => go (BinOpLCtx op e2 :: K) e1
  | App ?e ?el => reshape_val e ltac:(fun f => go_fun K f (@nil val) el)
  | App ?e ?el => go (AppLCtx el :: K) e
  | Copy ?e => go (CopyCtx :: K) e
  | Write ?e1 ?e2 =>
    reshape_val e1 ltac:(fun v1 => go (WriteRCtx v1 :: K) e2)
  | Write ?e1 ?e2 => go (WriteLCtx e2 :: K) e1
  | CAS ?e0 ?e1 ?e2 => reshape_val e0 ltac:(fun v0 => first
     [ reshape_val e1 ltac:(fun v1 => go (CasRCtx v0 v1 :: K) e2)
     | go (CasMCtx v0 e2 :: K) e1 ])
  | CAS ?e0 ?e1 ?e2 => go (CasLCtx e1 e2 :: K) e0
  | Free ?e => go (FreeCtx :: K) e
  | Deref ?e ?T ?mut => go (DerefCtx T mut :: K) e
  | Ref ?e => go (RefCtx :: K) e
  | Field ?e ?path => go (FieldCtx path :: K) e
  | EndCall ?e => go (EndCallCtx :: K) e
  | Retag ?e ?kind => go (RetagCtx kind :: K) e
  | Case ?e ?el => go (CaseCtx el :: K) e
  end
  in go (@nil ectx_item) e. *)
