From stbor.lang Require Import expr_semantics.

(** Substitution with a *map*, for the reflexivity proof. *)
Fixpoint subst_map (xs : gmap string result) (e : expr) : expr :=
  match e with
  | Var y => if xs !! y is Some v then of_result v else Var y
  | Val v => Val v
  (* | Rec f xl e =>
    Rec f xl $ if bool_decide (BNamed x ≠ f ∧ BNamed x ∉ xl) then subst_map xs e else e *)
  | Call e el => Call (subst_map xs e) (map (subst_map xs) el)
  | InitCall e => InitCall (subst_map xs e)
  | EndCall e => EndCall (subst_map xs e)
  | Place l tag T => Place l tag T
  (* | App e1 el => App (subst_map xs e1) (map (subst_map xs) el) *)
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
        (subst_map (if x1 is BNamed s then delete s xs else xs) e2)
  | Case e el => Case (subst_map xs e) (map (subst_map xs) el)
  end.
