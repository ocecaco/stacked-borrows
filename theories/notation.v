From stbor Require Export lang.

Coercion App : expr >-> Funclass.
Coercion of_val : val >-> expr.

Coercion Var : string >-> expr.

Coercion BNamed : string >-> binder.
Notation "<>" := BAnon : lrust_binder_scope.

(** Lambda's arguments *)
Notation "[ ]" := (@nil expr) : expr_scope.
Notation "[ x ]" := (@cons expr x%E (@nil expr)) : expr_scope.
Notation "[ x1 ; x2 ; .. ; xn ]" :=
  (@cons expr x1%E (@cons expr x2%E
        (..(@cons expr xn%E (@nil expr))..))) : expr_scope.

(** Rvalues *)
Notation "#[ ]" := (TVal (@nil expr)) : expr_scope.
Notation "#[ x ]" := (TVal (@cons expr x%E (@nil expr))) : expr_scope.
Notation "#[ x1 ; x2 ; .. ; xn ]" :=
  (TVal (@cons expr x1%E (@cons expr x2%E
        (..(@cons expr xn%E (@nil expr))..)))) : expr_scope.

(* No scope for the values, does not conflict and scope is often not inferred
properly. *)
Notation "# l" := (ImmV (LitV l%Z%V%L)) (at level 8, format "# l").
Notation "# l" := (Lit l%Z%V%L) (at level 8, format "# l") : expr_scope.

(** Some common types *)
Notation int := (Scalar 1).
Notation int_arr n := (Scalar n).
Notation "'&mut' T" := (Reference (RefPtr Mutable) T%RustT)
  (at level 8, format "&mut  T") : lrust_type.
Notation "'&' T" := (Reference (RefPtr Immutable) T%RustT)
  (at level 8, format "&  T")  : lrust_type.
Notation "'*mut' T" := (Reference (RawPtr Mutable) T%RustT)
  (at level 8, format "*mut  T") : lrust_type.
Notation "'*const' T" := (Reference (RawPtr Immutable) T%RustT)
  (at level 8, format "*const  T") : lrust_type.
Notation "'Box<' T '>'" := (Reference RawPtr T%RustT)
  (at level 8, format "Box< T >") : lrust_type.

(** Pointer operations *)
Notation "& e" := (Ref e%E) (at level 8, format "& e") : expr_scope.
Notation "*{ T } e" := (Deref e%E T%RustT)
  (at level 9, format "*{ T }  e") : expr_scope.

Notation "'Copy1' e" := (Proj (Copy e%E) #0) (at level 10) : expr_scope.

(** Syntax inspired by Coq/Ocaml. Constructions with higher precedence come
    first. *)
Notation "'case:' e0 'of' el" := (Case e0%E el%E)
  (at level 102, e0, el at level 150) : expr_scope.
Notation "'if:' e1 'then' e2 'else' e3" := (If e1%E e2%E e3%E)
  (only parsing, at level 102, e1, e2, e3 at level 150) : expr_scope.
Notation "☠" := LitPoison : val_scope.

(* Notation "! e" := (Read e%E) (at level 9, format "! e") : expr_scope. *)

(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <- e2" := (Write e1%E e2%E)
  (at level 80) : expr_scope.

Notation "e1 + e2" := (BinOp AddOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "e1 - e2" := (BinOp SubOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "e1 ≤ e2" := (BinOp LeOp e1%E e2%E)
  (at level 70) : expr_scope.
Notation "e1 < e2" := (BinOp LtOp e1%E e2%E)
  (at level 70) : expr_scope.
Notation "e1 = e2" := (BinOp EqOp e1%E e2%E)
  (at level 70) : expr_scope.
Notation "e1 +ₗ e2" := (BinOp OffsetOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.

Notation "'rec:' f xl := e" := (Rec f%RustB xl%RustB e%E)
  (at level 102, f, xl at level 1, e at level 200) : expr_scope.
Notation "'rec:' f xl := e" := (locked (RecV f%RustB xl%RustB e%E))
  (at level 102, f, xl at level 1, e at level 200) : val_scope.

Notation "λ: xl , e" := (Lam xl%RustB e%E)
  (at level 102, xl at level 1, e at level 200) : expr_scope.
Notation "λ: xl , e" := (locked (LamV xl%RustB e%E))
  (at level 102, xl at level 1, e at level 200) : val_scope.

Notation "'let:' x := e1 'in' e2" :=
  ((Lam (@cons binder x%RustB nil) e2%E) (@cons expr e1%E nil))
  (at level 102, x at level 1, e1, e2 at level 150) : expr_scope.
Notation "e1 ;; e2" := (let: <> := e1 in e2)%E
  (at level 100, e2 at level 200, format "e1  ;;  e2") : expr_scope.
(* These are not actually values, but we want them to be pretty-printed. *)
Notation "'let:' x := e1 'in' e2" :=
  (LamV (@cons binder x%RustB nil) e2%E (@cons expr e1%E nil))
  (at level 102, x at level 1, e1, e2 at level 150) : val_scope.
Notation "e1 ;; e2" := (let: <> := e1 in e2)%V
  (at level 100, e2 at level 200, format "e1  ;;  e2") : val_scope.
