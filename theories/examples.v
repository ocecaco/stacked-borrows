From stbor Require Import notation tactics.

(** Some common types *)
Notation int := (Scala 1).
Notation int_arr n := (Scala n).
Notation "'!&mut' T" := (Reference (RefPtr Mutable) T) (at level 10, format "!&mut  T").
Notation "'!&' T" := (Reference (RefPtr Immutable) T) (at level 10, format "!&  T").
Notation "'!*' T" := (Reference RawPtr T) (at level 10, format "!*  T").
Notation "'Box<' T '>'" := (Reference RawPtr T) (at level 10, format "Box< T >").


Notation "@& e" := (Ref e%E) (at level 9, format "@& e") : expr_scope.
Notation "'@*' T '/' N e" := (Deref e%E T N) (at level 8, format "@* T / N  e") : expr_scope.

Definition new_zero amod : val :=
  λ: [<>], let: "i" := Alloc int amod in "i" <- #0 ;; @&"i".
Definition new_mut_ref_int amod : val :=
  λ: ["v"],
    let: "x" := Alloc (!&mut int) amod in
      "x" <- "v" ;; "x".

Definition demo0 : val :=
  λ: ["x"],
  let: "y" := new_mut_ref_int Stack [  @& (Deref (!"x") int (Some Mutable) ) ] in
  (Deref (!"y") int (Some Mutable) ) <- #5 ;;
  (Deref (!"x") int (Some Mutable) ) <- #5 ;;
  !(Deref (!"y") int (Some Mutable) ).