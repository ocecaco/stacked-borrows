From stbor Require Import notation tactics.

(** Some common types *)
Notation int := (Scala 1).
Notation int_arr n := (Scala n).
Notation "'ᵗ&mut' T" := (Reference (RefPtr Mutable) T) (at level 10, format "ᵗ&mut  T").
Notation "'ᵗ&' T" := (Reference (RefPtr Immutable) T) (at level 10, format "ᵗ&  T").
Notation "'ᵗ*' T" := (Reference RawPtr T) (at level 10, format "ᵗ*  T").
Notation "'Box<' T '>'" := (Reference RawPtr T) (at level 10, format "Box< T >").


Notation "ᵛ& e" := (Ref e%E) (at level 9, format "ᵛ& e") : expr_scope.
Notation "ᵛ*{ T , N } e" := (Deref e%E T N) (at level 8, format "ᵛ*{ T ,  N }  e") : expr_scope.

Definition new_zero amod : val :=
  λ: [<>], let: "i" := Alloc int amod in "i" <- #0 ;; ᵛ&"i".
Definition new_mut_ref_int amod : val :=
  λ: ["v"],
    let: "x" := Alloc (ᵗ&mut int) amod in
      "x" <- "v" ;; "x".

Definition demo0 : val :=
  λ: ["x"],
  let: "y" := new_mut_ref_int Stack [ ᵛ& ᵛ*{int, Some Mutable} (!"x") ] in
  Retag "y" (ᵗ&mut int) Default ;;
  ᵛ*{int, Some Mutable} (!"y") <- #5 ;;
  ᵛ*{int, Some Mutable} (!"x") <- #3 ;;
  !(ᵛ*{int, Some Mutable} (!"y")).
