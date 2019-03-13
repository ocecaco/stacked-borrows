From stbor Require Import notation tactics.

(** Some common types *)
Notation int := (Scala 1).
Notation int_arr n := (Scala n).
Notation "'ᵗ&mut' T" := (Reference (RefPtr Mutable) T)
  (at level 10, format "ᵗ&mut  T").
Notation "'ᵗ&' T" := (Reference (RefPtr Immutable) T)
  (at level 10, format "ᵗ&  T").
Notation "'ᵗ*' T" := (Reference RawPtr T) (at level 10, format "ᵗ*  T").
Notation "'Box<' T '>'" := (Reference RawPtr T) (at level 10, format "Box< T >").


Notation "ᵛ& e" := (Ref e%E) (at level 9, format "ᵛ& e") : expr_scope.
Notation "ᵛ*mut{ T } e" := (Deref e%E T (Some Mutable))
  (at level 8, format "ᵛ*mut{ T }  e") : expr_scope.
Notation "ᵛ*imm{ T } e" := (Deref e%E T (Some Immutable))
  (at level 8, format "ᵛ*imm{ T }  e") : expr_scope.
Notation "ᵛ*raw{ T } e" := (Deref e%E T None)
  (at level 8, format "ᵛ*raw{ T }  e") : expr_scope.

(* These two are supposed to be inlined, so they don't contribute to creating
  call ids or retagging. *)
Definition new_int (i: Z) amod : val :=
  λ: [<>], let: "i" := Alloc int amod in "i" <- #i ;; ᵛ&"i".
Definition new_pointer_int T amod : val :=
  λ: ["v"],
    let: "x" := Alloc T amod in
      "x" <- "v" ;; "x".

(* UB *)
(* from https://www.ralfj.de/blog/2018/11/16/stacked-borrows-implementation.html *)
Definition demo0 : val :=
  λ: [<>],
  (* let x = &mut 1u8; *)
  let: "x" := new_pointer_int (ᵗ&mut int) Stack [new_int 1 Heap] in
  (* stack of int: [Raw], not frozen *)
  (* stack of x  : [Uniq(x)], not frozen *)
  (* x uses Alias(None) for the int *)

  (* retag x with new borrow *)
  Retag "x" (ᵗ&mut int) Default ;;
  (* stack of int: [Uniq(0); Raw], not frozen *)
  (* x now uses Uniq(0) for the int *)

  (* mut reference y created by dereferencing mut reference x *)
  (* let y = &mut *x; *)
  let: "y" := new_pointer_int (ᵗ&mut int) Stack [ ᵛ& ᵛ*mut{int} (!"x") ] in
  (* Check read  x   with Uniq(x): OK! *)
  (* Check deref int with Uniq(0): OK! *)
  (* stack of y  : [Uniq(y)], not frozen *)

  (* retag y with new borrow *)
  Retag "y" (ᵗ&mut int) Default ;;
  (* stack of int: [Uniq(1); Uniq(0); Raw], not frozen *)
  (* y now uses Uniq(1) for the int *)

  ᵛ*mut{int} (!"y") <- #5 ;;
  (* Check read  y   with Uniq(y): OK! *)
  (* Check deref int with Uniq(1): OK! because Uniq(1) in on the stack *)
  (* Check write int with Uniq(1): OK! *)
  (* stack of int: [Uniq(1); Uniq(0); Raw], not frozen *)

  ᵛ*mut{int} (!"x") <- #3 ;;
  (* Check read  x   with Uniq(x): OK! *)
  (* Check deref int with Uniq(0): OK! because Uniq(0) in on the stack *)
  (* Check write int with Uniq(0): OK! but pop Uniq(1) to reactivate Uniq(0) *)
  (* stack of int: [Uniq(0); Raw], not frozen *)


  !ᵛ*mut{int} (!"y")
  (* Check read  y   with Uniq(y): OK! *)
  (* Check deref int with Uniq(1): UB! Uniq(1) not on stack of int! *)
  (* Check read  int with Uniq(1): unreachable *)
  .

(* DB *)
Definition demo1 : val :=
  λ: [<>],
  (* let x = &mut 1u8; *)
  let: "x" := new_pointer_int (ᵗ&mut int) Stack [new_int 1 Heap] in
  (* stack of int: [Raw], not frozen *)
  (* stack of x  : [Uniq(x)], not frozen *)
  (* x uses Alias(None) for the int *)

  (* retag x with new borrow *)
  Retag "x" (ᵗ&mut int) Default ;;
  (* stack of int: [Uniq(0); Raw], not frozen *)
  (* x now uses Uniq(0) for the int *)

  (* immut reference y1 created by dereferencing mut reference x *)
  (* let y1 = & *x; *)
  let: "y1" := new_pointer_int (ᵗ& int) Stack [ ᵛ& ᵛ*mut{int} (!"x") ] in
  (* Check read  x   with Uniq(x): OK! *)
  (* Check deref int with Uniq(0): OK! *)
  (* stack of y1  : [Uniq(y1)], not frozen *)

  (* retag y1 with new borrow *)
  Retag "y1" (ᵗ& int) Default ;;
  (* stack of int: [Raw; Uniq(0); Raw], frozen_since(1) *)
  (* y1 now uses Alias(1) for the int *)

  !ᵛ*mut{int} (!"x") ;;
  (* Check read  x   with Uniq(x): OK! *)
  (* Check deref int with Uniq(0): OK! because Uniq(0) is on the stack *)
  (* Check read  int with Uniq(0): OK! because the stack is frozen *)
  (* stack of int: [Raw; Uniq(0); Raw], frozen_since(1) *)

  (* immut reference y2 created by dereferencing mut reference x *)
  (* let y2 = & *x; *)
  let: "y2" := new_pointer_int (ᵗ& int) Stack [ ᵛ& ᵛ*mut{int} (!"x") ] in
  (* Check read  x   with Uniq(x): OK! *)
  (* Check deref int with Uniq(0): OK! *)
  (* stack of y2  : [Uniq(y2)], not frozen *)

  (* retag y2 with new borrow *)
  Retag "y2" (ᵗ& int) Default ;;
  (* stack of int: [Raw; Uniq(0); Raw], frozen_since(1) *)
  (* y2 now uses Alias(2) for the int *)

  !ᵛ*imm{int} (!"y1") ;;
  (* Check read  y1  with Uniq(y1): OK! *)
  (* Check deref y1  with Alias(1): OK! because the stack is frozen_since(1) *)
  (* Check read  int with Alias(1): OK! because the stack is frozen *)

  !ᵛ*imm{int} (!"y2")
  (* Check read  y2  with Uniq(y2): OK! *)
  (* Check deref y2  with Alias(2): OK! because the stack is frozen_since(1) *)
  (* Check read  int with Alias(2): OK! because the stack is frozen *)
  .

(* UB *)
Definition demo2 : val :=
  λ: [<>],
  (* let x = &mut 1u8; *)
  let: "x" := new_pointer_int (ᵗ&mut int) Stack [new_int 1 Heap] in
  (* stack of int: [Raw], not frozen *)
  (* stack of x  : [Uniq(x)], not frozen *)
  (* x uses Alias(None) for the int *)

  (* retag x with new borrow *)
  Retag "x" (ᵗ&mut int) Default ;;
  (* stack of int: [Uniq(0); Raw], not frozen *)
  (* x now uses Uniq(0) for the int *)

  (* immut reference y created by dereferencing mut reference x *)
  (* let y = & *x; *)
  let: "y" := new_pointer_int (ᵗ& int) Stack [ ᵛ& ᵛ*mut{int} (!"x") ] in
  (* Check read  x   with Uniq(x): OK! *)
  (* Check deref int with Uniq(0): OK! *)
  (* stack of y  : [Uniq(y)], not frozen *)

  (* retag y with new borrow *)
  Retag "y" (ᵗ& int) Default ;;
  (* stack of int: [Raw; Uniq(0); Raw], frozen_since(1) *)
  (* y now uses Alias(1) for the int *)

  (* raw pointer z created by dereferencing x as raw pointer immutably then
     mutably. *)
  (* let z = x as *const u8 as *mut u8; *)
  let: "z" := new_pointer_int (ᵗ* int) Stack [ ᵛ& ᵛ*raw{int} ᵛ& ᵛ*imm{int} (!"x") ] in
  (* Check read  x   with Uniq(x): OK! *)
  (* Check deref int with Uniq(0): OK! because Uniq(0) is on the stack and
                                       raw derefs are not checked. *)
  (* stack of z  : [Uniq(z)], not frozen *)

  (* retag z with new borrow *)
  Retag "z" (ᵗ* int) RawRt ;;
  (* stack of int: [Raw; Uniq(0); Raw], frozen_since(1) *)
  (* z now uses Alias(None) for the int *)

  ᵛ*raw{int} (!"z") <- #3 ;;
  (* Check read  z   with Uniq(z)    : OK! *)
  (* Check deref int with Alias(None): OK! because raw derefs are not checked. *)
  (* Check write int with Alias(None): OK! because there matches a Raw.
                                           Furthermore, the stack is unfrozen. *)
  (* stack of int: [Raw; Uniq(0); Raw], not frozen *)

  !ᵛ*imm{int} (!"y")
  (* Check read  y   with Uniq(y) : OK! *)
  (* Check deref int with Alias(1): UB! because the stack is not frozen with a
                                    timestamp less than or equal to the tag.
                                    The type int doesn't contain UnsafeCell. *)
  (* Check read  int with Alias(1): unreachable *)
  .

(* UB *)
Definition demo4 : val :=
  λ: [<>],
  (* let x = &mut 1u8; *)
  let: "x" := new_pointer_int (ᵗ&mut int) Stack [new_int 1 Heap] in
  (* stack of int: [Raw], not frozen *)
  (* stack of x  : [Uniq(x)], not frozen *)
  (* x uses Alias(None) for the int *)

  (* retag x with new borrow *)
  Retag "x" (ᵗ&mut int) Default ;;
  (* stack of int: [Uniq(0); Raw], not frozen *)
  (* x now uses Uniq(0) for the int *)

  (* raw pointer y1 created from x *)
  (* let y1 = x as *mut u8; *)
  let: "y1" := new_pointer_int (ᵗ* int) Stack [ᵛ& ᵛ*mut{int} (!"x")] in
  (* Check read  x   with Uniq(x): OK! *)
  (* Check deref int with Uniq(0): OK! *)
  (* stack of y1 : [Uniq(y1)], not frozen *)

  (* retag y with new borrow *)
  Retag "y1" (ᵗ* int) RawRt ;;
  (* stack of int: [Raw; Uniq(0); Raw], not frozen *)
  (* y1 now uses Alias(None) for the int *)

  (* raw pointer y2 created from y1. *)
  (* let y2 = y1; *)
  let: "y2" := new_pointer_int (ᵗ* int) Stack [ ᵛ& ᵛ*raw{int} (!"y1") ] in
  (* Check read  y1  with Uniq(y1)   : OK! *)
  (* Check deref int with Alias(None): OK! because Raw is on the stack. *)
  (* stack of y2  : [Uniq(y2)], not frozen *)

  (* retag y2 with new borrow *)
  Retag "y2" (ᵗ* int) RawRt ;;
  (* stack of int: [Raw; Uniq(0); Raw], not frozen *)
  (* y2 now uses Alias(None) for the int *)

  ᵛ*raw{int} (!"y1") <- #3 ;;
  ᵛ*raw{int} (!"y2") <- #5 ;;
  ᵛ*raw{int} (!"y2") <- ! ᵛ*raw{int} (!"y1") ;;
  (* Checks for deref/read/write of y1 and y2 all pass because:
     * raw derefs are not checked
     * read/write are ok because Raw is on top of the stack, and nothing changes. *)
  (* stack of int: [Raw; Uniq(0); Raw], not frozen *)

  ᵛ*mut{int} (!"x") <- #7 ;;
  (* Check read  x   with Uniq(x): OK! *)
  (* Check deref int with Uniq(0): OK! because Uniq(0) is on the stack *)
  (* Check write int with Uniq(0): OK! because Uniq(0) is on the stack *)
  (* stack of int: [Uniq(0); Raw], not frozen *)

  !ᵛ*raw{int} (!"y1")
  (* Check read  y1  with Uniq(y1)   : OK! *)
  (* Check deref int with Alias(None): OK! because Raw is on the stack *)
  (* Check read  int with Alias(None): OK! because Raw is on the stack *)
  (* stack of int: [Raw], not frozen *)
  (* TODO: so why is this UB?!? The example in the blog post assumes the stack
     to be [Uniq(0)], but here we are with [Uniq(0); Raw], due to the
     initialization of the stack for heap locations *)
  .