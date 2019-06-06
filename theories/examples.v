From stbor Require Import lang.

(* Allocate a place of type [T] and initialize it with a value [v] *)
Definition new_place T (v: expr) : expr :=
   let: "x" := Alloc T in "x" <- v ;; "x".

(* UB *)
(* from https://www.ralfj.de/blog/2018/11/16/stacked-borrows-implementation.html *)
Definition demo0 : expr :=
  (* let x = &mut 1u8; *)
  let: "i" := new_place int #1 in
  let: "x" := new_place (&mut int) &"i" in
  (* stack of i   : [Uniq(?)], not frozen *)
  (* stack of x   : [Uniq(x)], not frozen *)
  (* x uses Alias(None) for i *)

  (* retag x with new borrow *)
  Retag "x" Default #0 ;;
  (* stack of i: [Uniq(0); Uniq(?)], not frozen *)
  (* x now uses Uniq(0) for i *)

  (* let y = &mut *x; *)
  (* mut reference y created by dereferencing mut reference x *)
  let: "y" := new_place (&mut int) & *{int} (Copy1 "x") in
  (* Check read  x   with Uniq(x): OK! *)
  (* Check deref int with Uniq(0): OK! *)
  (* stack of y  : [Uniq(y)], not frozen *)

  (* retag y with new borrow *)
  Retag "y" Default #0 ;;
  (* stack of i: [Uniq(1); Uniq(0); Uniq(?)], not frozen *)
  (* y now uses Uniq(1) for i *)

  (* *y = 5; *)
  *{int} (Copy1 "y") <- #[ #5 ] ;;
  (* Check read  y with Uniq(y): OK! *)
  (* Check deref i with Uniq(1): OK! because Uniq(1) in on the stack *)
  (* Check write i with Uniq(1): OK! *)
  (* stack of int: [Uniq(1); Uniq(0); Uniq(?)], not frozen *)

  (* *x = 3; *)
  *{int} (Copy1 "x") <- #[ #3 ] ;;
  (* Check read  x with Uniq(x): OK! *)
  (* Check deref i with Uniq(0): OK! because Uniq(0) in on the stack *)
  (* Check write i with Uniq(0): OK! but pop Uniq(1) to reactivate Uniq(0) *)
  (* stack of i: [Uniq(0); Uniq(?)], not frozen *)

  (* let _val = *y; *)
  Copy *{int} (Copy1 "y") ;;
  (* Check read  y with Uniq(y): OK! *)
  (* Check deref i with Uniq(1): UB! Uniq(1) not on stack of i! *)
  (* Check read  i with Uniq(1): UNREACHABLE *)

  (* UNREACHABLE *)
  Free "i" ;;
  Free "x" ;;
  Free "y"
  .

(* DB *)
Definition demo1 : expr :=
  (* let x = &mut 1u8; *)
  let: "i" := new_place int #1 in
  let: "x" := new_place (&mut int) &"i" in
  (* stack of i : [Uniq(?)], not frozen *)
  (* stack of x : [Uniq(x)], not frozen *)
  (* x uses Alias(None) for i *)

  (* retag x with new borrow *)
  Retag "x" Default #☠ ;;
  (* stack of i: [Uniq(0); Uniq(?)], not frozen *)
  (* x now uses Uniq(0) for i *)

  (* let y1 = & *x; *)
  (* immut reference y1 created by dereferencing mut reference x *)
  let: "y1" := new_place (& int) & *{int} (Copy1 "x") in
  (* Check read  x with Uniq(x): OK! *)
  (* Check deref i with Uniq(0): OK! *)
  (* stack of y1 : [Uniq(y1)], not frozen *)

  (* retag y1 with new borrow *)
  Retag "y1" Default #☠ ;;
  (* stack of i: [Raw; Uniq(0); Uniq(?)], frozen_since(1) *)
  (* y1 now uses Alias(1) for i *)

  (* let _val = *x; *)
  Copy *{int} (Copy1 "x") ;;
  (* Check read  x with Uniq(x): OK! *)
  (* Check deref i with Uniq(0): OK! because Uniq(0) is on the stack *)
  (* Check read  i with Uniq(0): OK! because the stack is frozen *)
  (* stack of i: [Raw; Uniq(0); Uniq(?)], frozen_since(1) *)

  (* immut reference y2 created by dereferencing mut reference x *)
  (* let y2 = & *x; *)
  let: "y2" := new_place (& int) & *{int} (Copy1 "x") in
  (* Check read  x with Uniq(x): OK! *)
  (* Check deref i with Uniq(0): OK! *)
  (* stack of y2 : [Uniq(y2)], not frozen *)

  (* retag y2 with new borrow *)
  Retag "y2" Default #☠ ;;
  (* stack of i: [Raw; Uniq(0); Uniq(?)], frozen_since(1) *)
  (* y2 now uses Alias(2) for i *)

  (* let _val = *y1; *)
  Copy *{int} (Copy1 "y1") ;;
  (* Check read  y1 with Uniq(y1): OK! *)
  (* Check deref y1 with Alias(1): OK! because the stack is frozen_since(1) *)
  (* Check read  i  with Alias(1): OK! because the stack is frozen *)

  (* let _val = *y2; *)
  Copy *{int} (Copy1 "y2") ;;
  (* Check read  y2 with Uniq(y2): OK! *)
  (* Check deref y2 with Alias(2): OK! because the stack is frozen_since(1) *)
  (* Check read  i  with Alias(2): OK! because the stack is frozen *)

  Free "y2" ;;
  Free "y1" ;;
  Free "x" ;;
  Free "i"
  .

(* UB *)
Definition demo2 : expr :=
  (* let x = &mut 1u8; *)
  let: "i" := new_place int #1 in
  let: "x" := new_place (&mut int) &"i" in
  (* stack of i : [Uniq(?)], not frozen *)
  (* stack of x : [Uniq(x)], not frozen *)
  (* x uses Alias(None) for the int *)

  (* retag x with new borrow *)
  Retag "x" Default #☠ ;;
  (* stack of iint: [Uniq(0); Uniq(?)], not frozen *)
  (* x now uses Uniq(0) for i *)

  (* immut reference y created by dereferencing mut reference x *)
  (* let y = & *x; *)
  let: "y" := new_place (& int) & *{int} (Copy1 "x") in
  (* Check read  x with Uniq(x): OK! *)
  (* Check deref i with Uniq(0): OK! *)
  (* stack of y : [Uniq(y)], not frozen *)

  (* retag y with new borrow *)
  Retag "y" Default #☠ ;;
  (* stack of i: [Raw; Uniq(0); Uniq(?)], frozen_since(1) *)
  (* y now uses Alias(1) for i *)

  (* raw pointer z created by dereferencing x as raw pointer immutably then
     mutably. *)
  (* let z = x as *const u8 as *mut u8; *)
  let: "z" := new_place ( *mut int ) & *{int} & *{int} (Copy1 "x") in
  (* Check read  x with Uniq(x): OK! *)
  (* Check deref i with Uniq(0): OK! because Uniq(0) is on the stack and
                                       raw derefs are not checked. *)
  (* stack of z : [Uniq(z)], not frozen *)

  (* retag z with new borrow *)
  Retag "z" RawRt #☠ ;;
  (* stack of i: [Raw; Uniq(0); Uniq(?)], frozen_since(1) *)
  (* z now uses Alias(None) for the int *)

  *{int} (Copy1 "z") <- #[ #3 ] ;;
  (* Check read  z   with Uniq(z)    : OK! *)
  (* Check deref int with Alias(None): OK! because raw derefs are not checked. *)
  (* Check write int with Alias(None): OK! because there matches a Raw.
                                           Furthermore, the stack is unfrozen. *)
  (* stack of int: [Raw; Uniq(0); Uniq(?)], not frozen *)

  Copy *{int} (Copy1 "y") ;;
  (* Check read  y with Uniq(y) : OK! *)
  (* Check deref i with Alias(1): UB! because the stack is not frozen with a
                                  timestamp less than or equal to the tag.
                                  The type int doesn't contain UnsafeCell. *)
  (* Check read  i with Alias(1): UNREACHABLE *)

  (* UNREACHABLE *)
  Free "y" ;;
  Free "z" ;;
  Free "x" ;;
  Free "i"
  .

(* UB *)
Definition demo4 : expr :=
  (*  let x = &mut 1u8; *)
  let: "i" := new_place int #1 in
  let: "x" := new_place (&mut int) &"i" in
  (* stack of i : [Uniq(?)], not frozen *)
  (* stack of x : [Uniq(x)], not frozen *)
  (* x uses Alias(None) for i *)

  (* retag x with new borrow *)
  Retag "x" Default #☠ ;;
  (* stack of int: [Uniq(0); Uniq(?)], not frozen *)
  (* x now uses Uniq(0) for i *)

  (* raw pointer y1 created from x *)
  (*  let y1 = x as *mut u8; *)
  let: "y1" := new_place ( *mut int) & *{int} (Copy1 "x") in
  (* Check read  x with Uniq(x): OK! *)
  (* Check deref i with Uniq(0): OK! *)
  (* stack of y1 : [Uniq(y1)], not frozen *)

  (* retag y with new borrow *)
  Retag "y1" RawRt #☠ ;;
  (* stack of i: [Raw; Uniq(0); Uniq(?)], not frozen *)
  (* y1 now uses Alias(None) for i *)

  (* raw pointer y2 created from y1. *)
  (*  let y2 = y1; *)
  let: "y2" := new_place ( *mut int) & *{int} (Copy1 "y1") in
  (* Check read  y1 with Uniq(y1)   : OK! *)
  (* Check deref i  with Alias(None): OK! because Raw is on the stack. *)
  (* stack of y2  : [Uniq(y2)], not frozen *)

  (* retag y2 with new borrow *)
  Retag "y2" RawRt #☠ ;;
  (* stack of i : [Raw; Uniq(0); Uniq(?)], not frozen *)
  (* y2 now uses Alias(None) for i *)

  (*  *y1 = 3;
      *y2 = 5;
      *y2 = *y1; *)
  *{int} (Copy1 "y1") <- #[ #3 ] ;;
  *{int} (Copy1 "y2") <- #[ #5 ];;
  *{int} (Copy1 "y2") <- Copy *{int} (Copy1 "y1") ;;
  (* Checks for deref/read/write of y1 and y2 all pass because:
     * raw derefs are not checked
     * read/write are ok because Raw is on top of the stack, and nothing changes. *)
  (* stack of i: [Raw; Uniq(0); Uniq(?)], not frozen *)

  (*  *x = 7; *)
  *{int} (Copy1 "x") <- #7 ;;
  (* Check read  x   with Uniq(x): OK! *)
  (* Check deref int with Uniq(0): OK! because Uniq(0) is on the stack *)
  (* Check write int with Uniq(0): OK! because Uniq(0) is on the stack *)
  (* stack of i: [Uniq(0); Uniq(?)], not frozen *)

  (*  let _val = unsafe { *y1 }; *)
  Copy *{int} (Copy1 "y1") ;;
  (* Check read  y1  with Uniq(y1)   : OK! *)
  (* Check deref int with Alias(None): UB! because Raw is not on the unfrozen stack *)
  (* Check read  int with Alias(None): UNREACHABLE *)

  (* UNREACHABLE *)
  Free "y1" ;;
  Free "y2" ;;
  Free "x" ;;
  Free "i"
  .
