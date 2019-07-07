From stbor.sim Require Import local invariant refl_step.

Set Default Proof Using "Type".

(** Moving a write to a mutable reference down across unknown code. *)

(* Assuming x : &mut i32 *)
Definition ex3_down : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    Retag "x"  FnEntry ;;
    *{int} "x" <- #[42] ;;
    let: "v" := Call #[ScFnPtr "f"] [] in
    *{int} "x" <- #[13] ;;
    "v"
  .

Definition ex3_down_opt_1 : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    Retag "x"  FnEntry ;;
    let: "v" := Call #[ScFnPtr "f"] [] in
    *{int} "x" <- #[42] ;;
    *{int} "x" <- #[13] ;;
    "v"
  .

Definition ex3_down_opt_2 : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    Retag "x"  FnEntry ;;
    let: "v" := Call #[ScFnPtr "f"] [] in
    *{int} "x" <- #[13] ;;
    "v"
  .

Lemma ex3_down_sim_fun : ⊨ᶠ ex3_down ≥ ex3_down_opt_1.
Proof.
Abort.
