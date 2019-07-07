From stbor.sim Require Import local invariant refl_step.

Set Default Proof Using "Type".

(** Moving a write to a mutable reference up across unknown code. *)

(* Assuming x : &mut i32 *)
Definition ex3 : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    Retag "x"  FnEntry ;;
    *{int} "x" <- #[42] ;;
    let: "v" := Call #[ScFnPtr "f"] [] in
    *{int} "x" <- #[13] ;;
    "v"
  .

Definition ex3_opt_1 : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    Retag "x"  FnEntry ;;
    *{int} "x" <- #[42] ;;
    *{int} "x" <- #[13] ;;
    Call #[ScFnPtr "f"] []
  .

Definition ex3_opt_2 : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    Retag "x"  FnEntry ;;
    *{int} "x" <- #[13] ;;
    Call #[ScFnPtr "f"] []
  .

Lemma ex3_sim_fun : ⊨ᶠ ex3 ≥ ex3_opt_1.
Proof.
Abort.
