From stbor.sim Require Import local invariant refl_step.

Set Default Proof Using "Type".

(** Moving a write to a mutable reference up across unknown code. *)

(* TODO: check if Free is in the right place *)
(* Assuming x : &mut i32 *)
Definition ex3 : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    retag_place "x" (RefPtr Mutable) int FnEntry ;;
    *{int} "x" <- #[42] ;;
    let: "v" := Call #[ScFnPtr "f"] [] in
    *{int} "x" <- #[13] ;;
    Free "x" ;;
    "v"
  .

Definition ex3_opt_1 : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    retag_place "x" (RefPtr Mutable) int FnEntry ;;
    *{int} "x" <- #[42] ;;
    *{int} "x" <- #[13] ;;
    let: "v" := Call #[ScFnPtr "f"] [] in
    Free "x" ;;
    "v"
  .

Definition ex3_opt_2 : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    retag_place "x" (RefPtr Mutable) int FnEntry ;;
    *{int} "x" <- #[13] ;;
    let: "v" := Call #[ScFnPtr "f"] [] in
    Free "x" ;;
    "v"
  .

(* TODO: show refinement to be transitive *)
Lemma ex3_sim_fun : ⊨ᶠ ex3 ≥ ex3_opt_1.
Proof.
Abort.
