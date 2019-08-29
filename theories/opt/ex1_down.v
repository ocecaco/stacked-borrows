From stbor.sim Require Import local invariant refl_step.

Set Default Proof Using "Type".

(** Moving a read of a mutable reference down across code that *may* use that ref. *)

(* Assuming x : &mut i32 *)
Definition ex1_down : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in (* put argument into place *)
    retag_place "x" (RefPtr Mutable) int FnEntry ;;
    let: "v" := Copy *{int} "x" in
    Call #[ScFnPtr "f"] [] ;;
    Free "x" ;; Free "i" ;;
    "v"
    .

Definition ex1_down_opt : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    retag_place "x" (RefPtr Mutable) int FnEntry ;;
    Call #[ScFnPtr "f"] [] ;;
    Free "x" ;; Free "i" ;;
    Copy *{int} "x"
    .


Lemma ex1_down_sim_fun : ⊨ᶠ ex1_down ≥ ex1_down_opt.
Proof.
Abort.
