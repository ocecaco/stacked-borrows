From stbor.sim Require Import local invariant refl_step.

Set Default Proof Using "Type".

(** Moving a read of a shared reference down across code that *may* use that ref. *)

(* Assuming x : & i32 *)
Definition ex2_down : function :=
  fun: ["i"],
    let: "x" := new_place (& int) "i" in
    retag_place "x" (RefPtr Immutable) int FnEntry ;;
    let: "v" := Copy *{int} "x" in
    Call #[ScFnPtr "f"] ["x"] ;;
    Free "x" ;; Free "i" ;;
    "v"
    .

Definition ex2_down_opt : function :=
  fun: ["i"],
    let: "x" := new_place (& int) "i" in
    retag_place "x" (RefPtr Immutable) int FnEntry ;;
    Call #[ScFnPtr "f"] ["x"] ;;
    let: "v" := Copy *{int} "x" in
    Free "x" ;; Free "i" ;;
    "v"
    .


Lemma ex2_down_sim_fun : ⊨ᶠ ex2_down ≥ ex2_down_opt.
Proof.
Abort.
