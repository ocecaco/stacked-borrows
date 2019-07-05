From stbor.sim Require Import local invariant refl_step.

Set Default Proof Using "Type".

(* Assuming x : &mut i32 *)
Definition ex1 : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) &"i" in
    Retag "x" Default ;;
    Call #[ScFnPtr "f"] [] ;;
    *{int} "x" <- #[42] ;;
    Call #[ScFnPtr "g"] [] ;;
    Copy *{int} "x"
  .

Definition ex1_opt : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) &"i" in
    Retag "x" Default ;;
    Call #[ScFnPtr "f"] [] ;;
    *{int} "x" <- #[42] ;;
    let: "v" := Copy *{int} "x" in
    Call #[ScFnPtr "g"] [] ;;
    "v"
  .

Lemma ex1_sim_body fs ft : ⊨{fs,ft} ex1 ≥ᶠ ex1_opt.
Proof.
Abort.
