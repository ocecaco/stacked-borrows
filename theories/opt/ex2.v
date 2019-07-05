From stbor.sim Require Import local invariant refl_step.

Set Default Proof Using "Type".

(* Assuming x : & i32 *)
Definition ex2 : function :=
  fun: ["i"],
    let: "x" := new_place (& int) &"i" in
    Retag "x" Default ;;
    Copy *{int} "x" ;;
    Call #[ScFnPtr "f"] ["x"] ;;
    Copy *{int} "x"
  .

Definition ex2_opt : function :=
  fun: ["i"],
    let: "x" := new_place (& int) &"i" in
    Retag "x" Default ;;
    Copy *{int} "x" ;;
    let: "v" := Copy *{int} "x" in
    Call #[ScFnPtr "f"] ["x"] ;;
    "v"
  .

Lemma ex2_sim_body fs ft : ⊨{fs,ft} ex2 ≥ᶠ ex2_opt.
Proof.
Abort.
