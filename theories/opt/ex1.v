From stbor.sim Require Import local invariant refl_step tactics body simple.

Set Default Proof Using "Type".

(** Moving read of mutable reference up across code not using that ref. *)

(* Assuming x : &mut i32 *)
Definition ex1 : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in (* put argument into place *)
    Retag "x" Default ;;
    Call #[ScFnPtr "f"] [] ;;
    *{int} "x" <- #[42] ;;
    Call #[ScFnPtr "g"] [] ;;
    Copy *{int} "x"
  .

Definition ex1_opt : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    Retag "x" Default ;;
    Call #[ScFnPtr "f"] [] ;;
    *{int} "x" <- #[42] ;;
    let: "v" := Copy *{int} "x" in
    Call #[ScFnPtr "g"] [] ;;
    "v"
  .

Lemma ex1_sim_body fs ft : ⊨ᶠ{fs,ft} ex1 ≥ ex1_opt.
Proof.
  apply (sim_fun_simple1 10)=>// rf es css et cs vs vt FREL ??. simplify_eq/=.
  (* InitCall *)
  apply sim_simple_init_call=> c /= {css}.
  (* Alloc *)
  sim_apply sim_simple_alloc_local=> l t /=.
  (* Let *)
  sim_apply sim_simple_let_place=>/=.
Abort.
