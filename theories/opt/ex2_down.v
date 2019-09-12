From stbor.sim Require Import local invariant refl_step.
From stbor.sim Require Import tactics simple program.
From stbor.sim Require Import refl_step right_step left_step viewshift.

Set Default Proof Using "Type".

(** Moving a read of a shared reference down across code that *may* use that ref. *)

(* Assuming x : & i32 *)
Definition ex2_down : function :=
  fun: ["i"],
    let: "x" := new_place (& int) "i" in
    retag_place "x" (RefPtr Immutable) int FnEntry ;;
    let: "v" := Copy *{int} "x" in
    Call #[ScFnPtr "f"] [Copy "x"] ;;
    Free "x" ;;
    "v"
  .

Definition ex2_down_opt : function :=
  fun: ["i"],
    let: "x" := new_place (& int) "i" in
    retag_place "x" (RefPtr Immutable) int FnEntry ;;
    Call #[ScFnPtr "f"] [Copy "x"] ;;
    let: "v" := Copy *{int} "x" in
    Free "x" ;;
    "v"
  .


Lemma ex2_down_sim_fun : ⊨ᶠ ex2_down ≥ ex2_down_opt.
Proof.
  apply (sim_fun_simple1 10)=>// fs ft rarg es et arg c LOOK AREL ??.
  simplify_eq/=.
  (* Alloc local *)
  sim_apply sim_simple_alloc_local=> l t /=.
  sim_apply sim_simple_let=>/=.
  (* Write local *)
  sim_apply sim_simple_write_local; [solve_sim..|].
  intros sarg ->.
  sim_apply sim_simple_let=>/=.
  apply: sim_simple_result.
  (* Retag a local place *)
  sim_apply sim_simple_let=>/=.
  apply Forall2_cons_inv in AREL as [AREL _].
  sim_apply sim_simple_let=>/=.
    (* Copy local place *)
    sim_apply sim_simple_copy_local; [solve_sim..|].
    apply sim_simple_valid_post.
    apply: sim_simple_result. simpl. intros VALID.
Abort.
