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
  sim_apply sim_simple_let_place=>/=.
  (* Write *)
  rewrite (vrel_eq _ _ _ FREL).
  sim_apply sim_simple_write_local. solve_res.
  intros s ->. simpl.
  sim_apply sim_simple_let_val=>/=.
  apply sim_simple_place.
  (* Retag. *)
  sim_apply sim_simple_let_place=>/=.
  destruct vs as [|s' vs]; first by inversion FREL.
  apply Forall2_cons_inv in FREL as [FREL FTAIL].
  destruct vs as [|]; last by inversion FTAIL. clear FTAIL.
  sim_apply sim_simple_retag_local. solve_res. done. solve_res.
  move=>l_i tg_i hplt /= Hl_i.
  (* Call *)
  sim_apply sim_simple_let_val=>/=.
  
Abort.
