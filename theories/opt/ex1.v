From stbor.sim Require Import local invariant refl tactics simple program.

Set Default Proof Using "Type".

(** Moving read of mutable reference up across code not using that ref. *)

(* Assuming x : &mut i32 *)
Definition ex1_unopt : function :=
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

Lemma ex1_sim_body :
  ⊨ᶠ ex1_unopt ≥ ex1_opt.
Proof.
  apply (sim_fun_simple1 10)=>// fs ft rarg es css et cs args argt LOOK AREL ??.
  simplify_eq/=.
  (* InitCall *)
  apply sim_simple_init_call=> c /= {css}.
  (* Alloc *)
  sim_apply sim_simple_alloc_local=> l t /=.
  sim_apply sim_simple_let_place=>/=.
  (* Write *)
  rewrite (vrel_eq _ _ _ AREL).
  sim_apply sim_simple_write_local; [done|solve_res|].
  intros arg ->. simpl.
  sim_apply sim_simple_let_val=>/=.
  apply sim_simple_place.
  (* Retag. *)
  sim_apply sim_simple_let_place=>/=.
  destruct args as [|args args']; first by inversion AREL.
  apply Forall2_cons_inv in AREL as [AREL ATAIL].
  destruct args' as [|]; last by inversion ATAIL. clear ATAIL.
  sim_apply sim_simple_retag_local; [solve_res|done|solve_res|].
  move=>l_i tg_i hplt /= Hl_i.
  (* Call *)
  sim_apply sim_simple_let_val=>/=.
  sim_apply (sim_simple_call 10 [] [] ε); [done|done|solve_res|].
  intros rf frs frt FREL.
  apply sim_simple_val.

Admitted.

(** Top-level theorem: Two programs that only differ in the
"ex1" function are related. *)
Corollary ex1 (prog: fn_env) :
  stuck_decidable →
  prog_wf prog →
  let prog_src := <["ex1":=ex1_unopt]> prog in
  let prog_tgt := <["ex1":=ex1_opt]> prog in
  behave_prog prog_tgt <1= behave_prog prog_src.
Proof.
  intros Hdec Hwf. apply sim_prog_sim_classical.
  { apply Hdec. }
  { apply has_main_insert, Hwf; done. }
  apply sim_mod_funs_local.
  apply sim_mod_funs_insert; first done.
  - exact: ex1_sim_body.
  - exact: sim_mod_funs_refl.
Qed.

Print Assumptions ex1.
