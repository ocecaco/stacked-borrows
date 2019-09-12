From stbor.sim Require Import local invariant refl tactics simple program refl_step right_step left_step viewshift.

Set Default Proof Using "Type".

(** Moving read of mutable reference up across code not using that ref. *)

(* Assuming x : &mut i32 *)
Definition ex1_unopt : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in (* put argument into place *)
    retag_place "x" (RefPtr Mutable) int Default ;;
    Call #[ScFnPtr "f"] [] ;;
    *{int} "x" <- #[42] ;;
    Call #[ScFnPtr "g"] [] ;;
    let: "v" := Copy *{int} "x" in
    Free "x" ;;
    "v"
  .

Definition ex1_opt : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    retag_place "x" (RefPtr Mutable) int Default ;;
    Call #[ScFnPtr "f"] [] ;;
    *{int} "x" <- #[42] ;;
    let: "v" := Copy *{int} "x" in
    Call #[ScFnPtr "g"] [] ;;
    Free "x" ;;
    "v"
  .

Lemma ex1_sim_body :
  ⊨ᶠ ex1_unopt ≥ ex1_opt.
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
    (* Retag *)
    sim_apply sim_simple_retag_ref; [simpl; lia|done| |eauto|..].
    { eapply arel_mono; [done|..|exact AREL]. solve_res. } clear VALID.
    move=>l_i tg_i tg_n hplt /= ?? IS_i. subst sarg.
    specialize (IS_i O ltac:(lia)). rewrite shift_loc_0_nat in IS_i.
    (* Write local *)
    sim_apply sim_simple_write_local; [solve_sim..|].
    intros s ?. simplify_eq.
  (* Call *)
  sim_apply sim_simple_let=>/=.
  sim_apply (sim_simple_call 10 [] [] ε); [solve_sim..|].
  intros rf frs frt ??? ? _ _ FREL. simplify_eq/=.
  apply: sim_simple_result. simpl.
  sim_apply sim_simple_let=>/=.
  (* Copy local *)
  sim_apply sim_simple_copy_local; [solve_sim..|].
  apply: sim_simple_result. simpl.
  sim_apply sim_simple_deref=>l' t' ?. simplify_eq/=.
  (* Write unique. We need to drop to complex mode, to preserve some local state info. *)
  intros σs σt.
  sim_apply sim_body_write_unique_1; [solve_sim..|].
  intros ?? Htop. simplify_eq/=.
  sim_apply sim_body_let. simplify_eq/=.
  (* Copy local (right) *)
  sim_apply_r sim_body_copy_local_r; [solve_sim..|].
  apply: sim_body_result=>_. simpl.
  (* Copy unique (right) *)
  sim_apply_r sim_body_deref_r. simpl.
  sim_apply_r sim_body_copy_unique_r; [try solve_sim..|].
  { rewrite lookup_insert. done. }
  apply: sim_body_result=>_. simpl.
  apply: sim_body_let_r. simpl. (* FIXME: figure out why [sim_apply_r] does the wrong thing here *)
  (* We can go back to simple mode! *)
  eapply (sim_simplify (fun_post_simple c)). { by eauto. }
  simplify_eq/=. clear- AREL FREL LOOK.
  (* Call *)
  sim_apply (sim_simple_call 10 [] [] ε); [solve_sim..|].
  intros rf' frs' frt' ??? ? _ _ FREL'. simplify_eq/=.
  apply: sim_simple_result. simpl.
  sim_apply sim_simple_let=>/=.
  (* Copy local (left). We drop to complex just because simple does not support this yet. *)
  intros σs σt.
  sim_apply_l sim_body_copy_local_l; [solve_sim..|].
  apply: sim_body_result=>_. simpl.
  (* Copy unique (left) *)
  sim_apply_l sim_body_deref_l. simpl.
  sim_apply_l sim_body_copy_unique_l; [try solve_sim..|].
  { rewrite lookup_insert. done. }
  apply: sim_body_result=>Hval. simpl.
  apply: sim_body_let_l. simpl.
  (* Free stuff *)
  eapply (sim_simplify (fun_post_simple c)). { by eauto. }
  sim_apply sim_simple_free_local_1; [solve_sim..|]. simpl.
  sim_apply sim_simple_let=>/=.
  (* Finishing up. *)
  apply: sim_simple_result. split.
  - solve_res.
  - constructor; simpl; auto.
Qed.

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
