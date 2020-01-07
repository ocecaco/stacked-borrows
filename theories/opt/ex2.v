From stbor.sim Require Import local invariant refl tactics simple program
  refl_step right_step left_step viewshift derived_step.

Set Default Proof Using "Type".

(** Moving read of shared ref up across code that *may* use that ref. *)

(* Assuming x : & i32 *)
Definition ex2_unopt : function :=
  fun: ["i"],
    (* "x" is the local variable that stores the pointer value "i" *)
    let: "x" := new_place (& int) "i" in

    (* retag_place reborrows the pointer value stored in "x" (which is "i"),
      then updates "x" with the new pointer value. A [Default] retag is
      sufficient for this, we don't need the protector. *)
    retag_place "x" (RefPtr Immutable) int Default ;;

    (* The unknown code is represented by a call to an unknown function "f",
      which does take the pointer value from "x" as an argument. *)
    Call #[ScFnPtr "f"] [Copy "x"] ;;

    (* Read the value "v" from the cell pointed to by the pointer in "x" *)
    let: "v" := Copy *{int} "x" in

    (* Free the local variable *)
    Free "x" ;;

    (* Finally, return the read value *)
    "v"
  .

Definition ex2_opt : function :=
  fun: ["i"],
    let: "x" := new_place (& int) "i" in
    retag_place "x" (RefPtr Immutable) int Default ;;
    let: "v" := Copy *{int} "x" in
    Call #[ScFnPtr "f"] [Copy "x"] ;;
    Free "x" ;;
    "v"
  .

Lemma ex2_sim_body : ⊨ᶠ ex2_unopt ≥ ex2_opt.
Proof.
  apply (sim_fun_simple1 10)=>// fs ft rarg es et arg c LOOK AREL ??.
  simplify_eq/=.
  (* Alloc local *)
  sim_apply sim_simple_alloc_local=> l t /=.
  (* TODO: sim_apply's bind cannot disambiguate the right "let" *)
  sim_bind (let: _ := Place _ _ _ in _)%E (let: _ := Place _ _ _ in _)%E.
  sim_apply sim_simple_let=>/=.
  (* Write local *)
  sim_apply sim_simple_write_local; [solve_sim..|].
  intros sarg ->.
  sim_apply sim_simple_let=>/=.
  apply: sim_simple_result.
  (* Retag a local place *)
  sim_apply sim_simple_let=>/=.
  apply Forall2_cons_inv in AREL as [AREL _].
  (* We need to drop to complex mode, to preserve some local state info. *)
  intros σs σt.
  (* TODO: sim_apply's bind cannot disambiguate the right "let" *)
  sim_bind (let: _ := Place _ _ _ in _)%E (let: _ := Place _ _ _ in _)%E.
  sim_apply sim_body_let=>/=.
    (* Copy local place *)
    sim_apply sim_body_copy_local; [solve_sim..|].
    sim_apply sim_body_result => /= VALID.
    (* Retag *)
    sim_apply sim_body_retag_ref_default; [simpl; lia|done| |eauto|..].
    { eapply arel_mono; [done|..|exact AREL]. solve_res. } clear VALID.
    move=> l' told tnew hplt c' cids α' nxtp' r0 ? _ _ IS_i σs' σt' s_new
      tk ARELn /=. subst sarg.
    specialize (IS_i O ltac:(simpl; lia)). rewrite shift_loc_0_nat in IS_i.
    destruct IS_i as [(ss & st & IS_i & _) TOP].
    (* Write local *)
    sim_apply sim_body_write_local_1; [solve_sim..|].
    intros s ?. simplify_eq. simpl.
  sim_apply sim_body_let. simplify_eq/=.
  (* Copy local (right) *)
  sim_apply_r sim_body_copy_local_r; [solve_sim..|].
  apply: sim_body_result=>_/=.
  (* Copy public right *)
  sim_apply_r sim_body_deref_r=>/=.
  sim_apply_r sim_body_copy_public_r; [solve_sim..|].
  apply: sim_body_result=>_/=.
  apply: sim_body_let_r=>/=.
  (* Back to simple mode! *)
  eapply (sim_simplify (fun_post_simple c)). { by eauto. }
  simplify_eq/=.
  (* Copy local place *)
  sim_apply sim_simple_copy_local; [solve_sim..|].
  apply: sim_simple_result=>/=.
  (* Call *)
  rewrite (_: rarg ⋅ res_cs c ∅ ⋅ res_tag tnew tk hplt ⋅ r0 ⋅
                res_loc l [(ScPtr l' (Tagged tnew), ScPtr l' (Tagged tnew))] t
              ≡ rarg ⋅ res_cs c ∅ ⋅ res_tag tnew tk hplt ⋅ r0 ⋅
                res_loc l [(ScPtr l' (Tagged tnew), ScPtr l' (Tagged tnew))] t ⋅
                res_tag tnew tk hplt); last first.
  { rewrite {1}res_tag_public_dup cmra_assoc. solve_res. }
  sim_apply (sim_simple_call 5 [ValR [ScPtr l' (Tagged tnew)]]
                               [ValR [ScPtr l' (Tagged tnew)]]
              (res_tag tnew tkPub hplt)); [solve_sim..| |].
  { constructor; [|by constructor].
    constructor; [done|by constructor]. } clear ARELn.
  intros rf' frs' frt' ??? ? _ _ FREL'. simplify_eq/=.
  apply: sim_simple_result=>/=.
  sim_apply sim_simple_let=>/=. clear σs' σt' nxtp' α' TOP σs σt .
  (* Copy local (left). We drop to complex just because simple does not support this yet. *)
  intros σs σt.
  sim_apply_l sim_body_copy_local_l; [solve_sim..|].
  apply: sim_body_result=>_/=.
  (* Copy public (left) *)
  sim_apply_l sim_body_deref_l=>/=.
  sim_apply_l sim_body_copy_public_l; [try solve_sim..|].
  intros r' AREL'.
  apply: sim_body_result=>Hval/=.
  apply: sim_body_let_l=>/=.
  (* Free stuff *)
  eapply (sim_simplify (fun_post_simple c)). { by eauto. }
  sim_apply sim_simple_free_local_1; [solve_sim..|]. simpl.
  sim_apply sim_simple_let=>/=.
  (* Finishing up. *)
  apply: sim_simple_result. split.
  - solve_res.
  - constructor; simpl; auto.
    eapply arel_mono; [..|solve_res|exact AREL'].
    eapply cmra_valid_included; [exact Hval|].
    do 2 apply cmra_mono_r. solve_res.
Qed.

(** Top-level theorem: Two programs that only differ in the
"ex2" function are related. *)
Corollary ex2 (prog: fn_env) :
  stuck_decidable →
  prog_wf prog →
  let prog_src := <["ex2":=ex2_unopt]> prog in
  let prog_tgt := <["ex2":=ex2_opt]> prog in
  behave_prog prog_tgt <1= behave_prog prog_src.
Proof.
  intros Hdec Hwf. apply sim_prog_sim_classical.
  { apply Hdec. }
  { apply has_main_insert, Hwf; done. }
  apply sim_mod_funs_local.
  apply sim_mod_funs_insert; first done.
  - exact: ex2_sim_body.
  - exact: sim_mod_funs_refl.
Qed.

Print Assumptions ex2.
