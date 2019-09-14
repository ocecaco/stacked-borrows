From stbor.sim Require Import local invariant refl.
From stbor.sim Require Import tactics simple program.
From stbor.sim Require Import refl_step right_step left_step derived_step viewshift.

Set Default Proof Using "Type".

(** Moving a write to a mutable reference down across unknown code. *)

(* Assuming x : &mut i32 *)
Definition ex3_down_unopt : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    retag_place "x" (RefPtr Mutable) int FnEntry ;;
    *{int} "x" <- #[42] ;;
    let: "v" := Call #[ScFnPtr "f"] [] in
    *{int} "x" <- #[13] ;;
    Free "x" ;;
    "v"
  .

Definition ex3_down_opt_1 : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    retag_place "x" (RefPtr Mutable) int FnEntry ;;
    let: "v" := Call #[ScFnPtr "f"] [] in
    *{int} "x" <- #[42] ;;
    *{int} "x" <- #[13] ;;
    Free "x" ;;
    "v"
  .

Definition ex3_down_opt_2 : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    retag_place "x" (RefPtr Mutable) int FnEntry ;;
    let: "v" := Call #[ScFnPtr "f"] [] in
    *{int} "x" <- #[13] ;;
    Free "x" ;;
    "v"
    .

Lemma ex3_down_1_sim_fun : ⊨ᶠ ex3_down_unopt ≥ ex3_down_opt_1.
Proof.
  (* We can't use sim_simple because we need to track our stack frame id *)
  intros fs ft LOOK rarg es et vls vlt σs σt FREL SUBSTs SUBSTt.
  (* Substitution *)
  move:(subst_l_is_Some_length _ _ _ _ SUBSTs) (subst_l_is_Some_length _ _ _ _ SUBSTt).
  rewrite /= => Hls Hlt.
  destruct vls as [|vs []]; [done| |done].
  destruct vlt as [|arg []]; [done| |done]. clear Hls Hlt.
  inversion FREL as [|???? VREL _].
  clear FREL. specialize (vrel_eq _ _ _ VREL)=>?.
  simplify_eq. simpl in SUBSTs, SUBSTt. simplify_eq/=.
  (* Init call *)
  exists 10%nat. apply sim_body_init_call=>/= Eqcs.
  (* Alloc local *)
  sim_apply sim_body_alloc_local => /=.
  sim_apply sim_body_let=>/=.
  (* Write local *)
  sim_apply sim_body_write_local_1; [solve_sim..|].
  intros sarg ? σs1 σt1. subst arg.
  sim_apply sim_body_let=>/=.
  apply: sim_body_result => _.
  (* Retag a local place *)
  sim_apply sim_body_let=>/=.
  apply Forall2_cons_inv in VREL as [AREL _].
  sim_apply sim_body_let=>/=.
    (* Copy local place *)
    sim_apply sim_body_copy_local; [solve_sim..|].
    sim_apply sim_body_result => /= VALID.
    (* Retag *)
    sim_apply sim_body_retag_ref_fn_entry; [simpl; lia|eauto| |done|..].
    { rewrite -cmra_assoc (cmra_comm (res_cs _ _)) cmra_assoc. eauto. }
    { eapply arel_mono; [done|..|exact AREL]. solve_res. } clear VALID.
    move=> l' told tnew hplt α' nxtp' r0 ? _ IS_i InD σs2 σt2 s_new tk _ /=.
    subst sarg.
    have IS_O := (IS_i O ltac:(simpl; lia)). rewrite shift_loc_0_nat in IS_O.
    destruct IS_O as [(ss & st & Eql' & Eqss & Eqst & ARELs) TOP].
    rewrite insert_empty.
    (* Write local *)
    sim_apply sim_body_write_local_1; [solve_sim..|].
    intros s ?. simplify_eq. simpl.
  sim_apply sim_body_let=>/=.
  (* Copy local (left) *)
  sim_apply_l sim_body_copy_local_l; [solve_sim..|].
  apply: sim_body_result=>_/=.
  (* Write protected left *)
  sim_apply_l sim_body_deref_l =>/=.
  sim_apply_l sim_body_write_non_ptr_protected_l;
    [solve_sim..|by rewrite lookup_insert|by eapply (elem_of_dom_2 _ _ _ Eql')|].
  move => Eqst2 σs2' rt'.
  apply: sim_body_result=>_ /=.
  sim_apply sim_body_let_l =>/=.
  (* Call *)
  rewrite -(right_id ε op (_ ⋅ rt')).
  sim_bind (Call _ _) (Call _ _). (* TODO: sim_apply fails to instantiate evars *)
  apply (sim_body_step_over_call _ _ _ ε _ (ValR _) [] []); [solve_sim..|].
  move => rf' ? _ _ frs' frt' σs3 σt3 VREL' /= Eqs1 Eqs2 ? _ _. simplify_eq.
  exists 5%nat.
  apply: sim_body_result=>_ /=.
  sim_apply sim_body_let=>/=.
  (* Copy local (right) *)
  sim_apply_r sim_body_copy_local_r; [solve_sim..|].
  apply: sim_body_result=>_/=.
  (* Write protected right *)
  sim_apply_r sim_body_deref_r =>/=. subst rt'.
  sim_apply_r sim_body_write_non_ptr_protected_r;
    [solve_sim..|by rewrite lookup_insert|by rewrite lookup_insert
    |by eapply (elem_of_dom_2 _ _ _ Eql')|].
  move => Eqss3 σt3' rt'.
  apply: sim_body_result=>_/=.
  sim_apply sim_body_let_r =>/=.
  (* Copy local place *)
  sim_apply sim_body_copy_local; [solve_sim..|].
  sim_apply sim_body_result => /= VALID.
  sim_bind (Deref _ _) (Deref _ _). (* TODO: sim_apply fails to instantiate evars *)
  apply (sim_body_deref _ _ _ _ (ValR _)).
  move => ?? Eq. symmetry in Eq. simplify_eq/=. subst rt'.
  (* Write unique of 13 *)
  sim_apply sim_body_write_unique_1;
    [done|solve_sim|rewrite lookup_insert;by eexists|..]; [solve_sim..|].
  move => σs4 σt4 TOP4 /=.
  sim_apply sim_body_let=>/=.
  (* Free stuff *)
  sim_apply sim_body_free_unique_local_1;
    [done|rewrite /res_loc /= insert_empty; solve_sim |by left|].
  move => _ _ α5 _ σs5 σt5.
  sim_apply sim_body_let=>/=.
  rewrite 2!insert_insert.
  (* Remove protection *)
  set rt' := res_tag tnew tkUnique (<[l':=(ScInt 13, ScInt 13)]> hplt).
  set r1 := rarg ⋅ res_cs σt.(snc) {[tnew := dom (gset loc) hplt]} ⋅ r0 ⋅ rf' ⋅ rt'.
  set r2 := rarg ⋅ res_cs σt.(snc) ∅ ⋅ r0 ⋅ rf' ⋅ rt'.
  apply (viewshift_state_sim_local_body _ _ _ _ r1 r2).
  { rewrite /r1 /r2. do 3 apply viewshift_state_frame_r.
    apply vs_state_drop_protector; [done|].
    move => l1 /InD [i [/= Lti ?]]. subst l1.
    destruct i; [|clear -Lti; by lia]. rewrite shift_loc_0_nat.
    move => ss5 /= /lookup_delete_Some [?].
    rewrite lookup_insert => ?. simplify_eq. exists (ScInt 13).
    rewrite lookup_delete_ne; [|done].
    by rewrite lookup_insert. }
  (* Finishing up. *)
  apply: sim_body_result => Hval. split.
  - exists σt.(snc). split; [done|]. rewrite /end_call_sat.
    apply (cmap_lookup_op_unique_included (res_cs σt.(snc) ∅).(rcm));
      [apply Hval|apply prod_included; rewrite /r2; solve_res|..].
    by rewrite res_cs_lookup.
  - move : VREL'. rewrite /r2. apply vrel_mono; [done|solve_res].
Qed.

(** Top-level theorem: Two programs that only differ in the
"ex3_down" function are related. *)
Corollary ex3_down_1 (prog: fn_env) :
  stuck_decidable →
  prog_wf prog →
  let prog_src := <["ex3_down":=ex3_down_unopt]> prog in
  let prog_tgt := <["ex3_down":=ex3_down_opt_1]> prog in
  behave_prog prog_tgt <1= behave_prog prog_src.
Proof.
  intros Hdec Hwf. apply sim_prog_sim_classical.
  { apply Hdec. }
  { apply has_main_insert, Hwf; done. }
  apply sim_mod_funs_local.
  apply sim_mod_funs_insert; first done.
  - exact: ex3_down_1_sim_fun.
  - exact: sim_mod_funs_refl.
Qed.

Print Assumptions ex3_down_1.
