From stbor.sim Require Import local invariant refl.
From stbor.sim Require Import tactics simple program.
From stbor.sim Require Import refl_step right_step left_step derived_step viewshift.

Set Default Proof Using "Type".

(** Moving a read of a shared reference down across code that *may* use that ref. *)

(* Assuming x : & i32 *)
Definition ex2_down_unopt : function :=
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


Lemma ex2_down_sim_fun : ⊨ᶠ ex2_down_unopt ≥ ex2_down_opt.
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
    move=> l' told tnew hplt α' nxtp' r0 ? _ IS_i InD σs2 σt2 s_new tk ARELn /=.
    subst sarg.
    have IS_O := (IS_i O ltac:(simpl; lia)). rewrite shift_loc_0_nat in IS_O.
    destruct IS_O as [(ss & st & Eql' & Eqss & Eqst & ARELs) TOP].
    rewrite insert_empty.
    (* Write local *)
    sim_apply sim_body_write_local_1; [solve_sim..|].
    intros s ?. simplify_eq. simpl.
  sim_apply sim_body_let=>/=.
  (* Copy local left *)
  sim_apply_l sim_body_copy_local_l; [solve_sim..|].
  apply: sim_body_result=>_ /=.
  (* Copy unique left *)
  sim_apply_l sim_body_deref_l =>/=.
  sim_apply_l sim_body_copy_public_l; [solve_sim..|].
  move => r' ARELs'.
  apply: sim_body_result=>_/=.
  apply: sim_body_let_l=>/=.
  (* Copy local place *)
  sim_apply sim_body_copy_local; [solve_sim..|].
  apply: sim_body_result=>_/=.
  (* Call *)
  set r1 := rarg ⋅ res_cs σt.(snc) {[tnew := dom (gset loc) hplt]} ⋅
            res_tag tnew tk hplt ⋅ r0 ⋅
            res_loc (fresh_block σt.(shp), 0)
                    [(ScPtr l' (Tagged tnew), ScPtr l' (Tagged tnew))] σt.(snp) ⋅
            r'.
  rewrite (_: r1 ≡ r1 ⋅ res_tag tnew tk hplt); last first.
  { rewrite /r1 {1}res_tag_public_dup cmra_assoc. solve_res. }
  sim_bind (Call _ _) (Call _ _). (* TODO: sim_apply fails to instantiate evars *)
  apply (sim_body_step_over_call _ _ _ (res_tag tnew tkPub hplt) _ (ValR _)
              [ValR [ScPtr l' (Tagged tnew)]] [ValR [ScPtr l' (Tagged tnew)]]);
    [|done|].
  { constructor; [|by constructor].
    constructor; [done|by constructor]. } clear ARELn.
  move => rf' ? _ _ frs' frt' σs3 σt3 _ /= Eqs1 Eqs2 ? _ _. simplify_eq.
  exists 5%nat.
  apply: sim_body_result=>_ /=.
  sim_apply sim_body_let=>/=. clear frs' frt'.
  (* Copy local right *)
  sim_apply_r sim_body_copy_local_r; [|rewrite /r1|..]; [solve_sim..|].
  apply: sim_body_result=>_ /=.
  (* Copy protected right *)
  sim_apply_r sim_body_deref_r =>/=.
  sim_apply_r sim_body_copy_protected_r; [|rewrite /r1|..];
    [solve_sim..|by rewrite lookup_insert|by eapply elem_of_dom_2|].
  intros Eqss3 Eqst3.
  apply: sim_body_result=> Hval /=.
  apply: sim_body_let_r=>/=.
  (* Free stuff *)
  sim_apply sim_body_free_unique_local_1;
    [done|rewrite /r1 /res_loc /= insert_empty; solve_sim |by left|].
  move => _ _ α4 _ σs4 σt4.
  sim_apply sim_body_let=>/=.
  (* Remove protection *)
  set r2 := rarg ⋅ r0 ⋅ res_cs σt.(snc) {[tnew := dom (gset loc) hplt]} ⋅
              res_tag tnew tk hplt ⋅ r' ⋅ rf'.
  set r3 := rarg ⋅ r0 ⋅ res_cs σt.(snc) ∅ ⋅ res_tag tnew tk hplt ⋅ r' ⋅ rf'.
  rewrite (_: rarg ⋅ res_cs σt.(snc) {[tnew := dom (gset loc) hplt]} ⋅
              res_tag tnew tk hplt ⋅ r0 ⋅ r' ⋅ rf' ≡ r2); last first.
  { rewrite -2!cmra_assoc (cmra_comm r0) cmra_assoc (cmra_comm _ r0)
            !cmra_assoc (cmra_comm r0) //. }
  apply (viewshift_state_sim_local_body _ _ _ _ r2 r3).
  { rewrite /r2 /r3. do 3 apply viewshift_state_frame_r.
    rewrite -insert_empty. apply vs_state_drop_protector; [done|].
    move => l1 /InD [i [/= Lti ?]]. subst l1.
    destruct i; [|clear -Lti; by lia]. rewrite shift_loc_0_nat.
    move => ss4 /= /lookup_delete_Some [? Eqst4].
    rewrite Eqst4 in Eqst3. simplify_eq. exists ss.
    rewrite lookup_delete_ne; [|done]. split; [done|].
    move : ARELs. apply arel_mono; [|solve_res]. clear -Hval.
    apply (cmra_valid_included _ _ Hval).
    do 3 (etrans; [|apply cmra_included_l]).
    apply cmra_mono_r. solve_res. } clear Hval.
  (* Finishing up. *)
  apply: sim_body_result => Hval. split.
  - exists σt.(snc). split; [done|]. rewrite /end_call_sat.
    apply (cmap_lookup_op_unique_included (res_cs σt.(snc) ∅).(rcm));
      [apply Hval|apply prod_included; rewrite /r3; solve_res|..].
    by rewrite res_cs_lookup.
  - constructor; [|by constructor].
    move : ARELs. rewrite /r3. apply arel_mono; [done|solve_res].
Qed.

(** Top-level theorem: Two programs that only differ in the
"ex2_down" function are related. *)
Corollary ex2_down (prog: fn_env) :
  stuck_decidable →
  prog_wf prog →
  let prog_src := <["ex2_down":=ex2_down_unopt]> prog in
  let prog_tgt := <["ex2_down":=ex2_down_opt]> prog in
  behave_prog prog_tgt <1= behave_prog prog_src.
Proof.
  intros Hdec Hwf. apply sim_prog_sim_classical.
  { apply Hdec. }
  { apply has_main_insert, Hwf; done. }
  apply sim_mod_funs_local.
  apply sim_mod_funs_insert; first done.
  - exact: ex2_down_sim_fun.
  - exact: sim_mod_funs_refl.
Qed.

Print Assumptions ex2_down.
