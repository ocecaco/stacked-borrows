From stbor.sim Require Import local invariant refl_step.
From stbor.sim Require Import tactics simple program.
From stbor.sim Require Import refl_step right_step left_step derived_step viewshift.

Set Default Proof Using "Type".

(** Moving a read of a mutable reference down across code that *may* use that ref. *)

(* Assuming x : &mut i32 *)
Definition ex1_down : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in (* put argument into place *)
    retag_place "x" (RefPtr Mutable) int FnEntry ;;
    let: "v" := Copy *{int} "x" in
    Call #[ScFnPtr "f"] [] ;;
    Free "x" ;;
    "v"
  .

Definition ex1_down_opt : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    retag_place "x" (RefPtr Mutable) int FnEntry ;;
    Call #[ScFnPtr "f"] [] ;;
    let: "v" := Copy *{int} "x" in
    Free "x" ;;
    "v"
  .

Lemma ex1_down_sim_fun : ⊨ᶠ ex1_down ≥ ex1_down_opt.
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
    move=> l' told tnew hplt α' nxtp' r0 ? _ IS_i σs2 σt2 s_new tk _ /=.
    subst sarg.
    specialize (IS_i O ltac:(simpl; lia)). rewrite shift_loc_0_nat in IS_i.
    destruct IS_i as [(ss & st & IS_i & Eqss & Eqst & ARELs) TOP].
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
  sim_apply_l sim_body_copy_unique_l; [solve_sim..|].
  apply: sim_body_result=>_ /=.
  apply: sim_body_let_l=>/=.
  (* Call *)
  rewrite -(right_id ε op (_ ⋅ res_loc _ _ _)).
  sim_bind (Call _ _) (Call _ _). (* TODO: sim_apply fails to instantiate evars *)
  apply (sim_body_step_over_call _ _ _ ε _ (ValR _) [] []); [solve_sim..|].
  move => rf' ? _ _ frs' frt' σs3 σt3 _ /= Eqs1 Eqs2 ? _ _. simplify_eq.
  exists 5%nat.
  apply: sim_body_result=>_ /=.
  sim_apply sim_body_let=>/=. clear frs' frt'.
  (* Copy local right *)
  sim_apply_r sim_body_copy_local_r; [solve_sim..|].
  apply: sim_body_result=>_ /=.
  (* Copy protected right *)
  sim_apply_r sim_body_deref_r =>/=.
  sim_apply_r sim_body_copy_protected_r;
    [solve_sim..|by rewrite lookup_insert|by eapply elem_of_dom_2|].
  apply: sim_body_result=>_ /=.
  apply: sim_body_let_r=>/=.
  (* Free stuff *)
  sim_apply sim_body_free_unique_local_1;
    [done|rewrite /res_loc /= insert_empty; solve_sim |by left|].
  simpl => _ _ α4 _.
  sim_apply sim_body_let=>/=.
  (* Finishing up. *)
  apply: sim_body_result => Hval. split.
  - exists σt.(snc). split; [done|]. admit.
  - constructor; [|by constructor].
    move : ARELs. apply arel_mono; [done|solve_res].
Abort.
