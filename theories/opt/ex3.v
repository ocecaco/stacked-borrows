From stbor.sim Require Import local invariant refl.
From stbor.sim Require Import tactics simple program.
From stbor.sim Require Import refl_step right_step left_step derived_step.

Set Default Proof Using "Type".

(** Moving a write to a mutable reference up across unknown code. *)

(* Assuming x : &mut i32 *)
Definition ex3_unopt : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    retag_place "x" (RefPtr Mutable) int FnEntry ;;
    *{int} "x" <- #[42] ;;
    let: "v" := Call #[ScFnPtr "f"] [] in
    *{int} "x" <- #[13] ;;
    Free "x" ;;
    "v"
  .

Definition ex3_opt_1 : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    retag_place "x" (RefPtr Mutable) int FnEntry ;;
    *{int} "x" <- #[42] ;;
    *{int} "x" <- #[13] ;;
    let: "v" := Call #[ScFnPtr "f"] [] in
    Free "x" ;;
    "v"
  .

Definition ex3_opt_2 : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    retag_place "x" (RefPtr Mutable) int FnEntry ;;
    *{int} "x" <- #[13] ;;
    let: "v" := Call #[ScFnPtr "f"] [] in
    Free "x" ;;
    "v"
  .

(* TODO: show refinement to be transitive *)
Lemma ex3_sim_fun : ⊨ᶠ ex3_unopt ≥ ex3_opt_1.
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
  (* Copy local place *)
  sim_apply sim_body_copy_local; [solve_sim..|].
  sim_apply sim_body_result => /= VALID.
  sim_apply (sim_body_deref _ _ _ _ (ValR _)).
  move => ?? Eq. symmetry in Eq. simplify_eq/=.
  (* Write unique of 42 *)
  sim_apply sim_body_write_unique_1;
    [done|solve_sim|by eexists|..]; [solve_sim..|].
  move => σs3 σt3 TOP3 /=.
  sim_apply sim_body_let=>/=.
  (* Copy local (right) *)
  sim_apply_r sim_body_copy_local_r; [solve_sim..|].
  apply: sim_body_result=>_/=.
  (* Write protected right *)
  sim_apply_r sim_body_deref_r =>/=.
  sim_apply_r sim_body_write_protected_r;
    [solve_sim..|by rewrite lookup_insert |by rewrite lookup_insert
    |by eapply (elem_of_dom_2 _ _ _ Eql')|].
  intros Eqss3 σt3' rt'. simpl.
  apply: sim_body_result=>_/=.
  sim_apply sim_body_let_r =>/=.
  (* Call *)
  rewrite -(right_id ε op (_ ⋅ rt')).
  sim_bind (Call _ _) (Call _ _). (* TODO: sim_apply fails to instantiate evars *)
  apply (sim_body_step_over_call _ _ _ ε _ (ValR _) [] []); [solve_sim..|].
  move => rf' ? _ _ frs' frt' σs4 σt4 VREL' /= Eqs1 Eqs2 ? _ _. simplify_eq.
  exists 5%nat.
  apply: sim_body_result=>_ /=.
  sim_apply sim_body_let=>/=.
  (* Copy local (left) *)
  sim_apply_l sim_body_copy_local_l; [solve_sim..|].
  apply: sim_body_result=>_/=.
  (* Write protected left *)
  sim_apply_l sim_body_deref_l =>/=.
Abort.
