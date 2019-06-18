From stbor.lang Require Import defs.
From stbor.sim Require Import local invariant.

Definition sim_body := sim_local_body wsat vrel_expr.
Definition sim_fun := sim_local_fun wsat vrel_expr.
Definition sim_funs := sim_local_funs wsat vrel_expr.

Definition foo_s : function :=
  fun: [],
  let: "i" := new_place int #[1] in
  let: "x" := new_place (&mut int) &"i" in
  Retag "x" Default ;;
  let: "j" := new_place int #[1] in
  let: "y" := new_place (&mut int) &"j" in
  Retag "y" Default ;;
  *{int} (Copy1 "y") <- #[5] ;;
  *{int} (Copy1 "x") <- #[3] ;;
  Free "i" ;;
  Free "x" ;;
  Free "j" ;;
  Free "y"
  .

Definition foo_t : function :=
  fun: [],
  let: "i" := new_place int #[1] in
  let: "x" := new_place (&mut int) &"i" in
  Retag "x" Default ;;
  let: "j" := new_place int #[1] in
  let: "y" := new_place (&mut int) &"j" in
  Retag "y" Default ;;
  (* reordering x and y *)
  *{int} (Copy1 "x") <- #[3] ;;
  *{int} (Copy1 "y") <- #[5] ;;
  Free "i" ;;
  Free "x" ;;
  Free "j" ;;
  Free "y"
  .

Lemma subst_l_is_Some_length xl el e e' :
  subst_l xl el e = Some e' → length xl = length el.
Proof.
  revert e' el. induction xl as [|x xl IH] => e' el; [by destruct el|].
  destruct el as [|e1 el]; [done|].
  rewrite /= /subst'. intros Eq. f_equal.
  destruct (subst_l xl el e) as [e2|] eqn:Eqs; [|done]. simplify_option_eq.
  by apply (IH _ _ Eqs).
Qed.

Lemma subst_l_nil_is_Some el e e' :
  subst_l [] el e = Some e' → e' = e.
Proof.
  intros Eq.
  have EqN: el = [].
  { apply nil_length_inv. by rewrite -(subst_l_is_Some_length _ _ _ _ Eq). }
  subst el. simpl in Eq. by simplify_eq.
Qed.

(* Lemma sim_local_body_InitCall_aux (fns_s fns_t: fn_env) r (es et: expr) σs σt et' ct'
  (VL: ✓ r) (WS: wsat r σs σt)
  (ST: (InitCall et, (mkConfig fns_t σt)) ~t~> (et', ct')) :
  let σt' := mkState σt.(shp) σt.(sst) (σt.(snc) :: σt.(scs)) σt.(snp) (S σt.(snc)) in
  let σs' := mkState σs.(shp) σs.(sst) (σs.(snc) :: σs.(scs)) σs.(snp) (S σs.(snc)) in
  et' = et ∧ ct' = mkConfig fns_t σt' ∧
  (InitCall es, (mkConfig fns_s σs)) ~t~>* (es, mkConfig fns_s σs').
Proof.
Abort. *)

From iris.algebra Require Import updates local_updates.

Lemma sim_body_InitCall fns fnt r es et σs σt :
  let σs' := mkState σs.(shp) σs.(sst) (σs.(snc) :: σs.(scs)) σs.(snp) (S σs.(snc)) in
  let σt' := mkState σt.(shp) σt.(sst) (σt.(snc) :: σt.(scs)) σt.(snp) (S σt.(snc)) in
  let r'  : resUR := (∅, {[σt.(snc) := to_callStateR (csOwned ∅)]}) in
  sim_body fns fnt (r ⋅ r') es σs' et σt' →
  sim_body fns fnt r (InitCall es) σs (InitCall et) σt.
Proof.
  intros σs' σt' r' SIM. pfold. apply sim_local_body_step.
  intros. exists es, σs', (r ⋅ r').
  have ?: e_tgt' = et. { admit. }
  have ?: σ_tgt' = σt'. { admit. }
  subst e_tgt' σ_tgt'. simpl in *.
  split; last split; last split.
  - admit.
  - rewrite cmra_assoc. admit.
  - rewrite cmra_assoc. admit.
  - by punfold SIM.
Admitted.

Lemma foo_sim_fun fns fnt : sim_fun fns fnt foo_s foo_t.
Proof.
  move => r es et els elt σs σt _ _ _ /subst_l_nil_is_Some ? /subst_l_nil_is_Some ?.
  subst es et. clear els elt.

  (* InitCall *)
  apply sim_body_InitCall.
Abort.
