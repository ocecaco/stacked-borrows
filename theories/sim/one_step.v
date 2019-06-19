From iris.algebra Require Import local_updates.

From stbor.lang Require Import steps_progress steps_inversion.
From stbor.sim Require Import local invariant.

Set Default Proof Using "Type".

Lemma local_update_discrete_valid_frame `{CmraDiscrete A} (r_f r r' : A) :
  ✓ (r_f ⋅ r) → (r_f ⋅ r, r) ~l~> (r_f ⋅ r', r') → ✓ (r_f ⋅ r').
Proof.
  intros VALID UPD. apply cmra_discrete_valid.
  apply (UPD O (Some r_f)); [by apply cmra_discrete_valid_iff|by rewrite /= comm].
Qed.

Notation sim_body := (sim_local_body wsat vrel_expr).
Notation sim_fun := (sim_local_fun wsat vrel_expr).
Notation sim_funs := (sim_local_funs wsat vrel_expr).

Instance dom_proper `{Countable K} {A : cmraT} :
  Proper ((≡) ==> (≡)) (dom (M:=gmap K A) (gset K)).
Proof.
  intros m1 m2 Eq. apply elem_of_equiv. intros i.
  by rewrite !elem_of_dom Eq.
Qed.

Lemma sim_body_InitCall fns fnt r n es et σs σt :
  let σs' := mkState σs.(shp) σs.(sst) (σs.(snc) :: σs.(scs)) σs.(snp) (S σs.(snc)) in
  let σt' := mkState σt.(shp) σt.(sst) (σt.(snc) :: σt.(scs)) σt.(snp) (S σt.(snc)) in
  let r'  : resUR := (∅, {[σt.(snc) := to_callStateR (csOwned ∅)]}) in
  sim_body fns fnt (r ⋅ r') n (EndCall es) σs' (EndCall et) σt' →
  sim_body fns fnt r n (InitCall es) σs (InitCall et) σt.
Proof.
  intros σs' σt' r' SIM. pfold. apply sim_local_body_step.
  intros. exists (EndCall es), σs', (r ⋅ r').
  destruct (tstep_init_call_inv _ _ _ _ _ STEPT).
  subst e_tgt' σ_tgt'.
  have STEPS: (InitCall es, σs) ~{fns}~> (EndCall es, σs').
  { by eapply (head_step_tstep _ []), initcall_head_step. }
  have FRESH: (r_f ⋅ r).2 !! σt.(snc) = None.
  { destruct ((r_f ⋅ r).2 !! σt.(snc)) as [cs|] eqn:Eqcs; [|done].
    exfalso. destruct WSAT as [WF _].
    by apply (lt_irrefl σt.(snc)), WF, (elem_of_dom_2 _ _ _ Eqcs). }
  have LOCAL: (r_f ⋅ r ⋅ ε, ε) ~l~> (r_f ⋅ r ⋅ r', r').
  { apply prod_local_update_2.
    rewrite /= right_id (comm _ (_ ⋅ _)) -insert_singleton_op //.
    by apply alloc_singleton_local_update. }
  exists n. split; last split; last split; last split; last split; cycle 3.
  { (* WF src *)    by apply (tstep_wf _ _ _ STEPS WFS). }
  { (* WF tgt *)    by apply (tstep_wf _ _ _ STEPT WFT). }
  { (* sim cont *)  by punfold SIM. }
  { (* STEP src *)  left. by apply tc_once. }
  { (* VALID new *)
    rewrite assoc.
    apply (local_update_discrete_valid_frame (r_f ⋅ r) ε r'); [|done].
    by rewrite right_id. }
  (* WSAT new *)
  destruct WSAT as (WF & PINV & CINV & SREL).
  rewrite assoc. split; last split; last split.
  { constructor.
    - intros c.
      rewrite /= (comm _ (r_f.2 ⋅ r.2)) -insert_singleton_op // dom_insert
              elem_of_union elem_of_singleton.
      move => [->|/(wf_res_call_id _ _ WF)]; lia.
    - intros ?. rewrite /= right_id. apply WF. }
  { move => t k h /=. rewrite right_id. apply PINV. }
  { intros c cs.
    rewrite /= (comm _ (r_f.2 ⋅ r.2)) -insert_singleton_op //.
    case (decide (c = σt.(snc))) => [->|NE].
    rewrite lookup_insert.
    - admit.
    - rewrite lookup_insert_ne // => /CINV. destruct cs as [[]| |]; [|done..].
      intros [? Ht]. split; [by right|]. intros ????. rewrite right_id. by apply Ht. }
  { destruct SREL as (?&?&?&?&SREL).
    do 2 (split; [done|]). do 2 (split; [simpl; by f_equal|]).
    move => l s /= /SREL [[ss [? PUB]]|[t [c [T [h [PRI [? ?]]]]]]]; [left|right].
    - exists ss. split; [done|]. move : PUB. rewrite /arel /=.
      destruct s, ss as [| |l2 [|]|]; auto.
      by setoid_rewrite (right_id _ _ (r_f.1 ⋅ r.1)).
    - exists t, c, T, h. rewrite /= right_id. split; [|done].
      rewrite (comm _ (r_f.2 ⋅ r.2)) -insert_singleton_op //.
      rewrite lookup_insert_ne // => Eqc. subst c.
      apply (lt_irrefl σt.(snc)), WF.
      case (decide (σt.(snc) ∈ dom (gset nat) (r_f ⋅ r).2))
        => [//|/not_elem_of_dom Eq1]. rewrite Eq1 in PRI. by inversion PRI. }
Admitted.
