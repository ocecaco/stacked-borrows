From iris.algebra Require Import local_updates.

From stbor.lang Require Import steps_progress steps_inversion.
From stbor.sim Require Import local invariant.

Set Default Proof Using "Type".

Notation "r ⊨{ n , fs , ft } ( es , σs ) ≤ ( et , σt ) : Φ" :=
  (sim_local_body wsat vrel_expr fs ft r n%nat es%E σs et%E σt Φ)
  (at level 70, format "r  ⊨{ n , fs , ft }  ( es ,  σs )  ≤  ( et ,  σt )  :  Φ").

Notation "⊨{ fs , ft } f1 ≤ᶠ f2" :=
  (sim_local_fun wsat vrel_expr fs ft f1 f2)
  (at level 70, format "⊨{ fs , ft }  f1  ≤ᶠ  f2").

Instance dom_proper `{Countable K} {A : cmraT} :
  Proper ((≡) ==> (≡)) (dom (M:=gmap K A) (gset K)).
Proof.
  intros m1 m2 Eq. apply elem_of_equiv. intros i.
  by rewrite !elem_of_dom Eq.
Qed.

Lemma local_update_discrete_valid_frame `{CmraDiscrete A} (r_f r r' : A) :
  ✓ (r_f ⋅ r) → (r_f ⋅ r, r) ~l~> (r_f ⋅ r', r') → ✓ (r_f ⋅ r').
Proof.
  intros VALID UPD. apply cmra_discrete_valid.
  apply (UPD O (Some r_f)); [by apply cmra_discrete_valid_iff|by rewrite /= comm].
Qed.

(* Lemma sim_body_head_step fns fnt r n
  (Ks: list (ectxi_language.ectx_item (bor_ectxi_lang fns)))
  (Kt: list (ectxi_language.ectx_item (bor_ectxi_lang fnt))) es et σs σt
  r' es' et' σs' σt' :
  sim_body fns fnt r n (fill Ks es') σs' (fill Kt et') σt' →
  sim_body fns fnt r n (fill Ks es) σs (fill Kt et) σt.
Proof. *)

Lemma sim_body_init_call fs ft r n es et σs σt Φ :
  let σs' := mkState σs.(shp) σs.(sst) (σs.(snc) :: σs.(scs)) σs.(snp) (S σs.(snc)) in
  let σt' := mkState σt.(shp) σt.(sst) (σt.(snc) :: σt.(scs)) σt.(snp) (S σt.(snc)) in
  let r'  : resUR := (∅, {[σt.(snc) := to_callStateR (csOwned ∅)]}) in
  r ⋅ r' ⊨{n,fs,ft} (EndCall es, σs') ≤ (EndCall et, σt') : Φ →
  r ⊨{n,fs,ft} (InitCall es, σs) ≤ (InitCall et, σt) : Φ.
Proof.
  intros σs' σt1 r' SIM. pfold.
  constructor 2. intros. split; [by intros []|]. constructor 1.
  intros.
  exists (EndCall es), σs', (r ⋅ r').
  destruct (tstep_init_call_inv _ _ _ _ _ STEPT). subst et' σt'.
  have STEPS: (InitCall es, σs) ~{fs}~> (EndCall es, σs').
  { by eapply (head_step_tstep _ []), initcall_head_step. }
  have FRESH: (r_f ⋅ r).2 !! σt.(snc) = None.
  { destruct ((r_f ⋅ r).2 !! σt.(snc)) as [cs|] eqn:Eqcs; [|done].
    exfalso. destruct WSAT as (WFS & WFT & WFR & _).
    by apply (lt_irrefl σt.(snc)), WFR, (elem_of_dom_2 _ _ _ Eqcs). }
  have LOCAL: (r_f ⋅ r ⋅ ε, ε) ~l~> (r_f ⋅ r ⋅ r', r').
  { apply prod_local_update_2.
    rewrite /= right_id (comm _ (_ ⋅ _)) -insert_singleton_op //.
    by apply alloc_singleton_local_update. }
  exists n. split; last split; cycle 2.
  { (* sim cont *)  by punfold SIM. }
  { (* STEP src *)  left. by apply tc_once. }
  (* WSAT new *)
  destruct WSAT as (WFS & WFT & WFR & VALID & PINV & CINV & SREL).
  rewrite assoc.
  split; last split; last split; last split; last split; last split.
  { (* WF src *)    by apply (tstep_wf _ _ _ STEPS WFS). }
  { (* WF tgt *)    by apply (tstep_wf _ _ _ STEPT WFT). }
  { (* WF res *)
    constructor.
    - intros c.
      rewrite /= comm -insert_singleton_op // dom_insert
              elem_of_union elem_of_singleton.
      move => [->|/(wf_res_call_id _ _ WFR)]; lia.
    - intros ?. rewrite /= right_id. apply WFR. }
  { (* VALID *)
    apply (local_update_discrete_valid_frame (r_f ⋅ r) ε r'); [|done].
    by rewrite right_id. }
  { (* ptrmap_inv *)
    move => t k h /=. rewrite right_id. apply PINV. }
  { (* cmap_inv *)
    intros c cs.
    rewrite /= (comm _ (r_f.2 ⋅ r.2)) -insert_singleton_op //.
    case (decide (c = σt.(snc))) => [->|NE].
    - rewrite lookup_insert. intros Eqcs%Some_equiv_inj.
      inversion Eqcs as [?? Eq| |]; subst. inversion Eq as [?? Eq2|] ; subst.
      split; [by left|]. intros ? IN. exfalso. move : IN.
      by rewrite -Eq2 elem_of_empty.
    - rewrite lookup_insert_ne // => /CINV. destruct cs as [[]| |]; [|done..].
      intros [? Ht]. split; [by right|]. intros ????. rewrite right_id. by apply Ht. }
  { (* srel *)
    destruct SREL as (?&?&?&?&SREL).
    do 2 (split; [done|]). do 2 (split; [simpl; by f_equal|]).
    move => l s /= /SREL [[ss [? PUB]]|[t [c [T [h [PRI [? ?]]]]]]]; [left|right].
    - exists ss. split; [done|]. move : PUB. rewrite /arel /=.
      destruct s, ss as [| |l2 [|]|]; auto.
      by setoid_rewrite (right_id _ _ (r_f.1 ⋅ r.1)).
    - exists t, c, T, h. rewrite /= right_id. split; [|done].
      rewrite (comm _ (r_f.2 ⋅ r.2)) -insert_singleton_op //.
      rewrite lookup_insert_ne // => Eqc. subst c.
      apply (lt_irrefl σt.(snc)), WFR.
      case (decide (σt.(snc) ∈ dom (gset nat) (r_f ⋅ r).2))
        => [//|/not_elem_of_dom Eq1]. rewrite Eq1 in PRI. by inversion PRI. }
Qed.

Lemma stuck_fill fns K (e : ectx_language.expr (bor_ectx_lang fns)) σ :
  stuck e σ → stuck (fill K e) σ.
Proof.
  intros ST. split; [by apply fill_not_val, ST|apply irreducible_fill; apply ST].
Qed.

(* Lemma sim_body_end_call fns fnt r n es et σs σt :
  sim_body fns fnt r n es σs et σt →
  sim_body fns fnt r n (EndCall es) σs (EndCall et) σt.
Proof.
  revert r n es et σs σt. pcofix CIH. rename r into R.
  intros r n es et σs σt PR.
  punfold PR. pfold. inversion PR; subst.
  { constructor 1. by apply (stuck_fill _ [EndCallCtx]). }
  constructor 2. intros.
  destruct (STEP _ WSAT) as [TE ST]. split; [by intros []|].
  constructor 1. intros.
  case (decide (terminal et)) => [Tet|NTet].
  - destruct (tstep_end_call_terminal_inv _ _ _ _ _ Tet STEPT)
      as (vt & Eqvt & Eqet & c & cids & EQC & EQS). subst.
    destruct (TE Tet) as
      (es' & σs1 & r1 & STEPS1 & Tes1 & WSAT1).
    exists es, (mkState σs1.(shp) σs1.(sst) cids σs1.(snp) σs1.(snc)).
Abort. *)
