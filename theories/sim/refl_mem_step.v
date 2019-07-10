From iris.algebra Require Import local_updates.

From stbor.lang Require Import steps_progress steps_inversion steps_retag.
From stbor.sim Require Export instance body invariant_access.

Set Default Proof Using "Type".

Section mem.
Implicit Types Φ: resUR → nat → result → state → result → state → Prop.

(** MEM STEP -----------------------------------------------------------------*)

Lemma wsat_tmap_nxtp r σs σt :
  wsat r σs σt → r.(rtm) !! σt.(snp) = None.
Proof.
  intros (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  destruct (r.(rtm) !! σt.(snp)) as [[k h]|] eqn:Eqr; [|done].
  exfalso.
  move : (proj1 (proj1 VALID) σt.(snp)). rewrite Eqr.
  intros [[k' Eqk']%tagKindR_valid VALh]. simpl in Eqk', VALh. subst k.
  destruct (PINV σt.(snp) k' h) as [Lt _]; [by rewrite Eqr|]. lia.
Qed.

Lemma sim_body_alloc_local fs ft r n T σs σt Φ :
  let l := (fresh_block σt.(shp), 0) in
  let t := (Tagged σt.(snp)) in
  let σs' := mkState (init_mem l (tsize T) σs.(shp))
                     (init_stacks σs.(sst) l (tsize T) t) σs.(scs)
                     (S σs.(snp)) σs.(snc) in
  let σt' := mkState (init_mem l (tsize T) σt.(shp))
                     (init_stacks σt.(sst) l (tsize T) t) σt.(scs)
                     (S σt.(snp)) σt.(snc) in
  let r' : resUR := res_mapsto l (repeat ☠%S (tsize T)) σt.(snp) in
  Φ (r ⋅ r') n (PlaceR l t T) σs' (PlaceR l t T) σt' →
  r ⊨{n,fs,ft} (Alloc T, σs) ≥ (Alloc T, σt) : Φ.
Proof.
  intros l t σs' σt' r' POST.
  pfold. intros NT. intros.
  have EqDOM := wsat_heap_dom _ _ _ WSAT.
  have EqFRESH := fresh_block_equiv _ _ EqDOM.
  have HNP := wsat_tmap_nxtp _ _ _ WSAT.
  have HEQr': (r_f ⋅ r ⋅ r').(rtm) !! snp σt ≡
      Some (to_tagKindR tkUnique, to_heapR (write_mem l (repeat ☠%S (tsize T)) ∅)).
  { rewrite lookup_op HNP left_id /= left_id lookup_insert //. }
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  destruct SREL as (Eqst&Eqnp&Eqcs&Eqnc&REL).
  have Eqlst: l = (fresh_block σs.(shp), 0). { by rewrite /l EqFRESH. }
  split; [|done|].
  { right. do 2 eexists. by eapply (head_step_fill_tstep _ []), alloc_head_step. }
  constructor 1. intros ? σt1 STEPT.
  destruct (tstep_alloc_inv _ _ _ _ _ STEPT) as [? Eqσt'].
  rewrite -/σt' in Eqσt'. subst et' σt1.
  have STEPS: (Alloc T, σs) ~{fs}~> (Place l t T, σs').
  { subst l σs' t. rewrite Eqlst -Eqnp.
    eapply (head_step_fill_tstep _ []),  alloc_head_step. }
  eexists _, σs', (r ⋅ r'), n. split; last split.
  { left. by apply tc_once. }
  { have Eqrcm: (r_f ⋅ r ⋅ r').(rcm) ≡ (r_f ⋅ r).(rcm)
      by rewrite /rcm /= 2!right_id.
    have HLF : ∀ i, (i < tsize T)%nat → (r_f ⋅ r).(rlm) !! (l +ₗ i) = None.
    { intros i Lti.
      destruct ((r_f ⋅ r).(rlm) !! (l +ₗ i)) as [ls|] eqn:Eql; [|done].
      exfalso. move : (proj2 VALID (l +ₗ i)). rewrite Eql.
      intros [t1 ?]%tagR_valid. subst ls.
      specialize (LINV (l +ₗ i) t1) as (? & Eqs & ?); [by rewrite Eql|].
      have InD: (l +ₗ i) ∈ dom (gset loc) σt.(sst) by eapply elem_of_dom_2.
      rewrite <-(state_wf_dom _ WFT) in InD. by apply (is_fresh_block σt.(shp) i). }
    have VALID': ✓ (r_f ⋅ r ⋅ r').
    { apply (local_update_discrete_valid_frame _ ε r'); [by rewrite right_id|].
      rewrite /= right_id -cmra_assoc cmra_assoc.
      apply res_mapsto_local_alloc_local_update; [done|]. by rewrite repeat_length. }
    rewrite cmra_assoc.
    destruct (init_mem_lookup l (tsize T) σt.(shp)) as [HLmt1 HLmt2].
    destruct (init_mem_lookup l (tsize T) σs.(shp)) as [HLms1 HLms2].
    destruct (init_stacks_lookup σt.(sst) l (tsize T) t) as [HLst1 HLst2].
    destruct (init_stacks_lookup σs.(sst) l (tsize T) t) as [HLss1 HLss2].
    destruct (res_mapsto_llookup l (repeat ☠%S (tsize T)) σt.(snp)) as [EQ1 EQ2].
    rewrite repeat_length in EQ1, EQ2.
    split; last split; last split; last split; last split; last split.
    - by apply (tstep_wf _ _ _ STEPS WFS).
    - by apply (tstep_wf _ _ _ STEPT WFT).
    - done.
    - intros t1 k1 h1. subst σt'; simpl.
      case (decide (t1 = σt.(snp))) => ?; [subst t1|].
      + intros Eqh1. split; [simpl; lia|].
        move : Eqh1. rewrite HEQr'.
        intros [Eqk1 Eqh1]%Some_equiv_inj. simpl in Eqk1, Eqh1.
        intros l1 s1. rewrite -Eqh1 lookup_fmap.
        destruct (write_mem_lookup_case  l (repeat ☠%S (tsize T)) ∅ l1)
          as [(i & Lti & ? & Eql1)|(NEQl1 & Eql1)].
        * subst l1. rewrite Eql1. rewrite repeat_length in Lti.
          rewrite (repeat_lookup_lt_length _ _ _ Lti) /=.
          intros ?%Some_equiv_inj%to_agree_inj. simplify_eq.
          rewrite (HLst1 _ Lti) (HLmt1 _ Lti) (HLms1 _ Lti).
          intros stk ?. simplify_eq.
          intros pm opro ?%elem_of_list_singleton ?. simplify_eq.
          do 2 (split; [done|]). destruct k1. by eexists. by inversion Eqk1.
        * rewrite Eql1 lookup_empty. inversion 1.
      + intros Eqh'.
        have Eqh1: (r_f ⋅ r).(rtm) !! t1 ≡ Some (to_tagKindR k1, h1).
        { move : Eqh'. rewrite lookup_op res_mapsto_tlookup_ne // right_id //. }
        specialize (PINV _ _ _ Eqh1) as [? PINV]. split; [simpl; lia|].
        intros l1 s1 Eqs1 stk Eqstk.
        destruct (init_stacks_lookup_case _ _ _ _ _ _ Eqstk)
          as [[Eql1 NEQl1]|(i & (? & Lti) & Eql1)].
        * rewrite (HLmt2 _ NEQl1) (HLms2 _ NEQl1). by apply PINV.
        * subst l1.
          have Lti': (Z.to_nat i < tsize T)%nat by rewrite Nat2Z.inj_lt Z2Nat.id.
          have Eq2 := HLst1 _ Lti'. rewrite Z2Nat.id // Eqstk in Eq2. simplify_eq.
          intros ?? ?%elem_of_list_singleton. simplify_eq.
    - intros c cs. subst σt'. rewrite Eqrcm /=. intros Eqc.
      specialize (CINV _ _ Eqc). destruct cs as [[Tc|]| |]; [|done..].
      destruct CINV as [IN CINV]. split; [done|].
      intros t1 [Ltc Ht]%CINV. split; [lia|].
      intros k h.
      case (decide (t1 = σt.(snp))) => ?; [subst t1|]; [lia|].
      rewrite lookup_op res_mapsto_tlookup_ne // right_id. intros Eqh1.
      intros l1 InD1. specialize (Ht _ _ Eqh1 _ InD1) as (stk1 & pm1 & Eql1 & Eqp).
      destruct (init_stacks_lookup_case_2 _ l (tsize T) t _ _ Eql1)
        as [[EQ NEQ1]|(i & (? & Lti) & ? & EQ)].
      + rewrite EQ. clear -Eqp. naive_solver.
      + exfalso. subst l1.
        apply (is_fresh_block σt.(shp) i). rewrite (state_wf_dom _ WFT).
        by eapply elem_of_dom_2.
    - subst σt'. split; last split; last split; last split; [|simpl;auto..|].
      { by rewrite /= Eqst. } simpl.
      intros l1 [s1 HL1]%elem_of_dom.
      destruct (init_mem_lookup_case _ _ _ _ _ HL1)
        as [[Eqs1 NEQ]|(i & (? & Lti) & Eql)].
      + have InD1 : l1 ∈ dom (gset loc) σt.(shp) by eapply elem_of_dom_2.
        specialize (HLmt2 _ NEQ). specialize (HLms2 _ NEQ).
        specialize (REL _ InD1) as [PB|[t' PV]]; [left|right].
        * rewrite /pub_loc /= HLmt2 HLms2.
          intros st1 Eqst1. destruct (PB _ Eqst1) as [ss [Eqss AREL]].
          exists ss. split; [done|]. eapply arel_mono; [done| |eauto].
          apply cmra_included_l.
        * destruct PV as (h' & Eqh' & Eqt').
          exists t', h'. setoid_rewrite Eqrcm. split.
          { apply tmap_lookup_op_l_unique_equiv; [apply VALID'|done]. }
          { destruct Eqt'; [left|by right].
            apply lmap_lookup_op_l; [apply VALID'|done]. }
      + right. exists σt.(snp). eexists. split.
        * rewrite HEQr'; eauto.
        * left. subst l1. apply lmap_lookup_op_r; [apply VALID'|].
          have Lti': (Z.to_nat i < tsize T)%nat by rewrite Nat2Z.inj_lt Z2Nat.id.
          specialize (EQ1 _ Lti').
          rewrite Z2Nat.id // in EQ1. by rewrite EQ1.
    - intros l1 t1 Eqt. subst σt'. simpl. move : (proj2 VALID' l1) Eqt.
      rewrite lookup_op.
      destruct ((r_f ⋅ r).2 !! l1) as [ls1|] eqn:Eqls1; rewrite Eqls1.
      + intros VAL' Eql1.
        have NEQ: ∀ i, (i < tsize T)%nat → l1 ≠ l +ₗ i.
        { intros i Lt Eqi. subst l1.
          move : Eql1. rewrite (EQ1 _ Lt). apply lmap_exclusive_2. }
        rewrite /= (HLmt2 _ NEQ) (HLms2 _ NEQ) (HLst2 _ NEQ).
        apply lmap_exclusive_eq_l in Eql1. simplify_eq.
        destruct  (LINV l1 t1); [by rewrite Eqls1|]. split; [lia|done].
      + rewrite left_id. intros VALs Eqls.
        destruct (res_mapsto_llookup_case l _ _ _ _ Eqls) as [Eq1 IN].
        simpl in Eq1. simplify_eq.
        destruct IN as [i [[? Lti] Eql1]]. rewrite repeat_length in Lti.
        have Lti': (Z.to_nat i < tsize T)%nat by rewrite Nat2Z.inj_lt Z2Nat.id.
        have Eq2 := HLmt1 _ Lti'. rewrite Z2Nat.id // -Eql1 in Eq2.
        have Eq3 := HLms1 _ Lti'. rewrite Z2Nat.id // -Eql1 in Eq3.
        have Eq4 := HLst1 _ Lti'. rewrite Z2Nat.id // -Eql1 in Eq4.
        rewrite /= Eq2 Eq3 Eq4.
        specialize (HLF _ Lti'). rewrite Z2Nat.id // in HLF.
        split; [|done]. lia. }
  left.
  apply: sim_body_result. intros.
  apply POST; eauto.
Qed.

Lemma sim_body_alloc_public fs ft r n T σs σt Φ :
  let l := (fresh_block σt.(shp), 0) in
  let t := (Tagged σt.(snp)) in
  let σs' := mkState (init_mem l (tsize T) σs.(shp))
                     (init_stacks σs.(sst) l (tsize T) t) σs.(scs)
                     (S σs.(snp)) σs.(snc) in
  let σt' := mkState (init_mem l (tsize T) σt.(shp))
                     (init_stacks σt.(sst) l (tsize T) t) σt.(scs)
                     (S σt.(snp)) σt.(snc) in
  let r' : resUR := res_tag σt.(snp) tkPub ∅ in
  Φ (r ⋅ r') n (PlaceR l t T) σs' (PlaceR l t T) σt' →
  r ⊨{n,fs,ft} (Alloc T, σs) ≥ (Alloc T, σt) : Φ.
Proof.
  intros l t σs' σt' r' POST.
  pfold. intros NT. intros.
  have EqDOM := wsat_heap_dom _ _ _ WSAT.
  have EqFRESH := fresh_block_equiv _ _ EqDOM.
  have HNP := wsat_tmap_nxtp _ _ _ WSAT.
  have HEQr': (r_f ⋅ r ⋅ r').(rtm) !! snp σt ≡ Some (to_tagKindR tkPub, to_heapR ∅).
  { rewrite lookup_op HNP left_id res_tag_lookup //. }
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  destruct SREL as (Eqst&Eqnp&Eqcs&Eqnc&REL).
  have Eqlst: l = (fresh_block σs.(shp), 0). { by rewrite /l EqFRESH. }
  split; [|done|].
  { right. do 2 eexists. by eapply (head_step_fill_tstep _ []), alloc_head_step. }
  constructor 1. intros ? σt1 STEPT.
  destruct (tstep_alloc_inv _ _ _ _ _ STEPT) as [? Eqσt'].
  rewrite -/σt' in Eqσt'. subst et' σt1.
  have STEPS: (Alloc T, σs) ~{fs}~> (Place l t T, σs').
  { subst l σs' t. rewrite Eqlst -Eqnp.
    eapply (head_step_fill_tstep _ []),  alloc_head_step. }
  eexists _, σs', (r ⋅ r'), n. split; last split.
  { left. by apply tc_once. }
  { have Eqrcm: (r_f ⋅ r ⋅ r').(rcm) ≡ (r_f ⋅ r).(rcm)
      by rewrite /rcm /= right_id.
    have Eqrlm: (r_f ⋅ r ⋅ r').(rlm) ≡ (r_f ⋅ r).(rlm) by rewrite /= right_id.
    have HLF : ∀ i, (i < tsize T)%nat → (r_f ⋅ r).(rlm) !! (l +ₗ i) = None.
    { intros i Lti.
      destruct ((r_f ⋅ r).(rlm) !! (l +ₗ i)) as [ls|] eqn:Eql; [|done].
      exfalso. move : (proj2 VALID (l +ₗ i)). rewrite Eql.
      intros [t1 ?]%tagR_valid. subst ls.
      specialize (LINV (l +ₗ i) t1) as (? & Eqs & ?); [by rewrite Eql|].
      have InD: (l +ₗ i) ∈ dom (gset loc) σt.(sst) by eapply elem_of_dom_2.
      rewrite <-(state_wf_dom _ WFT) in InD. by apply (is_fresh_block σt.(shp) i). }
    have VALID': ✓ (r_f ⋅ r ⋅ r').
    { apply (local_update_discrete_valid_frame _ ε r'); [by rewrite right_id|].
      rewrite /= right_id -cmra_assoc cmra_assoc.
      by apply res_tag_alloc_local_update. }
    rewrite cmra_assoc.
    destruct (init_mem_lookup l (tsize T) σt.(shp)) as [HLmt1 HLmt2].
    destruct (init_mem_lookup l (tsize T) σs.(shp)) as [HLms1 HLms2].
    destruct (init_stacks_lookup σt.(sst) l (tsize T) t) as [HLst1 HLst2].
    destruct (init_stacks_lookup σs.(sst) l (tsize T) t) as [HLss1 HLss2].
    split; last split; last split; last split; last split; last split.
    - by apply (tstep_wf _ _ _ STEPS WFS).
    - by apply (tstep_wf _ _ _ STEPT WFT).
    - done.
    - intros t1 k1 h1. subst σt'; simpl.
      case (decide (t1 = σt.(snp))) => ?; [subst t1|].
      + intros Eqh1. split; [simpl; lia|].
        move : Eqh1. rewrite HEQr'.
        intros [Eqk1 Eqh1]%Some_equiv_inj. simpl in Eqk1, Eqh1.
        intros l1 s1. rewrite -Eqh1 lookup_fmap lookup_empty. by inversion 1.
      + intros Eqh'.
        have Eqh1: (r_f ⋅ r).(rtm) !! t1 ≡ Some (to_tagKindR k1, h1).
        { move : Eqh'. rewrite lookup_op res_tag_lookup_ne // right_id //. }
        specialize (PINV _ _ _ Eqh1) as [? PINV]. split; [simpl; lia|].
        intros l1 s1 Eqs1 stk Eqstk.
        destruct (init_stacks_lookup_case _ _ _ _ _ _ Eqstk)
          as [[Eql1 NEQl1]|(i & (? & Lti) & Eql1)].
        * rewrite (HLmt2 _ NEQl1) (HLms2 _ NEQl1). by apply PINV.
        * subst l1.
          have Lti': (Z.to_nat i < tsize T)%nat by rewrite Nat2Z.inj_lt Z2Nat.id.
          have Eq2 := HLst1 _ Lti'. rewrite Z2Nat.id // Eqstk in Eq2. simplify_eq.
          intros ?? ?%elem_of_list_singleton. simplify_eq.
    - intros c cs. subst σt'. rewrite Eqrcm /=. intros Eqc.
      specialize (CINV _ _ Eqc). destruct cs as [[Tc|]| |]; [|done..].
      destruct CINV as [IN CINV]. split; [done|].
      intros t1 [Ltc Ht]%CINV. split; [lia|].
      intros k h.
      case (decide (t1 = σt.(snp))) => ?; [subst t1|]; [lia|].
      rewrite lookup_op res_tag_lookup_ne // right_id. intros Eqh1.
      intros l1 InD1. specialize (Ht _ _ Eqh1 _ InD1) as (stk1 & pm1 & Eql1 & Eqp).
      destruct (init_stacks_lookup_case_2 _ l (tsize T) t _ _ Eql1)
        as [[EQ NEQ1]|(i & (? & Lti) & ? & EQ)].
      + rewrite EQ. clear -Eqp. naive_solver.
      + exfalso. subst l1.
        apply (is_fresh_block σt.(shp) i). rewrite (state_wf_dom _ WFT).
        by eapply elem_of_dom_2.
    - subst σt'. split; last split; last split; last split; [|simpl;auto..|].
      { by rewrite /= Eqst. } simpl.
      intros l1 [s1 HL1]%elem_of_dom.
      destruct (init_mem_lookup_case _ _ _ _ _ HL1)
        as [[Eqs1 NEQ]|(i & (? & Lti) & Eql)].
      + have InD1 : l1 ∈ dom (gset loc) σt.(shp) by eapply elem_of_dom_2.
        specialize (HLmt2 _ NEQ). specialize (HLms2 _ NEQ).
        specialize (REL _ InD1) as [PB|[t' PV]]; [left|right].
        * rewrite /pub_loc /= HLmt2 HLms2.
          intros st1 Eqst1. destruct (PB _ Eqst1) as [ss [Eqss AREL]].
          exists ss. split; [done|]. eapply arel_mono; [done| |eauto].
          apply cmra_included_l.
        * destruct PV as (h' & Eqh' & Eqt').
          exists t', h'. setoid_rewrite Eqrcm. split.
          { apply tmap_lookup_op_l_unique_equiv; [apply VALID'|done]. }
          { destruct Eqt'; [left|by right].
            apply lmap_lookup_op_l; [apply VALID'|done]. }
      + left. subst l1. intros st. simpl.
        have Lti': (Z.to_nat i < tsize T)%nat by rewrite Nat2Z.inj_lt Z2Nat.id.
        specialize (HLmt1 _ Lti'). rewrite Z2Nat.id // in HLmt1.
        specialize (HLms1 _ Lti'). rewrite Z2Nat.id // in HLms1.
        rewrite HLmt1 HLms1. inversion 1. subst st. by exists ScPoison.
    - intros l1 t1. rewrite Eqrlm. subst σt'. simpl. intros Eqt.
      specialize (LINV _ _ Eqt) as (Lt1 & Eqstk1 & Eqhp1).
      split; [lia|].
      have NEQ: ∀ i, (i < tsize T)%nat → l1 ≠ l +ₗ i.
      { intros i Lt Eqi. subst l1. apply (is_fresh_block σt.(shp) i).
        rewrite (state_wf_dom _ WFT). by eapply elem_of_dom_2. }
      rewrite (HLmt2 _ NEQ) (HLms2 _ NEQ) (HLst2 _ NEQ) //. }
  left.
  apply: sim_body_result. intros.
  apply POST; eauto.
Qed.

(** Copy *)
Lemma sim_body_copy_public fs ft r n (pl: result) σs σt Φ
  (RREL: rrel r pl pl) :
  (∀ l t T vs vt r',
    pl = PlaceR l t T →
    read_mem l (tsize T) σs.(shp) = Some vs →
    read_mem l (tsize T) σt.(shp) = Some vt →
    ∀ α', memory_read σt.(sst) σt.(scs) l t (tsize T) = Some α' →
      let σs' := mkState σs.(shp) α' σs.(scs) σs.(snp) σs.(snc) in
      let σt' := mkState σt.(shp) α' σt.(scs) σt.(snp) σt.(snc) in
      vrel ((* r ⋅  *) r') vs vt → Φ (r ⋅ r') n (ValR vs) σs' (ValR vt) σt') →
  r ⊨{n,fs,ft} (Copy pl, σs) ≥ (Copy pl, σt) : Φ.
Proof.
  intros POST. pfold. intros NT. intros.
  have WSAT1 := WSAT. (* backup *)

  (* making a step *)
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  split; [|done|].
  { right.
    destruct (NT (Copy pl) σs) as [[]|[es' [σs' STEPS]]];
      [done..|].
    destruct (tstep_copy_inv _ _ _ _ _ STEPS)
      as (l&t&T& vs & α' & EqH & ? & Eqvs & Eqα' & ?). symmetry in EqH. simplify_eq.
    destruct (read_mem_is_Some l (tsize T) σt.(shp)) as [vt Eqvt].
    { intros m. rewrite (srel_heap_dom _ _ _ WFS WFT SREL).
      apply (read_mem_is_Some' l (tsize T) σs.(shp)). by eexists. }
    have Eqα'2: memory_read σt.(sst) σt.(scs) l t (tsize T) = Some α'.
    { destruct SREL as (Eqst&?&Eqcs&?). by rewrite -Eqst -Eqcs. }
    exists (#vt)%E, (mkState σt.(shp) α' σt.(scs) σt.(snp) σt.(snc)).
    by eapply (head_step_fill_tstep _ []), copy_head_step'. }
  constructor 1. intros.
  destruct (tstep_copy_inv _ _ _ _ _ STEPT)
    as (l&t&T& vt & α' & EqH & ? & Eqvt & Eqα' & ?). symmetry in EqH. simplify_eq.
  destruct (read_mem_is_Some l (tsize T) σs.(shp)) as [vs Eqvs].
  { intros m. rewrite -(srel_heap_dom _ _ _ WFS WFT SREL).
    apply (read_mem_is_Some' l (tsize T) σt.(shp)). by eexists. }
  have Eqα'2: memory_read σs.(sst) σs.(scs) l t (tsize T) = Some α'.
  { destruct SREL as (Eqst&?&Eqcs&?). by rewrite Eqst Eqcs. }
  set σs' := mkState σs.(shp) α' σs.(scs) σs.(snp) σs.(snc).
  have STEPS: (Copy (Place l t T), σs) ~{fs}~> ((#vs)%E, σs').
  { by eapply (head_step_fill_tstep _ []), copy_head_step'. }

  (* unfolding rrel for place *)
  simpl in RREL. destruct RREL as [VREL _].
  inversion VREL as [|???? AREL U]; subst; simplify_eq. clear U VREL.
  destruct AREL as (_ & _ & AREL).

  (* returned values must be related *)
  have CORE : (r_f ⋅ r) ≡ r_f ⋅ r ⋅ core (r_f ⋅ r) by rewrite cmra_core_r.
  assert (VREL': vrel (core (r_f ⋅ r)) vs vt).
  { destruct SREL as (Eqst & Eqnp & Eqcs & Eqnc & PRIV).
    destruct (read_mem_values _ _ _ _ Eqvs) as [Eqls HLs].
    destruct (read_mem_values _ _ _ _ Eqvt) as [Eqlt HLt].
    apply Forall2_same_length_lookup. split; [by rewrite Eqls Eqlt|].
    intros i ss st Hss Hst.
    have HLLs := lookup_lt_Some _ _ _ Hss. have HLLt := lookup_lt_Some _ _ _ Hst.
    rewrite -Eqls in HLs. specialize (HLs _ HLLs). rewrite Hss in HLs.
    rewrite -Eqlt in HLt. specialize (HLt _ HLLt). rewrite Hst in HLt.
    have InD: (l +ₗ i) ∈ dom (gset loc) σt.(shp) by eapply elem_of_dom_2.
    specialize (PRIV _ InD).

    destruct (for_each_lookup_case_2 _ _ _ _ _ Eqα') as [EQ1 _].
    rewrite Eqlt in HLLt.
    specialize (EQ1 _ HLLt) as (stk & stk' & Eqstk & Eqstk' & ACC).
    have ISA: is_Some (access1 stk AccessRead t (scs σt)).
    { move : ACC. case access1; [by eexists|done]. }

    destruct PRIV as [PB|[t' PRIV]]; last first.
    { destruct (priv_pub_access_UB _ _ _ _ _ _ _ _ Eqstk ISA WSAT1 PRIV).
      destruct t; [|done]. destruct AREL as [h Eqh].
      apply (tmap_lookup_op_r_equiv_pub r_f.(rtm)) in Eqh as [h1 Eqh1];
        [|apply VALID]. by exists (h1 ⋅ h). }

    specialize (PB _ HLt) as [ss1 [Eqss1 AREL1]].
    rewrite Eqss1 in HLs. simplify_eq. by apply arel_persistent. }

  (* reestablishing WSAT *)
  exists (Val vs), σs', (r ⋅ (core (r_f ⋅ r))), n. split; last split.
  { left. by constructor 1. }
  { rewrite cmra_assoc -CORE.
    split; last split; last split; last split; last split; last split.
    - by apply (tstep_wf _ _ _ STEPS WFS).
    - by apply (tstep_wf _ _ _ STEPT WFT).
    - done.
    - intros t1 k h Eqt. specialize (PINV t1 k h Eqt) as [Lt PI]. simpl.
      split; [done|]. intros l' s' Eqk' stk' Eqstk'.
      specialize (PI _ _ Eqk') as PI.
      destruct (for_each_access1 _ _ _ _ _ _ _ Eqα' _ _ Eqstk')
        as (stk & Eqstk & SUB & ?).
      intros pm opro In' NDIS.
      destruct (SUB _ In') as (it2 & In2 & Eqt2 & Eqp2 & NDIS2).
      specialize (PI _ Eqstk it2.(perm) opro) as [Eql' [? HTOP]].
      { simpl in *. rewrite /= Eqt2 Eqp2. by destruct it2. }
      { simpl in *. by rewrite (NDIS2 NDIS). }
      do 2 (split; [done|]).
      destruct (for_each_lookup_case _ _ _ _ _ Eqα' _ _ _ Eqstk Eqstk')
        as [?|[MR _]]; [by subst|]. clear -In' MR HTOP Eqstk WFT NDIS.
      destruct (access1 stk AccessRead t σt.(scs)) as [[n stk1]|] eqn:Eqstk';
        [|done]. simpl in MR. simplify_eq.
      destruct (state_wf_stack_item _ WFT _ _ Eqstk). move : Eqstk' HTOP.
      destruct k.
      + eapply access1_head_preserving; eauto.
      + eapply access1_active_SRO_preserving; eauto.
    - intros c cs Eqc. specialize (CINV _ _ Eqc). simpl.
      clear -Eqα' CINV. destruct cs as [[T1|]| |]; [|done..].
      destruct CINV as [IN CINV]. split; [done|].
      intros t1 InT. specialize (CINV _ InT) as [? CINV]. split; [done|].
      intros k h Eqt l' Inh.
      destruct (CINV _ _ Eqt _ Inh) as (stk' & pm' & Eqstk' & Instk' & NDIS).
      destruct (for_each_access1_active_preserving _ _ _ _ _ _ _ Eqα' _ _ Eqstk')
        as [stk [Eqstk AS]].
      exists stk, pm'. split; last split; [done| |done]. by apply AS.
    - rewrite /srel /=. by destruct SREL as (?&?&?&?&?).
    - intros l1 t1. simpl. intros Eqs.
      specialize (LINV _ _ Eqs) as (LTi & Eqst & Eqhs).
      split; [done|]. split; [|done].
      destruct (for_each_access1_lookup_inv _ _ _ _ _ _ _ Eqα' _ _ Eqst)
        as (stk2 & Eq2 & LOR).
      destruct LOR as [[n' ACC1]|LOR]; [|by rewrite LOR].
      destruct (local_access_eq _ _ _ _ _ _ _ _ _ _ Eqst ACC1 WSAT1 Eqs)
        as [? Eqstk2]. by rewrite Eq2 Eqstk2. }
  left.
  apply: sim_body_result. intros. eapply POST; eauto.
Qed.

(** Write *)

(** For writing to public locations. *)
Lemma sim_body_write_public
  fs ft (r: resUR) n (pl vl: result) σs σt Φ
  (RRELp: rrel r pl pl) (RRELv: rrel r vl vl) :
  (∀ l t T v α',
    pl = PlaceR l t T → vl = ValR v →
    memory_written σt.(sst) σt.(scs) l t (tsize T) = Some α' →
    let σs' := mkState (write_mem l v σs.(shp)) α' σs.(scs) σs.(snp) σs.(snc) in
    let σt' := mkState (write_mem l v σt.(shp)) α' σt.(scs) σt.(snp) σt.(snc) in
    Φ r n (ValR [☠]%S) σs' (ValR [☠]%S) σt' : Prop) →
  r ⊨{n,fs,ft} (pl <- vl, σs) ≥ (pl <- vl, σt) : Φ.
Proof.
  intros POST. pfold. intros NT. intros.
  have WSAT1 := WSAT.
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).

  (* make a step *)
  split; [|done|].
  { right.
    edestruct NT as [[]|[es' [σs' STEPS]]]; [constructor 1|done|].
    destruct (tstep_write_inv _ _ _ _ _ _ STEPS)
      as (l&t&T&v& α' & EqH & EqH' & ? & Eqα' & EqD & IN & EQL & ?).
    symmetry in EqH, EqH'. simplify_eq.
    setoid_rewrite <-(srel_heap_dom _ _ _ WFS WFT SREL) in EqD.
    destruct SREL as (Eqst&Eqnp&Eqcs&Eqnc&AREL).
    rewrite Eqst Eqcs in Eqα'. rewrite EQL in EqD. rewrite Eqnp in IN.
    exists (#[☠])%V,
           (mkState (write_mem l v σt.(shp)) α' σt.(scs) σt.(snp) σt.(snc)).
    eapply (head_step_fill_tstep _ []), write_head_step'; eauto. }
  constructor 1. intros.
  destruct (tstep_write_inv _ _ _ _ _ _ STEPT)
      as (l&t&T&v& α' & EqH & EqH' & ? & Eqα' & EqD & IN & EQL & ?).
  symmetry in EqH, EqH'. simplify_eq.
  set σs' := mkState (write_mem l v σs.(shp)) α' σs.(scs) σs.(snp) σs.(snc).
  have STEPS: ((Place l t T <- v)%E, σs) ~{fs}~> ((#[☠])%V, σs').
  { setoid_rewrite (srel_heap_dom _ _ _ WFS WFT SREL) in EqD.
    destruct SREL as (Eqst&Eqnp&Eqcs&Eqnc&AREL).
    rewrite -Eqst -Eqcs in Eqα'. rewrite EQL in EqD. rewrite -Eqnp in IN.
    eapply (head_step_fill_tstep _ []), write_head_step'; eauto. }

  (* unfolding rrel for place *)
  simpl in RRELp. destruct RRELp as [VREL _].
  inversion VREL as [|???? ARELp U]; subst; simplify_eq. clear U VREL.
  destruct ARELp as (_ & _ & ARELp). simpl in RRELv.

  exists (#[☠])%V, σs', r, n. split; last split.
  { left. by constructor 1. }
  { destruct (for_each_lookup _ _ _ _ _ Eqα') as [EQ1 _].
    split; last split; last split; last split; last split; last split.
    - by apply (tstep_wf _ _ _ STEPS WFS).
    - by apply (tstep_wf _ _ _ STEPT WFT).
    - done.
    - (* tmap_inv *)
      intros t1 k1 h1 Eqt. simpl. specialize (PINV _ _ _ Eqt) as [Ltt1 PINV].
      split; [done|]. intros l1.

      destruct (write_mem_lookup_case l v σt.(shp) l1)
          as [[i [Lti [Eqi Eqmi]]]|[NEql Eql]]; last first.
      { (* l1 is NOT written to *)
        destruct (for_each_lookup _ _ _ _ _ Eqα') as [_ [_ EQ]].
        rewrite EQL in NEql. rewrite (EQ _ NEql) Eql.
        destruct (write_mem_lookup l v σs.(shp)) as [_ EQ2].
        rewrite -EQL in NEql. rewrite (EQ2 _ NEql).
        by apply PINV. }
      (* l1 is written to *)
      intros s1 Eqs1 stk1 Eqstk1 pm opro In1 NDIS. subst l1.
      destruct (for_each_access1 _ _ _ _ _ _ _ Eqα' _ _ Eqstk1)
        as (stk & Eqstk & SUB & ?).
      destruct (SUB _ In1) as (it2 & In2 & Eqt2 & Eqp2 & NDIS2). simpl in *.

      (* invoke PINV for t *)
      specialize (PINV _ _ Eqs1 _ Eqstk it2.(perm) opro) as [Eql' [? HTOP]].
      { rewrite /= Eqt2 Eqp2. by destruct it2. } { by rewrite (NDIS2 NDIS). }
      destruct k1.
      + (* if k1 is Unique ∧ Tagged t1 ≠ t, writing with t must have popped t1
            from top, contradicting In'. *)
        exfalso.
        rewrite EQL in Lti. destruct (EQ1 _ _ Lti Eqstk) as [ss' [Eq' EQ3]].
        have ?: ss' = stk1. { rewrite Eqstk1 in Eq'. by inversion Eq'. }
        subst ss'. clear Eq'. move : EQ3.
        case access1 as [[n1 stk2]|] eqn:EQ4; [|done].
        simpl. intros ?. simplify_eq.
        (* specialize (NEQ eq_refl). *)
        have ND := proj2 (state_wf_stack_item _ WFT _ _ Eqstk).
        move : In1.
        eapply (access1_write_remove_incompatible_head _ t t1 _ _ _ ND);
          [by eexists|done|].
        intros ?. subst t. move : Eqt.
        destruct ARELp as [h ARELp]. rewrite lookup_op ARELp.
        by apply tagKindR_exclusive_2.

      + (* if k1 is Public => t1 is for SRO, and must also have been popped,
          contradicting In1. *)
        exfalso.
        rewrite EQL in Lti. destruct (EQ1 _ _ Lti Eqstk) as [ss' [Eq' EQ3]].
        have ?: ss' = stk1. { rewrite Eqstk1 in Eq'. by inversion Eq'. }
        subst ss'. clear Eq'. move : EQ3.
        case access1 as [[n2 stk2]|] eqn:EQ4; [|done].
        simpl. intros ?. simplify_eq.
        have ND := proj2 (state_wf_stack_item _ WFT _ _ Eqstk).
        move : In1.
        eapply (access1_write_remove_incompatible_active_SRO _ t t1 _ _ _ ND); eauto.

    - (* cmap_inv : make sure tags in the new resource are still on top *)
      intros c cs Eqc. simpl. specialize (CINV _ _ Eqc).
      clear -Eqα' CINV VALID. destruct cs as [[Tc|]| |]; [|done..].
      destruct CINV as [IN CINV]. split; [done|].
      intros t1 InT. specialize (CINV _ InT) as [? CINV]. split; [done|].
      intros k h Eqt l' Inh.
      destruct (CINV _ _ Eqt _ Inh) as (stk' & pm' & Eqstk' & Instk' & NDIS).
      destruct (for_each_access1_active_preserving _ _ _ _ _ _ _ Eqα' _ _ Eqstk')
        as [stk [Eqstk AS]].
      exists stk, pm'. split; last split; [done|by apply AS|done].

    - (* srel *)
      rewrite /srel /=. destruct SREL as (?&?&?&?&PV).
      split; last split; last split; last split; [done..|].
      intros l1 InD1.
      destruct (write_mem_lookup l v σs.(shp)) as [EqN EqO].
      destruct (write_mem_lookup_case l v σt.(shp) l1)
        as [[i [Lti [Eqi Eqmi]]]|[NEql Eql]].
      + subst l1. specialize (EqN _ Lti). (* rewrite EqN. *)
        have InD := (EqD _ Lti). specialize (PV _ InD).
        destruct (lookup_lt_is_Some_2 _ _ Lti) as [s Eqs].
        (* (l +ₗ i) was written to *)
        left. intros st. simpl. intros Eqst.
        have ?: st = s. { rewrite Eqmi Eqs in Eqst. by inversion Eqst. }
        subst st. exists s. rewrite EqN. split; [done|].
        (* we know that the values written must be publicly related *)
        apply (arel_mono r _ VALID).
        { apply cmra_included_r. }
        { by apply (Forall2_lookup_lr _ _ _ _ _ _ RRELv Eqs). }
      + specialize (EqO _ NEql).
        have InD1': l1 ∈ dom (gset loc) σt.(shp)
          by rewrite elem_of_dom -Eql -(elem_of_dom (D:=gset loc)).
        specialize (PV _ InD1'). by rewrite /pub_loc EqO Eql.
    - intros l' t' Eqt'. simpl.
      specialize (LINV _ _ Eqt') as (?&Eqstk'&Eqhp'). split; last split; [done|..].
      + destruct (for_each_access1_lookup_inv _ _ _ _ _ _ _ Eqα' _ _ Eqstk')
          as (stk1 & Eqstk1 & [[n1 ACC1]|Eq1]); [|by rewrite Eq1].
        specialize (access1_in_stack _ _ _ _ _ _ ACC1)
          as (it1 & In1%elem_of_list_singleton & Eqit & ?). subst it1 t.
        destruct (tag_unique_head_access σt.(scs) (init_stack (Tagged t'))
                    (Tagged t') None AccessWrite) as [n2 Eq2]. by exists [].
        rewrite Eq2 in ACC1. by simplify_eq.
      + destruct (write_mem_lookup l v σs.(shp)) as [HLs1 HLs2].
        destruct (write_mem_lookup_case l v σt.(shp) l')
          as [[i [Lti [Eqi Eqmi]]]|[NEql Eql]].
        * subst l'. by rewrite Eqmi (HLs1 _ Lti).
        * by rewrite Eql (HLs2 _ NEql) Eqhp'. }
  left.
  apply: sim_body_result.
  intros. simpl. by eapply POST.
Qed.

(** Writing to unique/local of size 1*)

Lemma sim_body_write_unique_local_1 fs ft r r0 r' n l t T vs vt h0 σs σt Φ :
  tsize T = 1%nat →
  r ≡ r' ⋅ r0 ⋅ res_tag t tkUnique h0 →
  (r0 ≡ res_loc l 1 t ∧ vs = vt ∨ vrel (r' ⋅ r0) vs vt) →
  is_Some (h0 !! l) →
  (∀ ss st, vs = [ss] → vt = [st] →
    let σs' := mkState (<[l := ss]> σs.(shp)) σs.(sst) σs.(scs) σs.(snp) σs.(snc) in
    let σt' := mkState (<[l := st]> σt.(shp)) σt.(sst) σt.(scs) σt.(snp) σt.(snc) in
    tag_on_top σt'.(sst) l t →
    Φ (r' ⋅ (r0 ⋅ res_tag t tkUnique (<[l := st]>h0))) n (ValR [☠%S]) σs' (ValR [☠%S]) σt') →
  r ⊨{n,fs,ft}
    (Place l (Tagged t) T <- #vs, σs) ≥ (Place l (Tagged t) T <- #vt, σt) : Φ.
Proof.
  intros LenT Eqr CASE' IS POST. pfold.
  intros NT. intros.
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).

  (* inversion step *)
  split; [|done|].
  { right.
    edestruct NT as [[]|[es' [σs' STEPS]]]; [constructor 1|done|].
    destruct (tstep_write_inv _ (PlaceR _ _ _) (ValR _) _ _ _ STEPS)
      as (?&?&?&?& α' & EqH & EqH' & ? & Eqα' & EqD & IN & EQL & ?).
    symmetry in EqH, EqH'. simplify_eq.
    setoid_rewrite <-(srel_heap_dom _ _ _ WFS WFT SREL) in EqD.
    destruct SREL as (Eqst&Eqnp&Eqcs&Eqnc&AREL).
    rewrite Eqst Eqcs in Eqα'. rewrite Eqnp in IN. rewrite EQL in EqD.
    exists (#[☠])%V,
           (mkState (write_mem l vt σt.(shp)) α' σt.(scs) σt.(snp) σt.(snc)).
    eapply (head_step_fill_tstep _ []), write_head_step'; eauto.
    - destruct CASE' as [[]|VREL]; [by subst vs|].
      by rewrite -(vrel_length _ _ _ VREL).
    - destruct CASE' as [[]|VREL]; [by subst vs|].
      by apply (vrel_tag_included _ _ _ _ VREL). }
  constructor 1. intros.
  destruct (tstep_write_inv _ (PlaceR _ _ _) (ValR _) _ _ _ STEPT)
      as (?&?&?&?& α' & EqH & EqH' & ? & Eqα' & EqD & IN & EQLt & ?).
  symmetry in EqH, EqH'. simplify_eq.
  assert (∃ st, vt = [st]) as [st ?].
  { rewrite LenT in EQLt. destruct vt as [|st vt]; [simpl in EQLt; lia|].
    exists st. destruct vt; [done|simpl in EQLt; lia]. } subst vt.
  assert (∃ ss, vs = [ss] ∧ (r0 ≡ res_loc l 1 t ∧ ss = st ∨ arel (r' ⋅ r0) ss st))
    as (ss & ? & CASE).
  { destruct CASE' as [[]|VREL]; [subst vs|].
    - naive_solver.
    - inversion VREL as [|ss ??? AREL VREL']; simplify_eq.
      inversion VREL'. subst. naive_solver. } subst vs. clear CASE' EQLt.

  (* some lookup properties *)
  have VALIDr := cmra_valid_op_r _ _ VALID. rewrite ->Eqr in VALIDr.
  have HLtr: r.(rtm) !! t ≡ Some (to_tagKindR tkUnique, to_agree <$> h0).
  { rewrite Eqr.
    eapply tmap_lookup_op_unique_included;
      [apply VALIDr|apply cmra_included_r|].
    rewrite res_tag_lookup //. }
  have HLtrf: (r_f ⋅ r).(rtm) !! t ≡ Some (to_tagKindR tkUnique, to_agree <$> h0).
  { apply tmap_lookup_op_r_unique_equiv; [apply VALID|done]. }
  have HLNt: (r_f ⋅ r' ⋅ r0).(rtm) !! t = None.
  { destruct ((r_f ⋅ r' ⋅ r0).(rtm) !! t) as [ls|] eqn:Eqls; [|done].
    exfalso. move : HLtrf.
    rewrite Eqr 2!cmra_assoc lookup_op Eqls res_tag_lookup.
    apply tagKindR_exclusive_heaplet. }
  have EQrcm : (r_f ⋅ r' ⋅ r0 ⋅ res_tag t tkUnique h0).(rcm) ≡
               (r_f ⋅ r' ⋅ r0 ⋅ res_tag t tkUnique (<[l := st]>h0)).(rcm) by done.
  have EQrlm : (r_f ⋅ r' ⋅ r0 ⋅ res_tag t tkUnique h0).(rlm) ≡
               (r_f ⋅ r' ⋅ r0 ⋅ res_tag t tkUnique (<[l := st]>h0)).(rlm) by done.
  have HLtr': (r_f ⋅ r' ⋅ r0 ⋅ res_tag t tkUnique (<[l := st]>h0)).(rtm) !! t ≡
                  Some (to_tagKindR tkUnique, to_agree <$> (<[l := st]>h0)).
  { rewrite lookup_op HLNt left_id res_tag_lookup //. }

  (* Unique: stack unchanged *)
  destruct (for_each_lookup_case_2 _ _ _ _ _ Eqα') as [EQ1 _].
  specialize (EQ1 O) as (stk & stk' & Eqstk & Eqstk' & ACC1); [rewrite LenT; lia|].
  rewrite shift_loc_0_nat in Eqstk, Eqstk'.
  move : ACC1. case access1 as [[n1 stk1]|] eqn:ACC1; [|done].
  simpl. intros Eqs1. symmetry in Eqs1. simplify_eq.

  destruct IS as [s' Eqs0].

  destruct (unique_access_head _ _ _ _ _ _ _ _ _ s' _ Eqstk ACC1 PINV HLtrf)
    as (it & Eqpit & Eqti & HDi & Eqhp); [by rewrite lookup_fmap Eqs0 |].

  have ?: α' = σt.(sst).
  { move : Eqα'.
    rewrite LenT /= /memory_written /= shift_loc_0_nat Eqstk /= ACC1 /=.
    destruct (tag_unique_head_access σt.(scs) stk (Tagged t) it.(protector) AccessWrite)
      as [ns Eqss].
    - destruct HDi as [stk' Eq']. exists stk'. rewrite Eq'. f_equal.
      rewrite -Eqpit -Eqti. by destruct it.
    - rewrite ACC1 in Eqss. simplify_eq. rewrite insert_id //. by inversion 1. }
  subst α'. rewrite Eqstk in Eqstk'. symmetry in Eqstk'. simplify_eq.

  have TOT: tag_on_top σt.(sst) l t.
  { destruct HDi as [stk' Eqstk'].
    rewrite /tag_on_top Eqstk Eqstk' /= -Eqpit -Eqti. destruct it. by eexists. }

  (* source step *)
  set σs' := mkState (<[l := ss]> σs.(shp)) σs.(sst) σs.(scs) σs.(snp) σs.(snc).
  have STEPS: ((Place l (Tagged t) T <- #[ss])%E, σs) ~{fs}~> ((#[☠])%V, σs').
  { setoid_rewrite (srel_heap_dom _ _ _ WFS WFT SREL) in EqD.
    destruct SREL as (Eqst&Eqnp&Eqcs&Eqnc&AREL).
    rewrite -Eqst -Eqcs in Eqα'. rewrite -Eqnp in IN.
    eapply (head_step_fill_tstep _ []), write_head_step'; eauto.
    - destruct CASE as [[]|AREL']; [by subst ss|].
      eapply vrel_tag_included; [|eauto]. by constructor.
    - rewrite LenT //. }

  have ?: ss = st.
  { destruct CASE as [[]|]; [done|]. by eapply arel_eq. } subst ss.

  exists (#[☠])%V, σs', (r' ⋅ (r0 ⋅ res_tag t tkUnique (<[l:=st]> h0))), n.
  split; last split.
  { left. by constructor 1. }
  { rewrite 2!cmra_assoc.
    have VALID' : ✓ (r_f ⋅ r' ⋅ r0 ⋅ res_tag t tkUnique (<[l:=st]> h0)).
    { move : VALID. rewrite Eqr 2!cmra_assoc => VALID.
      apply (local_update_discrete_valid_frame _ _ _ VALID).
      by apply res_tag_insert_local_update. }

    split; last split; last split; last split; last split; last split.
    - by apply (tstep_wf _ _ _ STEPS WFS).
    - by apply (tstep_wf _ _ _ STEPT WFT).
    - done.

    (* tmap_inv *)
    - intros t1 k1 h1 HL1. simpl.
      case (decide (t1 = t)) => ?; [subst t1|].
      + specialize (PINV _ _ _ HLtrf) as [? PINV]. split; [done|].
        move : HL1. rewrite HLtr'.
        intros [Eq1 Eq2]%Some_equiv_inj. simpl in Eq1, Eq2. simplify_eq.
        intros l1 s1. rewrite -Eq2 lookup_fmap.
        case (decide (l1 = l)) => ?; [subst l1|].
        * rewrite lookup_insert. intros Eq%Some_equiv_inj%to_agree_inj.
          symmetry in Eq.
          intros stk1 Eqstk1 pm opro In1 NDIS.
          rewrite Eqstk1 in Eqstk. simplify_eq.
          split; [by rewrite lookup_insert|].
          split; [by rewrite lookup_insert|].
          specialize (PINV l s'). rewrite lookup_fmap Eqs0 in PINV.
          specialize (PINV ltac:(done) _ Eqstk1 _ _ In1 NDIS) as [? [? PINV]].
          destruct k1; [done|by inversion Eq1].

        * rewrite lookup_insert_ne // -lookup_fmap.
          intros Eq. specialize (PINV _ _ Eq).
          setoid_rewrite lookup_insert_ne; [|done..].
          destruct k1; [done|by inversion Eq1].

      + have HL': (r_f ⋅ r).(rtm) !! t1 ≡ Some (to_tagKindR k1, h1).
        { rewrite Eqr 2!cmra_assoc. move: HL1.
          rewrite lookup_op res_tag_lookup_ne //.
          rewrite (lookup_op _ (res_tag _ _ _).(rtm)) res_tag_lookup_ne //. }
        specialize (PINV _ _ _ HL') as [? PINV]. split; [done|].
        intros l1 s1 Eqs1 stk1 Eqstk1.
        case (decide (l1 = l)) => [?|NEQ];
          [subst l1; rewrite lookup_insert|rewrite lookup_insert_ne //].
        * rewrite Eqstk1 in Eqstk. simplify_eq.
          intros pm opro Instk NDIS.
          specialize (PINV _ _ Eqs1 _ Eqstk1 _ _ Instk NDIS) as [Eqs' [? HD]].
          (* t1 ≠ t, t is top of stack(l), t1 is top or SRO in stack (l).
            This cannot happen. *)
          exfalso.
          have ND := proj2 (state_wf_stack_item _ WFT _ _ Eqstk1).
          destruct k1.
          { eapply (access1_write_remove_incompatible_head _ (Tagged t) t1 _ _ _ ND);
              eauto. by inversion 1. }
          { eapply (access1_write_remove_incompatible_active_SRO _ (Tagged t) t1 _ _ _ ND);
              eauto. }

        * setoid_rewrite lookup_insert_ne; [|done]. by apply PINV.

    (* cmap_inv *)
    - intros c cs. simpl. rewrite -EQrcm. intros Eqcm.
      move : CINV. rewrite Eqr 2!cmra_assoc => CINV.
      specialize (CINV _ _ Eqcm). destruct cs as [[Tc|]| |]; [|done..].
      destruct CINV as [Inc CINV]. split; [done|].
      intros t1 Int. specialize (CINV _ Int) as [Ltt CINV]. split; [done|].
      intros k1 h1.

      case (decide (t1 = t)) => ?; [subst t1|].
      + move : HLtrf. rewrite Eqr 2!cmra_assoc. intros HLtrf.
        specialize (CINV _ _ HLtrf).
        destruct (CINV l) as (stk1 &  Hstk).
        { rewrite dom_fmap. by eapply elem_of_dom_2. }
        rewrite HLtr'. intros [Eq1 Eq2]%Some_equiv_inj. simpl in Eq1, Eq2.
        intros l1. rewrite -Eq2 fmap_insert dom_insert elem_of_union elem_of_singleton.
        intros [?|In1].
        * subst l1. by exists stk1.
        * apply (CINV l1 In1).

      + intros HL.
        have HL': (r_f ⋅ r' ⋅ r0 ⋅ res_tag t tkUnique h0).(rtm) !! t1
                  ≡ Some (k1, h1).
        { move : HL. rewrite lookup_op res_tag_lookup_ne //.
          rewrite (lookup_op _ (res_tag _ _ _).(rtm)) res_tag_lookup_ne //. }
        apply (CINV _ _ HL').

    (* srel *)
    - destruct SREL as (?&?&?&?& REL). do 4 (split; [done|]).
      simpl. intros l1 Inl1.
      case (decide (l1 = l)) => ?; [subst l1|].
      + destruct CASE as [[Eq0 ?]|AREL].
        * (* Local => Private *)
          right. eexists t, _. split. { by rewrite HLtr'. }
          left. apply lmap_lookup_op_l; [apply VALID'|].
          rewrite Eq0. apply lmap_lookup_op_r.
          { move : VALID'. rewrite Eq0. intros VAL%cmra_valid_op_l. apply VAL. }
          apply res_loc_lookup_1. simpl; lia.
        * (* Unique => Public *)
          left. intros st1. simpl. rewrite lookup_insert.
          intros Eq. symmetry in Eq. simplify_eq. exists st.
          rewrite lookup_insert. split; [done|].
          eapply arel_mono; [apply VALID'|..|exact AREL].
          etrans; [apply cmra_included_r|]. rewrite cmra_assoc.
          apply cmra_included_l.
      + move : Inl1. rewrite dom_insert elem_of_union elem_of_singleton.
        intros [?|Inl1]; [done|].
        specialize (REL _ Inl1) as [PB|[t1 PV]]; [left|right].
        * move : PB.
          rewrite Eqr 2!cmra_assoc /pub_loc /= lookup_insert_ne; [|done].
          intros PB st1 Eqst. specialize (PB _ Eqst) as (ss1 & Eqss & AREL).
          exists ss1. split; [by rewrite lookup_insert_ne|].
          move : AREL. apply arel_res_tag_overwrite.
        * exists t1. move : PV. rewrite Eqr 2!cmra_assoc /priv_loc.
          intros (h & Eqh & PV).
          case (decide (t1 = t)) => ?; [subst t|].
          { eexists. rewrite HLtr'. split; [eauto|].
            move : HLtrf. rewrite Eqr 2!cmra_assoc. rewrite Eqh.
            intros [_ Eqh']%Some_equiv_inj. simpl in Eqh'.
            destruct PV as [PV|(c & Tc & PV & ? & Inh)]; [left|right].
            - move : PV. done.
            - exists c, Tc. rewrite -EQrcm. do 2 (split; [done|]).
              rewrite fmap_insert dom_insert elem_of_union -Eqh'. by right. }
          { exists h. setoid_rewrite EQrcm. split; [|destruct PV as [PB|PV]].
            - move : Eqh.
              rewrite lookup_op res_tag_lookup_ne; [|done].
              rewrite (lookup_op _ (res_tag _ _ _).(rtm)) res_tag_lookup_ne //.
            - left. move : PB. done.
            - by right. }

    (* lmap_inv *)
    - move : LINV. rewrite Eqr 2!cmra_assoc.
      intros LINV l1 t1 Eq1. simpl. specialize (LINV l1 t1 Eq1) as (?&?&?).
      do 2 (split; [done|]).
      case (decide (l1 = l)) => [->|?];
        [rewrite 2!lookup_insert //|rewrite lookup_insert_ne// lookup_insert_ne//]. }

  left. apply: sim_body_result.
  intros. simpl. by apply POST.
Qed.

(** Writing to local of size 1 *)
Lemma sim_body_write_local_1 fs ft r r' n l tg T v v' σs σt Φ :
  tsize T = 1%nat →
  r ≡ r' ⋅ res_mapsto l [v'] tg →
  (∀ s, v = [s] →
    let σs' := mkState (<[l := s]> σs.(shp)) σs.(sst) σs.(scs) σs.(snp) σs.(snc) in
    let σt' := mkState (<[l := s]> σt.(shp)) σt.(sst) σt.(scs) σt.(snp) σt.(snc) in
    Φ (r' ⋅ res_mapsto l [s] tg) n
      (ValR [☠%S]) σs' (ValR [☠%S]) σt') →
  r ⊨{n,fs,ft}
    (Place l (Tagged tg) T <- #v, σs) ≥ (Place l (Tagged tg) T <- #v, σt) : Φ.
Proof.
  intros LenT Eqr POST.
  eapply sim_body_write_unique_local_1; [done| |by left|..].
  - rewrite Eqr /res_mapsto cmra_assoc /= insert_empty; eauto.
  - rewrite lookup_insert. by eexists.
  - intros. rewrite insert_insert insert_empty. naive_solver.
Qed.

(** Writing to owned (unique) location *)
Lemma sim_body_write_unique_1
  fs ft (r r' r'' rs: resUR) n l h tg T s σs σt Φ:
  tsize T = 1%nat →
  r ≡ r' ⋅ res_tag tg tkUnique h →
  is_Some (h !! l) →
  arel rs s s → (* assuming to-write values are related *)
  r' ≡ r'' ⋅ rs →
  (let σs' := mkState (write_mem l [s] σs.(shp)) σs.(sst) σs.(scs) σs.(snp) σs.(snc) in
   let σt' := mkState (write_mem l [s] σt.(shp)) σt.(sst) σt.(scs) σt.(snp) σt.(snc) in
    tag_on_top σt'.(sst) l tg →
    Φ (r' ⋅ res_tag tg tkUnique (<[l:=s]> h)) n (ValR [☠]%S) σs' (ValR [☠]%S) σt') →
  r ⊨{n,fs,ft}
    (Place l (Tagged tg) T <- #[s], σs) ≥ (Place l (Tagged tg) T <- #[s], σt) : Φ.
Proof.
  intros Hs Hr IS AREL Hr' POST.
  eapply (sim_body_bind _ _ [] _ []).
  eapply sim_body_valid. intros VALID.
  eapply sim_body_write_unique_local_1; [done|..].
  - rewrite Hr Hr'; eauto.
  - right. constructor; [|constructor].
    eapply arel_mono; [..|apply cmra_included_r|exact AREL].
    move : VALID. rewrite Hr Hr'. apply cmra_valid_op_l.
  - done.
  - intros. rewrite cmra_assoc -Hr'.
    apply : sim_body_result. intros. simplify_eq. eapply POST; eauto.
Qed.

(** Retag *)

Lemma sim_body_retag_local_mut_ref fs ft r r' r'' n x xt xs xs' rs T σs σt Φ :
  (0 < tsize T)%nat →
  (* owns local x with tag xt and value xs *)
  r ≡ r' ⋅ res_mapsto x [xs] xt →
  (* xs is supposed to be a Ptr(li,told), and, coming from the arguments, told
    must be a public tag. *)
  arel rs xs' xs →
  r' ≡ r'' ⋅ rs →
  let Tr := (Reference (RefPtr Mutable) T) in
  (∀ li told,
    xs = ScPtr li told →
    ∀ tnew hplt c cids hs' αs' nps' ht' αt' npt' (STACK: σt.(scs) = c :: cids),
    retag σt.(shp) σt.(sst) σt.(snp) σt.(scs) c x Default Tr
      = Some (ht', αt', npt') →
    retag σs.(shp) σs.(sst) σs.(snp) σs.(scs) c x Default Tr
      = Some (hs', αs', nps') →
    let σs' := mkState hs' αs' σs.(scs) nps' σs.(snc) in
    let σt' := mkState ht' αt' σt.(scs) npt' σt.(snc) in
    let s_new := ScPtr li (Tagged tnew) in
    let tk := tkUnique in
    is_Some (hplt !! li) →
    tag_on_top αt' li tnew →
    Φ (r'' ⋅ rs ⋅ res_mapsto x [s_new] xt ⋅ res_tag tnew tk hplt)
      n (ValR [☠%S]) σs' (ValR [☠%S]) σt') →
  r ⊨{n,fs,ft}
    (Retag (Place x (Tagged xt) Tr) Default, σs) ≥
    (Retag (Place x (Tagged xt) Tr) Default, σt) : Φ.
Proof.
  intros NZST Eqr PTag Eqr' Tr POST. pfold. intros NT. intros.
  have WSAT1 := WSAT. (* back up *)

  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  destruct SREL as (Eqsst & Eqnp & Eqcs & Eqnc & PUBP).
  (* some lookup properties *)
  have VALIDr := cmra_valid_op_r _ _ VALID. rewrite ->Eqr in VALIDr.
  have HLxtr: r.(rtm) !! xt ≡ Some (to_tagKindR tkUnique, {[x := to_agree xs]}).
  { rewrite Eqr. eapply tmap_lookup_op_unique_included;
                  [apply VALIDr|apply cmra_included_r|].
    rewrite res_mapsto_tlookup // fmap_insert fmap_empty //. }
  have HLxtrf:
    (r_f ⋅ r).(rtm) !! xt ≡ Some (to_tagKindR tkUnique, {[x := to_agree xs]}).
  { apply tmap_lookup_op_r_unique_equiv; [apply VALID|done]. }
  have HLNxt: (r_f ⋅ r'' ⋅ rs).(rtm) !! xt = None.
  { destruct ((r_f ⋅ r'' ⋅ rs).(rtm) !! xt) as [ls|] eqn:Eqls; [|done].
    exfalso. move : HLxtrf.
    rewrite Eqr Eqr' cmra_assoc (cmra_assoc r_f) lookup_op Eqls res_mapsto_tlookup.
    apply tagKindR_exclusive_heaplet. }
  have HLxlr : (r.(rlm) !! x : optionR tagR) ≡ Some (to_tagR xt).
  { rewrite Eqr. apply lmap_lookup_op_r; [apply VALIDr|].
    rewrite (res_mapsto_llookup_1 x [xs]); [done|by simpl;lia]. }
  have HLxlrf: ((r_f ⋅ r).(rlm) !! x : optionR tagR) ≡ Some (to_tagR xt).
  { apply lmap_lookup_op_r; [apply VALID|done]. }

  (* xt is the head of x's stack *)
  destruct (LINV _ _ HLxlrf) as (Ltxt & Eqst & Eqhpl).
  destruct (PINV _ _ _ HLxtrf) as [_ Pxt]. specialize (Pxt x xs).
  rewrite lookup_insert in Pxt.
  specialize (Pxt ltac:(done) _ Eqst Unique None) as (Eqhs & _ & HD).
  { by rewrite elem_of_list_singleton. } { done. }

  split; [|done|].
  { (* tgt reducible *)
    right.
    edestruct NT as [[]|[es' [σs' STEPS]]]; [constructor 1|done|].
    (* inversion retag of src *)
    destruct (tstep_retag_inv _ _ _ _ _ _ _ _ _ STEPS)
      as (c & cids & h' & α' & nxtp' & Eqs & EqT & ? & ?). subst es'.
    apply retag_ref_change in EqT as (l & to & Eqx' & Eqh' & Eqp' & RB); [|done..].
    subst h' nxtp'. rewrite Eqhs Eqx' in Eqhpl. simplify_eq.
    rewrite Eqsst Eqcs Eqnp in RB. rewrite Eqcs in Eqs.
    (* retag of tgt *)
    exists (#[☠])%V,
      (mkState (<[x:=ScPtr l (Tagged σt.(snp))]> σt.(shp)) α' σt.(scs) (S σt.(snp)) σt.(snc)).
    eapply (head_step_fill_tstep _ []), retag1_head_step'; [eauto|].
    eapply retag_ref_reborrowN; eauto. }
  constructor 1.
  intros.

  (* inversion retag of tgt *)
  destruct (tstep_retag_inv _ _ _ _ _ _ _ _ _ STEPT)
      as (c & cids & h' & α' & nxtp' & Eqs & EqT & ? & ?). subst et'.
  apply retag_ref_change in EqT as (li & to & Eqx' & Eqh' & Eqp' & RB); [|done..].
  subst h' nxtp'. rewrite Eqhs in Eqx'. simplify_eq. simpl in RB.
  set tn := σt.(snp).
  set tk := tkUnique.

  (* new heaplet *)
  have InDli: ∀ i, (i < tsize T)%nat → li +ₗ i ∈ dom (gset loc) σt.(shp).
  { intros i Lti. rewrite (state_wf_dom _ WFT).
    destruct (for_each_lookup_case_2 _ _ _ _ _ RB) as [EQ1 _].
    specialize (EQ1 _ Lti) as (? & ? & In1 & _). by eapply elem_of_dom_2. }
  assert (∃ vl, read_mem li (tsize T) σt.(shp) = Some vl) as [vl Eqvl]
    by apply (read_mem_is_Some _ _ _ InDli).
  set hplt : heaplet := write_mem li vl ∅.

  set σs' :=
    (mkState (<[x:=ScPtr li (Tagged σs.(snp))]> σs.(shp)) α' σs.(scs) (S σs.(snp)) σs.(snc)).

  have RETAGt :
    retag σt.(shp) σt.(sst) σt.(snp) σt.(scs) c x Default (&mut T) =
      Some (<[x:=ScPtr li (Tagged σt.(snp))]> σt.(shp), α', S σt.(snp)).
  { eapply retag_ref_reborrowN; eauto. }
  have RETAGs :
    retag σs.(shp) σs.(sst) σs.(snp) σs.(scs) c x Default (&mut T) =
      Some (<[x:=ScPtr li (Tagged σs.(snp))]> σs.(shp), α', S σs.(snp)).
  { rewrite -Eqsst -Eqcs -Eqnp in RB. rewrite -Eqcs in Eqs.
    eapply retag_ref_reborrowN; eauto. by rewrite -Eqhpl. }

  (* src makes a step *)
  have STEPS: (Retag (Place x (Tagged xt) Tr) Default, σs) ~{fs}~> ((#[☠])%V, σs').
  { rewrite -Eqsst -Eqcs -Eqnp in RB. rewrite -Eqcs in Eqs.
    eapply (head_step_fill_tstep _ []), retag1_head_step'; eauto. }

  exists (#[☠])%V, σs'.
  exists (r'' ⋅ rs ⋅ res_mapsto x [ScPtr li (Tagged tn)] xt ⋅ res_tag tn tk hplt), n.
  split; last split.
  { left. by apply tc_once. }
  { rewrite 2!cmra_assoc (cmra_assoc r_f).
    split; last split; last split; last split; last split; last split.
    - by apply (tstep_wf _ _ _ STEPS WFS).
    - by apply (tstep_wf _ _ _ STEPT WFT).
    - admit.
    - admit.
    - admit.
    - admit.
    - admit. }

  left. apply : sim_body_result. intros. simplify_eq. eapply POST; eauto.
  - destruct (read_mem_values _ _ _ _ Eqvl) as [Eqlv Eqhp].
    destruct (write_mem_lookup li vl ∅) as [EQ1 _].
    specialize (EQ1 O). rewrite Eqlv shift_loc_0_nat in EQ1.
    rewrite (EQ1 NZST). apply lookup_lt_is_Some_2. by rewrite Eqlv.
  - (* tag on top as result of retagging Unique *)
    eapply tag_on_top_reborrowN; [|eauto]. done.
Admitted.


(** InitCall *)
Lemma sim_body_init_call fs ft r n es et σs σt Φ :
  let σs' := mkState σs.(shp) σs.(sst) (σs.(snc) :: σs.(scs)) σs.(snp) (S σs.(snc)) in
  let σt' := mkState σt.(shp) σt.(sst) (σt.(snc) :: σt.(scs)) σt.(snp) (S σt.(snc)) in
  let r'  : resUR := res_callState σt.(snc) (csOwned ∅) in
  (σs'.(scs) = σt'.(scs) →
    r ⋅ r' ⊨{n,fs,ft} (es, σs') ≥ (et, σt') : Φ) →
  r ⊨{n,fs,ft} (InitCall es, σs) ≥ (InitCall et, σt) : Φ.
Proof.
  intros σs' σt1 r' SIM. pfold.
  intros NT. intros. split; [|done|].
  { right. do 2 eexists. by eapply (head_step_fill_tstep _ []), initcall_head_step. }
  constructor 1. intros.
  exists es, σs', (r ⋅ r').
  destruct (tstep_init_call_inv _ _ _ _ _ STEPT). subst et' σt'.
  have STEPS: (InitCall es, σs) ~{fs}~> (es, σs').
  { by eapply (head_step_fill_tstep _ []), initcall_head_step. }
  have FRESH: (r_f ⋅ r).(rcm) !! σt.(snc) = None.
  { destruct ((r_f ⋅ r).(rcm) !! σt.(snc)) as [cs|] eqn:Eqcs; [|done].
    exfalso. destruct WSAT as (WFS & WFT & ? & ? & CINV & ?).
    apply (lt_irrefl σt.(snc)), (cinv_lookup_in_eq _ _ _ _ WFT CINV Eqcs). }
  have LOCAL: (r_f ⋅ r ⋅ ε, ε) ~l~> (r_f ⋅ r ⋅ r', r').
  { apply prod_local_update_1, prod_local_update_2.
    rewrite /= right_id (comm _ (_ ⋅ _)) -insert_singleton_op //.
    by apply alloc_singleton_local_update. }
  have ANNOYING: scs σs' = scs σt1.
  { simpl. destruct WSAT as (_ & _ & _ & _ & _ & SREL & _).
    destruct SREL as (?&?&->&->&?). done. }

  exists n. split; last split; cycle 2.
  { (* sim cont *)  specialize (SIM ANNOYING). punfold SIM. }
  { (* STEP src *)  left. by apply tc_once. }
  (* WSAT new *)
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  rewrite assoc.
  have VALID': ✓ (r_f ⋅ r ⋅ r').
  { apply (local_update_discrete_valid_frame (r_f ⋅ r) ε r'); [|done].
    by rewrite right_id. }
  split; last split; last split; last split; last split; last split.
  { (* WF src *)    by apply (tstep_wf _ _ _ STEPS WFS). }
  { (* WF tgt *)    by apply (tstep_wf _ _ _ STEPT WFT). }
  { (* VALID *)     done. }
  { (* tmap_inv *)  move => t k h /=. rewrite /rtm /= right_id. apply PINV. }
  { (* cmap_inv *)
    intros c cs.
    rewrite /rcm /= (comm _ (r_f.(rcm) ⋅ r.(rcm))) -insert_singleton_op //.
    case (decide (c = σt.(snc))) => [->|NE].
    - rewrite lookup_insert. intros Eqcs%Some_equiv_inj.
      inversion Eqcs as [?? Eq| |]; subst. inversion Eq as [?? Eq2|] ; subst.
      split; [by left|]. intros ? IN. exfalso. move : IN.
      by rewrite -Eq2 elem_of_empty.
    - rewrite lookup_insert_ne // => /CINV. destruct cs as [[]| |]; [|done|lia|done].
      intros [? Ht]. split; [by right|].
      setoid_rewrite (right_id _ _ (r_f.(rtm) ⋅ r.(rtm))). naive_solver. }
  { (* srel *)
    destruct SREL as (?&?&?&?&SREL).
    do 2 (split; [done|]). do 2 (split; [simpl; by f_equal|]). simpl.
    intros l InD.
    destruct (SREL _ InD) as [PUB|(t & h & Eqh & LOC)]; [left|right].
    - move => st /= /PUB [ss [Eqss AREL]]. exists ss. split; [done|].
      eapply arel_mono; [apply VALID'| |eauto]. apply cmra_included_l.
    - exists t, h. split.
      { apply tmap_lookup_op_l_unique_equiv; [apply VALID'|done]. }
      destruct LOC as [LOC|(c & T & Eqc & ?)]; [left|right].
      + apply lmap_lookup_op_l; [apply VALID'|done].
      + exists c, T. split; [|done].
        apply cmap_lookup_op_l_equiv; [apply VALID'|done]. }
  { intros ?. rewrite /=. rewrite right_id_L.
    have Eqrtm: (r_f ⋅ r ⋅ r').(rtm) ≡ (r_f ⋅ r).(rtm) by rewrite /rtm /= right_id.
    apply LINV. }
Qed.

(** EndCall *)
Lemma end_call_tstep_src_tgt fs ft r_f r σs σt (rs rt: result) es' σs' :
  rrel r rs rt →
  wsat (r_f ⋅ r) σs σt →
  (EndCall rs, σs) ~{fs}~> (es', σs') →
  ∃ vs vt : value, rs = ValR vs ∧ rt = ValR vt ∧ reducible ft (EndCall rt) σt.
Proof.
  intros RREL WSAT STEPS.
  edestruct (tstep_end_call_inv _ rs _ _ _ (ltac:(rewrite to_of_result; by eexists))
                STEPS) as (vs & Eqvs & ? & c & cids & Eqc & Eqs).
  subst. simpl in Eqvs. symmetry in Eqvs. simplify_eq.
  destruct WSAT as (?&?&?&?&?&SREL&?). destruct SREL as (? & ? & Eqcs' & ?).
  rewrite to_of_result in Eqvs. simplify_eq.
  destruct rt as [vt|]; [|done].
  exists vs, vt. do 2 (split; [done|]).
  exists (#vt)%E, (mkState σt.(shp) σt.(sst) cids σt.(snp) σt.(snc)).
  eapply (head_step_fill_tstep _ []).
  econstructor. by econstructor. econstructor. by rewrite -Eqcs'.
Qed.

Lemma sim_body_end_call fs ft r n rs rt σs σt Φ :
  (* return values are related *)
  rrel r rs rt →
  (* The top of the call stack has no privately protected locations left *)
  (∃ c cids, σt.(scs) = c :: cids ∧ end_call_sat r c) →
  (∀ c1 c2 cids1 cids2 vs vt,
      σs.(scs) = c1 :: cids1 → σt.(scs) = c2 :: cids2 →
      rs = ValR vs → rt = ValR vt →
      let σs' := mkState σs.(shp) σs.(sst) cids1 σs.(snp) σs.(snc) in
      let σt' := mkState σt.(shp) σt.(sst) cids2 σt.(snp) σt.(snc) in
      Wf σt →
      Φ r n rs σs' rt σt' : Prop) →
  r ⊨{n,fs,ft} (EndCall (of_result rs), σs) ≥ (EndCall (of_result rt), σt) : Φ.
Proof.
  intros VREL ESAT POST. pfold. intros NT r_f WSAT.
  split; [|done|].
  { right.
    destruct (NT (EndCall rs) σs) as [[]|[es' [σs' STEPS]]]; [done..|].
    eapply (end_call_tstep_src_tgt fs ft r_f r) in STEPS as (?&?&?&?&?); eauto. }
  constructor 1. intros et' σt' STEPT.
  destruct (tstep_end_call_inv ft (of_result rt) et' σt σt'
              (ltac:(rewrite to_of_result; by eexists)) STEPT)
    as (vt' & Eqvt & ? & c & cids & Eqc & Eqs).
  subst. rewrite to_of_result in Eqvt. simplify_eq.
  rewrite /end_call_sat Eqc in ESAT.
  destruct ESAT as [c' [cs [Eqcs ESAT]]]. symmetry in Eqcs. simplify_eq.
  set σs' := (mkState σs.(shp) σs.(sst) cids σs.(snp) σs.(snc)).
  destruct rs as [vs|]; [|done].
  have STEPS: (EndCall #vs, σs) ~{fs}~> ((#vs)%E, σs').
  { destruct WSAT as (?&?&?&?&?&SREL&?). destruct SREL as (? & ? & Eqcs' & ?).
    eapply (head_step_fill_tstep _ []).
    econstructor. by econstructor. econstructor. by rewrite Eqcs'. }
  exists (Val vs), σs', r, n.
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  split; last split.
  { left. by constructor 1. }
  { split; last split; last split; last split; last split; last split.
    - by apply (tstep_wf _ _ _ STEPS WFS).
    - by apply (tstep_wf _ _ _ STEPT WFT).
    - done.
    - done.
    - intros c1 cs1 Eqcs1. simpl.
      case (decide (c1 = c)) => [?|NEqc].
      + subst c1.
        have VALID1: ✓ cs1. { rewrite -Some_valid -Eqcs1. apply VALID. }
        destruct cs1 as [[T|]| |]; [|done| |done]; last first.
        { apply (state_wf_cid_agree _ WFT). rewrite Eqc. by left. }
        (* TODO: move out *)
        exfalso. move : Eqcs1. rewrite lookup_op ESAT. apply callStateR_exclusive_2.
      + move : (CINV _ _ Eqcs1). clear -NEqc Eqc.
        destruct cs1 as [[T|]| |]; [|done..]. rewrite Eqc.
        move => [/elem_of_cons IN ?]. split; [|done].
        destruct IN; [by subst|done].
    - by destruct SREL as (Eqst & Eqnp & Eqcs' & Eqnc & Eqhp).
    - done. }
  (* result *)
  left. apply: sim_body_result.
  intros VALID'.
  eapply POST; eauto. destruct SREL as (?&?&Eqs&?). by rewrite Eqs.
Qed.

Lemma sim_body_end_call_elim' fs ft r n (rs rt: result) σs σt Φ :
  r ⊨{n,fs,ft} (EndCall rs, σs) ≥ (EndCall rt, σt) : Φ →
  ∀ r_f et' σt' (WSAT: wsat (r_f ⋅ r) σs σt)
    (NT: never_stuck fs (EndCall rs) σs)
    (STEPT: (EndCall rt, σt) ~{ft}~> (et', σt')),
  ∃ r' n' σs' vs vt, (EndCall rs, σs) ~{fs}~>+ (Val vs, σs') ∧ et' = Val vt ∧
    Φ r' n' (ValR vs) σs' (ValR vt) σt' ∧
    wsat (r_f ⋅ r') σs' σt'.
Proof.
  intros SIM r_f et' σt' WSAT NT STEPT.
  punfold SIM.
  specialize (SIM NT _ WSAT) as [NOSK TERM STEPSS].
  inversion STEPSS; last first.
  { exfalso. clear -CALLTGT. symmetry in CALLTGT.
    apply fill_end_call_decompose in CALLTGT as [[]|[K' [? Eq]]]; [done|].
    destruct (fill_result ft K' (Call #[ScFnPtr fid] (of_result <$> vl_tgt))) as [[] ?];
      [rewrite Eq to_of_result; by eexists|done]. }
  specialize (STEP _ _ STEPT) as (es1 & σs1 & r1 & n1 & STEP1 & WSAT1 & SIMV).
  have STEPK: (EndCall rs, σs) ~{fs}~>* (es1, σs1).
  { destruct STEP1 as [|[]]. by apply tc_rtc. by simplify_eq. }
  have NT1 := never_stuck_tstep_rtc _ _ _ _ _ STEPK NT.
  pclearbot. punfold SIMV.
  specialize (SIMV NT1 _ WSAT1) as [ST1 TE1 STEPS1].
  apply tstep_end_call_inv in STEPT as (vt & Eq1 &? & ? & ? & ? & ?);
        [|by rewrite to_of_result; eexists].
  rewrite to_of_result /= in Eq1. simplify_eq.
  specialize (TE1 vt eq_refl) as (rs2 & σs2 & r2 & STEP2 & WSAT2 & POST).
  exists r2, n1, σs2.
  assert (rs2 = rs ∧ ∃ vs, (EndCall rs, σs) ~{fs}~>+ ((#vs)%E, σs2) ∧ rs = ValR vs)
    as [? [vs [??]]].
  { clear -STEP1 STEP2.
    destruct STEP1 as [STEP1|[Eq11 Eq12]]; [|simplify_eq].
    - have STEP1' := STEP1.
       apply tstep_end_call_inv_tc in STEP1 as (vs & Eq1 &? & ? & ? & ? & ?);
        [|by rewrite to_of_result; eexists]. simplify_eq.
      apply result_tstep_rtc in STEP2 as [Eq3 Eq4]; [|by eexists].
      rewrite to_of_result in Eq1. simplify_eq.
      have Eq := to_of_result rs2.
      rewrite Eq3 /to_result in Eq. simplify_eq. naive_solver.
    - inversion STEP2 as [x1 x2 Eq2|x1 [] x3 STEP3 STEP4]; simplify_eq.
      + by destruct rs, rs2.
      + have STEP3' := STEP3.
        apply tstep_end_call_inv in STEP3 as (v1 & Eq1 &? & ? & ? & ? & ?);
          [|by rewrite to_of_result; eexists]. simplify_eq.
        apply result_tstep_rtc in STEP4 as [Eq3 Eq4]; [|by eexists].
        rewrite to_of_result in Eq1. simplify_eq.
        have Eq := to_of_result rs2. rewrite Eq3 /to_result in Eq.
        simplify_eq. split; [done|]. eexists. split; [|done]. by apply tc_once. }
  subst. simpl. by exists vs, vt.
Qed.

End mem.
