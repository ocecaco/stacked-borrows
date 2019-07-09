From iris.algebra Require Import local_updates.

From stbor.lang Require Import steps_progress steps_inversion steps_retag.
From stbor.sim Require Export instance body.

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

Lemma repeat_lookup_lt_length `{A: Type} (a: A) (n: nat) :
  ∀ i, (i < n)%nat → repeat a n !! i = Some a.
Proof.
  induction n as [|n IH]; intros i Lt; [lia|]; simpl.
  destruct i as [|i]; [done|]. simpl. apply IH. lia.
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
          rewrite (HLst1 _ Lti) (HLmt1 _ Lti). intros stk ?. simplify_eq.
          intros pm opro ?%elem_of_list_singleton ?. simplify_eq.
          split; [done|]. destruct k1. by eexists. by inversion Eqk1.
        * rewrite Eql1 lookup_empty. inversion 1.
      + intros Eqh'.
        have Eqh1: (r_f ⋅ r).(rtm) !! t1 ≡ Some (to_tagKindR k1, h1).
        { move : Eqh'. rewrite lookup_op res_mapsto_tlookup_ne // right_id //. }
        specialize (PINV _ _ _ Eqh1) as [? PINV]. split; [simpl; lia|].
        intros l1 s1 Eqs1 stk Eqstk.
        destruct (init_stacks_lookup_case _ _ _ _ _ _ Eqstk)
          as [[Eql1 NEQl1]|(i & (? & Lti) & Eql1)].
        * rewrite (HLmt2 _ NEQl1). by apply PINV.
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

(** Alloc *)
(* 
Lemma sim_body_alloc_shared fs ft r n T σs σt Φ :
  let ls := (fresh_block σs.(shp), 0) in
  let lt := (fresh_block σt.(shp), 0) in
  let ts := (Tagged σs.(snp)) in
  let tgt := (Tagged σt.(snp)) in
  let σs' := mkState (init_mem ls (tsize T) σs.(shp))
                     (init_stacks σs.(sst) ls (tsize T) ts) σs.(scs)
                     (S σs.(snp)) σs.(snc) in
  let σt' := mkState (init_mem lt (tsize T) σt.(shp))
                     (init_stacks σt.(sst) lt (tsize T) tgt) σt.(scs)
                     (S σt.(snp)) σt.(snc) in
  let r' : resUR :=
    (({[σt.(snp) := (to_tagKindR tkUnique, to_heapletR $ init_mem lt (tsize T) ∅)]},
        ε), ε) in
  (ls = lt → ts = tgt →
    Φ (r ⋅ r') n (PlaceR ls ts T) σs' (PlaceR lt tgt T) σt' : Prop) →
  r ⊨{n,fs,ft} (Alloc T, σs) ≥ (Alloc T, σt) : Φ.
Proof.
  intros ls lt ts tgt σs' σt' r' POST.
  pfold. intros NT. intros.
  have EqDOM := wsat_heap_dom _ _ _ WSAT.
  have EqFRESH := fresh_block_equiv _ _ EqDOM.
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  have Eqnp : σs.(snp) = σt.(snp). { by destruct SREL as (?&?&?&?). }
  have Eqlst: ls = lt. { by rewrite /ls /lt EqFRESH. }
  split; [|done|].
  { right. do 2 eexists. by eapply (head_step_fill_tstep _ []), alloc_head_step. }
  constructor 1. intros ? σt1 STEPT.
  destruct (tstep_alloc_inv _ _ _ _ _ STEPT) as [? Eqσt'].
  rewrite -/σt' in Eqσt'. subst et' σt1.
  have STEPS: (Alloc T, σs) ~{fs}~>
              (Place (fresh_block σs.(shp), 0) (Tagged σs.(snp)) T, σs').
  { subst ls σs' ts. eapply (head_step_fill_tstep _ []), alloc_head_step. }
  eexists _, σs', (r ⋅ r'), (S n). split; last split.
  { left. by apply tc_once. }
  { have HLF : (r_f ⋅ r).(rtm) !! σt.(snp) = None.
    { destruct ((r_f ⋅ r).(rtm) !! σt.(snp)) as [[k h]|] eqn:Eqkh; [|done]. exfalso.
      destruct (tagKindR_valid k) as [k' Eqk'].
      { apply (Some_valid (k,h)). rewrite -Some_valid -Eqkh. apply VALID. }
      destruct (PINV σt.(snp) k' h) as [Lt _]; [by rewrite Eqkh Eqk'|lia]. }
    have VALID': ✓ (r_f ⋅ r ⋅ r').
    { apply (local_update_discrete_valid_frame _ ε r'); [by rewrite right_id|].
      do 2 apply prod_local_update_1. rewrite /= right_id.
      rewrite -(cmra_comm _ (r_f.(rtm) ⋅ r.(rtm))) -insert_singleton_op //.
      apply alloc_singleton_local_update; [done|]. split; [done|].
      by apply to_heapletR_valid. }
    have INCL: r_f ⋅ r ≼ r_f ⋅ r ⋅ r' by apply cmra_included_l.
    rewrite cmra_assoc.
    destruct (init_mem_lookup ls (tsize T) σs.(shp)) as [HLs1 HLs2].
    destruct (init_mem_lookup lt (tsize T) σt.(shp)) as [HLt1 HLt2].
    split; last split; last split; last split; last split; last split.
    - by apply (tstep_wf _ _ _ STEPS WFS).
    - by apply (tstep_wf _ _ _ STEPT WFT).
    - done.
    - intros t k h. rewrite lookup_op.
      case (decide (t = σt.(snp))) => ?; [subst t|].
      + rewrite /= lookup_insert HLF left_id.
        intros [Eq1 Eq2]%Some_equiv_inj. simpl in Eq1, Eq2. split; [lia|].
        intros l s. rewrite -Eq2. intros Eqs stk Eqstk pm opro Instk NDIS.
        (* l is new memory *)
        apply to_heapletR_lookup in Eqs.
        destruct (init_mem_lookup_empty _ _ _ _ Eqs) as [i [[? Lti] Eql]].
        have Eqi: Z.of_nat (Z.to_nat i) = i by rewrite Z2Nat.id.
        have Lti': (Z.to_nat i < tsize T)%nat by rewrite Nat2Z.inj_lt Eqi.
        have ?: s = ScPoison.
        { rewrite Eql -Eqi in Eqs.
          rewrite (proj1 (init_mem_lookup lt (tsize T) ∅)) // in Eqs.
          by inversion Eqs. } subst s.
        have Eqs2 := HLt1 _ Lti'. rewrite Eqi -Eql in Eqs2. split; [done|].
        destruct k; [|by inversion Eq1].
        have Eqstk2 := proj1 (init_stacks_lookup σt.(sst) lt (tsize T) tgt) _ Lti'.
        rewrite Eqi -Eql Eqstk in Eqstk2.
        exists []. move : Instk. inversion Eqstk2.
        rewrite elem_of_list_singleton. by inversion 1.
      + rewrite lookup_insert_ne // right_id. intros Eqkh.
        specialize (PINV t k h Eqkh) as [Lt PINV].
        split. { etrans; [exact Lt|simpl; lia]. }
        intros l s Eqs stk Eqstk pm opro Instk NDIS.
        specialize (PINV l s Eqs).
        destruct (init_stacks_lookup_case _ _ _ _ _ _ Eqstk)
          as [[EqstkO Lti]|[i [[? Lti] Eql]]].
        * specialize (PINV _ EqstkO _ _ Instk NDIS) as [Eqss PINV].
          rewrite /= HLt2 //.
        * exfalso. move : Eqstk. simpl.
          destruct (init_stacks_lookup σt.(sst) lt (tsize T) tgt) as [EQ _].
          have Lti': (Z.to_nat i < tsize T)%nat by rewrite Nat2Z.inj_lt Z2Nat.id //.
          specialize (EQ _ Lti'). rewrite Z2Nat.id // in EQ. rewrite Eql EQ.
          intros. inversion Eqstk. clear Eqstk. subst stk.
          move : Instk. rewrite elem_of_list_singleton. by inversion 1.
    - intros c cs. rewrite /rcm /= right_id => /CINV.
      destruct cs as [[T0|]| |]; [|done..]. intros [InT Eqh].
      split; [done|]. intros t2 InT2. specialize (Eqh t2 InT2) as [Lt2 Eqh].
      split; [lia|]. intros k2 h2. rewrite lookup_op.
      case (decide (t2 = σt.(snp))) => ?; [subst t2|]; [exfalso; by lia|].
      rewrite lookup_insert_ne // right_id.
      intros Eqh2 l Inl.
      specialize (Eqh _ _ Eqh2 l Inl) as (stk & pm & Eqsk & Instk).
      destruct (init_stacks_lookup_case_2 _ lt (tsize T) tgt _ _ Eqsk)
        as [[EqO NIn]|[i [[? Lti] [Eqi EqN]]]].
      + exists stk, pm. by rewrite EqO.
      + exfalso. apply (is_fresh_block σt.(shp) i).
        rewrite (state_wf_dom _ WFT). apply elem_of_dom. exists stk.
        rewrite (_: (fresh_block (shp σt), i) = lt +ₗ i) //.
        by rewrite -Eqi.
    - destruct SREL as (Eqst&_&Eqcs&Eqnc&VREL).
      repeat split; simpl; [|auto..|].
      { subst σs' σt' ls lt ts tgt. by rewrite Eqst EqFRESH Eqnp. }
      intros l st HL.
      destruct (init_mem_lookup_case _ _ _ _ _ HL) as [[EqO NIn]|[i [[? Lti] Eqi]]].
      + rewrite -Eqlst in NIn. rewrite (HLs2 _ NIn).
        specialize (VREL _ _ EqO) as [[ss [? AREL]]|[t PV]].
        * left. exists ss. split; [done|]. move : AREL. by apply arel_mono.
        * right. exists t. move : PV. by apply priv_loc_mono.
      + left. exists ☠%S.
        have Lti': (Z.to_nat i < tsize T)%nat by rewrite Nat2Z.inj_lt Z2Nat.id //.
        specialize (HLt1 _ Lti').
        rewrite Z2Nat.id // -Eqi HL in HLt1.
        specialize (HLs1 _ Lti'). rewrite -Eqlst in Eqi.
        rewrite Z2Nat.id // -Eqi in HLs1. split; [done|by inversion HLt1].
    - intros ???. rewrite /lmap_inv /= right_id. intros IN.
      specialize (LINV _ _ _ IN) as [Eq1 Eq2].
      have ?: ∀ i : nat, (i < tsize T)%nat → l ≠ lt +ₗ i.
      { intros i Lt Eq. apply (is_fresh_block σt.(shp) i), elem_of_dom.
        exists s. rewrite (_ : (fresh_block σt.(shp), Z.of_nat i) = l) //. }
      rewrite HLt2 // HLs2 // Eqlst //. }
  left.
  apply: sim_body_result. intros.
  apply POST; eauto. by rewrite /ts Eqnp.
Qed. *)

(** Copy *)

Lemma priv_loc_not_public r l t t' :
  priv_loc r l t →
  (∃ (h: heapletR), r.(rtm) !! t' ≡ Some (to_tagKindR tkPub, h)) →
  t ≠ t'.
Proof.
  intros [h1 [Eqh1 ?]] [h2 Eqh2] ?. subst t'. move : Eqh2. rewrite Eqh1.
  intros [Eq1 ?]%Some_equiv_inj. by inversion Eq1.
Qed.

Lemma local_access_eq r l t t' stk n stk' kind σs σt :
  σt.(sst) !! l = Some stk →
  access1 stk kind t' σt.(scs) = Some (n, stk') →
  wsat r σs σt →
  (r.(rlm) !! l : optionR tagR) ≡ Some (to_tagR t) →
  t' = Tagged t ∧ stk' = stk.
Proof.
  intros Eql Eqstk WSAT Eqt'.
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  specialize (LINV _ _ Eqt') as [? [Eqs ?]]. rewrite Eql in Eqs. simplify_eq.
  destruct (access1_in_stack _ _ _ _ _ _ Eqstk)
    as [it [?%elem_of_list_singleton Eqt]].
  subst. split; [done|].
  destruct (tag_unique_head_access σt.(scs) (init_stack (Tagged t)) t None kind)
    as [stk1 Eq1]; [by exists []|].
  rewrite Eq1 in Eqstk. by simplify_eq.
Qed.

Lemma priv_loc_UB_access_eq r l kind σs σt t t' stk :
  σt.(sst) !! l = Some stk →
  is_Some (access1 stk kind t' σt.(scs)) →
  wsat r σs σt →
  priv_loc r l t →
  t' = Tagged t.
Proof.
  intros Eql ACC WSAT (h & Eqh & [LOC|PRO]).
  { destruct ACC as [[]]. eapply local_access_eq; eauto. }
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  specialize (PINV _ _ _ Eqh) as [Lt PINV].
  destruct PRO as (c & T & Eqc & InT & Inl). have Inl' := Inl.
  move : Inl'. rewrite elem_of_dom. intros [sa Eqs].
  move : (proj1 (proj1 VALID) t). rewrite Eqh. intros [_ VALh].
  specialize (VALh l). rewrite Eqs in VALh.
  apply to_agree_uninj in VALh as [s Eqsa].
  have Eqss : h !! l ≡ Some (to_agree s) by rewrite Eqsa Eqs.
  specialize (PINV _ _ Eqss stk Eql).
  specialize (CINV _ _ Eqc). simpl in CINV. destruct CINV as [Ltc CINV].
  specialize (CINV _ InT) as [Ltt CIN].
  specialize (CIN _ _ Eqh _ Inl) as (stk1 & pm1 & Eqstk1 & In1 & NDIS1).
  rewrite Eqstk1 in Eql. simplify_eq.
  specialize (PINV _ _ In1 NDIS1) as [Eqs1 HD].

  destruct ACC as [[n stk'] ACC].
  apply (access1_incompatible_head_protector _ _ _ _ _ _ _ _ HD Ltc ACC).
Qed.

Lemma priv_pub_access_UB (r: resUR) l kind σs σt t t' stk :
  σt.(sst) !! l = Some stk →
  is_Some (access1 stk kind t' σt.(scs)) →
  wsat r σs σt →
  priv_loc r l t →
  (if t' is (Tagged t2)
   then ∃ (h: heapletR), r.(rtm) !! t2 ≡ Some (to_tagKindR tkPub, h)
   else True) →
  False.
Proof.
  intros Eql IS WSAT PV PB.
  have Eq := priv_loc_UB_access_eq _ _ _ _ _ _ _ _ Eql IS WSAT PV.
  rewrite Eq in PB.
  by apply (priv_loc_not_public _ _ _ _ PV PB).
Qed.

Lemma sim_body_copy_public fs ft r n (pl: result) σs σt Φ
  (RREL: rrel r pl pl) :
  (∀ l t T vs vt r',
    pl = PlaceR l t T →
    read_mem l (tsize T) σs.(shp) = Some vs →
    read_mem l (tsize T) σt.(shp) = Some vt →
    ∀ α', memory_read σt.(sst) σt.(scs) l t (tsize T) = Some α' →
      let σs' := mkState σs.(shp) α' σs.(scs) σs.(snp) σs.(snc) in
      let σt' := mkState σt.(shp) α' σt.(scs) σt.(snp) σt.(snc) in
      vrel (r ⋅ r') vs vt → Φ (r ⋅ r') n (ValR vs) σs' (ValR vt) σt') →
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
      specialize (PI _ Eqstk it2.(perm) opro) as [Eql' HTOP].
      { simpl in *. rewrite /= Eqt2 Eqp2. by destruct it2. }
      { simpl in *. by rewrite (NDIS2 NDIS). }
      split; [done|].
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
  apply: sim_body_result. intros.
  have VREL2: vrel (r ⋅ (core (r_f ⋅ r))) vs vt.
  { eapply vrel_mono; [done| |exact VREL']. apply cmra_included_r. }
  eapply POST; eauto.
Qed.

(** Write *)
(* Fixpoint write_heaplet (l: loc) (v: value) (h: gmapR loc (agreeR scalarC)) :=
  match v with
  | [] => h
  | s :: v =>
      write_heaplet (l +ₗ 1) v (if h !! l then <[l := to_agree s]> h else h)
  end.
 *)
Fixpoint write_heaplet (l: loc) (v: value) (h: heaplet) :=
  match v with
  | [] => h
  | s :: v =>
      write_heaplet (l +ₗ 1) v (if h !! l then <[l := s]> h else h)
  end.

(* TODO: move *)
Instance insert_gmap_proper `{Countable K} {A : cmraT} (i: K) :
  Proper ((≡) ==> (≡) ==> (≡)) (insert (M:=gmap K A) i).
Proof.
  intros m1 m2 Eq a1 a2 Eqa i'. case (decide (i = i')) => [->|?].
  - by rewrite 2!lookup_insert Eq.
  - do 2 (rewrite lookup_insert_ne //).
Qed.

Instance write_heaplet_proper (l: loc) (v: value) :
  Proper ((≡) ==> (≡)) (write_heaplet l v).
Proof.
  intros h1 h2 Eq. revert l h1 h2 Eq.
  induction v as [|s v IH]; intros l h1 h2 Eq; simpl; [done|].
  apply IH. move : (Eq l).
  destruct (h1 !! l) as [s1|] eqn:Eq1, (h2 !! l) as [s2|] eqn:Eq2; [..|done];
    rewrite Eq1 Eq2; intros Eql; [by rewrite Eq|by inversion Eql..].
Qed.

Lemma write_heaplet_dom (l: loc) (v: value) h :
  dom (gset loc) (write_heaplet l v h) ≡ dom (gset loc) h.
Proof.
  revert l h.
  induction v as [|s v IH]; intros l h; simpl; [done|].
  rewrite IH. destruct (h !! l) eqn:Eq; [|done].
  rewrite dom_map_insert_is_Some //. by eexists.
Qed.

Lemma write_heaplet_empty l v : write_heaplet l v ∅ ≡ ∅.
Proof. revert l. induction v as [|?? IH]; [done|]; intros l. apply IH. Qed.

(* Lemma write_heaplet_valid l v h:
  ✓ h → ✓ (write_heaplet l v h).
Proof.
  revert l h. induction v as [|s v IH]; intros l h VALID; simpl; [done|].
  apply IH. destruct (h !! l) eqn:Eql; [|done]. by apply insert_valid.
Qed. *)

Lemma write_heaplet_lookup (l: loc) (vl: value) (h: heaplet) :
  (∀ (i: nat) s, (i < length vl)%nat →
    write_heaplet l vl h !! (l +ₗ i) = Some s →
    vl !! i = Some s) ∧
  (∀ (l': loc), (∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i) →
    write_heaplet l vl h !! l' = h !! l').
Proof.
  revert l h. induction vl as [|v vl IH]; move => l h; simpl;
    [split; [intros; by lia|done]|].
  destruct (IH (l +ₗ 1) (if h !! l then <[l:=v]> h else h)) as [IH1 IH2].
  split.
  - intros i s Lt. destruct i as [|i].
    + rewrite shift_loc_0_nat /=. rewrite IH2; [|].
      * destruct (h !! l) eqn:Eql; [by rewrite lookup_insert|].
        rewrite Eql; by inversion 1.
      * move => ? _.
        rewrite shift_loc_assoc -{1}(shift_loc_0 l) => /shift_loc_inj ?. by lia.
    + intros Eq. rewrite /= (IH1 _ s) ; [eauto|lia|].
      by rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
  - intros l' Lt. rewrite IH2.
    + destruct (h !! l) eqn:Eql; [|done].
      rewrite lookup_insert_ne; [done|].
      move => ?. subst l'. apply (Lt O); [lia|by rewrite shift_loc_0_nat].
    + move => i Lti. rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
      apply Lt. by lia.
Qed.

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
  intros LenT Eqr POST. pfold.
  intros NT. intros.
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
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
           (mkState (write_mem l v σt.(shp)) α' σt.(scs) σt.(snp) σt.(snc)).
    eapply (head_step_fill_tstep _ []), write_head_step'; eauto. }
  constructor 1. intros.
  destruct (tstep_write_inv _ (PlaceR _ _ _) (ValR _) _ _ _ STEPT)
      as (?&?&?&?& α' & EqH & EqH' & ? & Eqα' & EqD & IN & EQL & ?).
  symmetry in EqH, EqH'. simplify_eq.
  assert (∃ s, v = [s]) as [s ?].
  { rewrite LenT in EQL. destruct v as [|s v]; [simpl in EQL; done|].
    exists s. destruct v; [done|simpl in EQL; lia]. } subst v.

  have VALIDr:= cmra_valid_op_r _ _ VALID.
  have HLlr: r.(rlm) !! l ≡ Some (to_locStateR (lsLocal v' tg)).
  { rewrite Eqr. apply lmap_lookup_op_r.
    - rewrite ->Eqr in VALIDr. apply VALIDr.
    - by rewrite /= /init_local_res lookup_fmap /= lookup_insert /=. }
  destruct (LINV l v' tg) as (Eql1 & Eql2 & Eqsl1 & Eqsl2 & LocUnique).
  { apply lmap_lookup_op_r; [apply VALID|done]. }
  have ?: α' = σt.(sst).
  { move : Eqα'. rewrite LenT /= /memory_written /= shift_loc_0_nat.
    rewrite Eqsl2 /=.
    destruct (tag_unique_head_access σt.(scs) (init_stack (Tagged tg))
                tg None AccessWrite) as [ns Eqss]; [by exists []|].
    rewrite Eqss /= insert_id //. by inversion 1. } subst α'.

  set σs' := mkState (<[l := s]> σs.(shp)) σs.(sst) σs.(scs) σs.(snp) σs.(snc).
  have STEPS: ((Place l (Tagged tg) T <- #[s])%E, σs) ~{fs}~> ((#[☠])%V, σs').
  { setoid_rewrite (srel_heap_dom _ _ _ WFS WFT SREL) in EqD.
    destruct SREL as (Eqst&Eqnp&Eqcs&Eqnc&AREL).
    rewrite -Eqst -Eqcs in Eqα'.
    rewrite EQL in EqD. rewrite -Eqnp in IN.
    eapply (head_step_fill_tstep _ []), write_head_step'; eauto. }

  exists (#[☠])%V, σs', (r' ⋅ res_mapsto l 1 s tg), n.
  split; last split.
  { left. by constructor 1. }
  { have HLlrf: (r_f ⋅ r) .(rlm) !! l ≡ Some (to_locStateR (lsLocal v' tg)).
    { apply lmap_lookup_op_r; [apply VALID|done]. }
    have HLN: (r_f ⋅ r').(rlm) !! l = None.
    { destruct ((r_f ⋅ r').(rlm) !! l) as [ls|] eqn:Eqls; [|done].
      exfalso. move : HLlrf.
      rewrite Eqr cmra_assoc lookup_op Eqls /=
              /init_local_res lookup_fmap /= lookup_insert.
      apply lmap_exclusive_2. }
    have HTEq: (r_f ⋅ r' ⋅ res_mapsto l 1 v' tg).(rtm) ≡
               (r_f ⋅ r' ⋅ res_mapsto l 1 s tg).(rtm).
    { rewrite /rtm /= right_id //. }
    have HCEq: (r_f ⋅ r' ⋅ res_mapsto l 1 v' tg).(rcm) ≡
               (r_f ⋅ r' ⋅ res_mapsto l 1 s tg).(rcm).
    { rewrite /rcm /= right_id //. }
    rewrite cmra_assoc.
    split; last split; last split; last split; last split; last split.
    - by apply (tstep_wf _ _ _ STEPS WFS).
    - by apply (tstep_wf _ _ _ STEPT WFT).
    - move : VALID. rewrite Eqr cmra_assoc => VALID.
      apply (local_update_discrete_valid_frame _ _ _ VALID).
      by eapply res_mapsto_1_insert_local_update.
    - intros t k h HL. destruct (PINV t k h) as [? PI].
      { rewrite Eqr. move: HL. by rewrite 4!lookup_op /= 2!right_id. }
      split; [done|]. simpl.
      intros l1 s1 Eqs1. specialize (PI l1 s1 Eqs1) as [HLs1 PI].
      have NEql1: l1 ≠ l.
      { intros ?. subst l1. move : HLs1. rewrite HLlrf.
        intros Eq%Some_equiv_inj. inversion Eq. } split.
      { move : HLs1. rewrite Eqr cmra_assoc /=.
        rewrite lookup_op (lookup_op (r_f.2 ⋅ r'.2)) /init_local_res /= 2!lookup_fmap.
        do 2 rewrite lookup_insert_ne //. }
      by setoid_rewrite lookup_insert_ne.
    - intros c cs. simpl. rewrite -HCEq. intros Eqcm.
      move : CINV. rewrite Eqr cmra_assoc => CINV.
      specialize (CINV _ _ Eqcm). destruct cs as [[]| |]; [|done..].
      destruct CINV as [? CINV]. split; [done|]. by setoid_rewrite <- HTEq.
    - destruct SREL as (?&?&?&?& EqDl & REL). do 4 (split; [done|]).
      simpl. split.
      { rewrite dom_insert EqDl Eqr cmra_assoc. clear.
        rewrite 2!(dom_op (r_f.2 ⋅ r'.2)) 2!init_local_res_mem_dom
                /= insert_empty dom_singleton. set_solver. }
      intros l1 Eq1.
      have NEql1: l1 ≠ l.
      { intros ?. subst l1. move : Eq1. rewrite lookup_op HLN left_id.
        rewrite /init_local_res lookup_fmap /= lookup_insert.
        intros Eq%Some_equiv_inj. inversion Eq. }
      (* move : Inl1. rewrite dom_insert elem_of_union elem_of_singleton.
      intros [?|Inl1]; [done|]. *)
      have Eq1' : (r_f ⋅ r).(rlm) !! l1 ≡ Some (Cinr ()).
      { rewrite Eqr cmra_assoc -Eq1 lookup_op (lookup_op (r_f.2 ⋅ r'.2)).
        rewrite /init_local_res /= 2!lookup_fmap lookup_insert_ne //
                lookup_insert_ne //. }
      specialize (REL _ Eq1') as [REL|REL].
      + left. move : REL. rewrite /pub_loc /=.
        do 2 rewrite lookup_insert_ne //. intros REL st Eqst.
        specialize (REL st Eqst) as [ss [Eqss AREL]].
        exists ss. split; [done|]. move : AREL. rewrite /arel /=.
        destruct ss as [| |? [] |], st as [| |? []|]; try done; [|naive_solver].
        setoid_rewrite Eqr. setoid_rewrite cmra_assoc. by setoid_rewrite <- HTEq.
      + right. move : REL. setoid_rewrite Eqr. setoid_rewrite cmra_assoc.
        rewrite /priv_loc. by setoid_rewrite <- HTEq.
    - move : LINV. rewrite Eqr cmra_assoc.
      (* TODO: general property of lmap_inv w.r.t to separable resource *)
      intros LINV l1 s1 t1. specialize (LINV l1 s1 t1).
      destruct ((r_f ⋅ r').(rlm) !! l1) as [ls1|] eqn:Eqls1.
      + have NEQ: l1 ≠ l. { intros ?. subst l1. by rewrite Eqls1 in HLN. }
        intros EQl1.
        have EQl1' : (r_f ⋅ r' ⋅ res_mapsto l 1 v' tg).(rlm) !! l1
            ≡ Some (to_locStateR (lsLocal s1 t1)).
        { move : EQl1. rewrite lookup_op Eqls1 lookup_op Eqls1.
          rewrite /= /init_local_res 2!lookup_fmap /= lookup_insert_ne // lookup_insert_ne //. }
        specialize (LINV EQl1').
        rewrite /= lookup_insert_ne // lookup_insert_ne //.
      + rewrite /= lookup_op Eqls1 left_id /init_local_res /= lookup_fmap.
        intros Eq. case (decide (l1 = l)) => ?; [subst l1|].
        * move : Eq. rewrite 3!lookup_insert /=.
          intros Eq%Some_equiv_inj. simplify_eq. do 4 (split; [done|]).
          destruct LocUnique as [h1 Eqh1]. exists h1.
          by rewrite -HTEq -cmra_assoc -Eqr Eqh1.
        * exfalso. move : Eq. rewrite lookup_insert_ne // lookup_empty /=.
          by inversion 1. }
  left.
  apply: sim_body_result.
  intros. simpl. by apply POST.
Qed.

(** For writing to owned *or* public locations. *)
Lemma sim_body_write_related_values
  fs ft (r r': resUR) (k0: tag_kind) (h0: heaplet) n l tg Ts Tt v σs σt Φ
  (EQS: tsize Ts = tsize Tt)
  (* (Eqtg: r.(rtm) !! tg = Some (to_tagKindR k0, h0)) *)
  (NONLOCAL: if k0 is tkUnique then ∀ i, (i < tsize Tt)%nat →
    r.(rlm) !! (l +ₗ i) ≡ None else True)
  (* assuming to-write values are related *)
  (PUBWRITE: ∀ s, s ∈ v → arel r s s) :
  let rw := res_tag tg k0 h0 in
  r ≡ r' ⋅ rw →
  let rw' := if k0 then res_tag tg tkUnique (write_heaplet l v h0) else rw in
  (∀ α', memory_written σt.(sst) σt.(scs) l (Tagged tg) (tsize Tt) = Some α' →
    let σs' := mkState (write_mem l v σs.(shp)) α' σs.(scs) σs.(snp) σs.(snc) in
    let σt' := mkState (write_mem l v σt.(shp)) α' σt.(scs) σt.(snp) σt.(snc) in
    Φ (r' ⋅ rw')  n (ValR [☠]%S) σs' (ValR [☠]%S) σt' : Prop) →
  r ⊨{n,fs,ft}
    (Place l (Tagged tg) Ts <- #v, σs) ≥ (Place l (Tagged tg) Tt <- #v, σt) : Φ.
Proof.
  intros rw Eqr rw' POST. pfold. intros NT. intros.
  have WSAT1 := WSAT.
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  split; [|done|].
  { right.
    edestruct NT as [[]|[es' [σs' STEPS]]]; [constructor 1|done|].
    destruct (tstep_write_inv _ (PlaceR _ _ _) (ValR _) _ _ _ STEPS)
      as (?&?&?&?& α' & EqH & EqH' & ? & Eqα' & EqD & IN & EQL & ?).
    symmetry in EqH, EqH'. simplify_eq.
    setoid_rewrite <-(srel_heap_dom _ _ _ WFS WFT SREL) in EqD.
    destruct SREL as (Eqst&Eqnp&Eqcs&Eqnc&AREL).
    rewrite Eqst Eqcs EQS in Eqα'. rewrite -EQL in EQS.
    rewrite EQS in EqD. rewrite Eqnp in IN.
    exists (#[☠])%V,
           (mkState (write_mem l v σt.(shp)) α' σt.(scs) σt.(snp) σt.(snc)).
    by eapply (head_step_fill_tstep _ []), write_head_step'. }
  constructor 1. intros.
  destruct (tstep_write_inv _ (PlaceR _ _ _) (ValR _) _ _ _ STEPT)
      as (?&?&?&?& α' & EqH & EqH' & ? & Eqα' & EqD & IN & EQL & ?).
  symmetry in EqH, EqH'. simplify_eq.
  set σs' := mkState (write_mem l v σs.(shp)) α' σs.(scs) σs.(snp) σs.(snc).
  have STEPS: ((Place l (Tagged tg) Ts <- v)%E, σs) ~{fs}~> ((#[☠])%V, σs').
  { setoid_rewrite (srel_heap_dom _ _ _ WFS WFT SREL) in EqD.
    destruct SREL as (Eqst&Eqnp&Eqcs&Eqnc&AREL).
    rewrite -Eqst -Eqcs -EQS in Eqα'. rewrite -EQS in EQL.
    rewrite EQL in EqD. rewrite -Eqnp in IN.
    eapply (head_step_fill_tstep _ []), write_head_step'; eauto. }
  move : VALID. rewrite Eqr cmra_assoc. intros VALID.
  have HL: if k0 then
           (r_f ⋅ r' ⋅ rw).(rtm) !! tg ≡ Some (to_tagKindR tkUnique, to_agree <$> h0)
           else True.
  { destruct k0; [|done].
    move : (proj1 (proj1 VALID) tg). rewrite lookup_op lookup_insert.
    destruct ((r_f ⋅ r').1.1 !! tg) eqn:Eqtg; rewrite Eqtg; [|by rewrite left_id].
    intros ?%exclusive_r; [done|].
    admit. }
  have HLN: if k0 then (r_f ⋅ r').(rtm) !! tg ≡ None else True.
  { destruct k0; [|done].
    rewrite (tmap_insert_op_r r_f.(rtm) r.(rtm) tg h0) //. apply VALID.
  (* have HL: if k0 then ∀ kh, r_f.(rtm) ⋅ <[tg:=kh]> r.(rtm) = <[tg:=kh]> (r_f.(rtm) ⋅ r.(rtm)) else True.
  { destruct k0; [|done]. intros.
    rewrite (tmap_insert_op_r r_f.(rtm) r.(rtm) tg h0) //. apply VALID. }
  have HL2: if k0 then  (r_f.(rtm) ⋅ r.(rtm)) !! tg = Some (to_tagKindR tkUnique, h0) else True.
  { destruct k0; [|done].
    by apply (tmap_lookup_op_r _ _ _ _ (proj1 (proj1 VALID)) Eqtg). } *)
  have SHR: ∀ i, (i < tsize Tt)%nat →
    (r_f ⋅ r).(rlm) !! (l +ₗ i) ≡ Some $ to_locStateR lsShared.
  { destruct k0.
    - intros i Lt. specialize (NONLOCAL _ Lt).
      apply lmap_lookup_op_r; [apply VALID|done].
    - eapply public_access_not_local; eauto. setoid_rewrite Eqr.
      have HLrw: rw.(rtm) !! tg ≡ Some (to_tagKindR tkPub, to_agree <$> h0).
      { by rewrite lookup_insert. }
      apply (tmap_lookup_op_r_equiv_pub r'.(rtm)) in HLrw as [h2 Eq2];
        [by eexists|]. apply cmra_valid_op_r in VALID. rewrite ->Eqr in VALID.
      apply VALID. } clear WSAT1.
  move : VALID. rewrite Eqr cmra_assoc. intros VALID.
  exists (#[☠])%V, σs', (r' ⋅ rw'), n. split; last split.
  { left. by constructor 1. }
  { have Eqrlm: (r_f ⋅ r' ⋅ rw').(rlm) ≡ (r_f ⋅ r' ⋅ rw).(rlm) by destruct k0.
    destruct (for_each_lookup _ _ _ _ _ Eqα') as [EQ1 EQ2].
    rewrite cmra_assoc.
    split; last split; last split; last split; last split; last split.
    - by apply (tstep_wf _ _ _ STEPS WFS).
    - by apply (tstep_wf _ _ _ STEPT WFT).
    - (* valid *)
      destruct k0; [|done].
      apply (local_update_discrete_valid_frame  _ _ _ VALID).
      apply prod_local_update_1, prod_local_update_1. simpl.
      admit.
    - (* tmap_inv *)
      intros t k h Eqt.
      have Eqttg: t = tg → k0 = tkUnique → k = k0 ∧ h ≡ to_agree <$> write_heaplet l v h0.
      { intros. subst t k0. move  : Eqt. rewrite /rtm /= HL lookup_insert.
        intros [Eq1 Eq2]%Some_equiv_inj.
        simpl in Eq1, Eq2. rewrite Eq2. repeat split; [|done].
        destruct k; [done|inversion Eq1]. }
      have CASEt : (t = tg ∧ k0 = tkUnique ∧ k = k0 ∧ h ≡ write_heaplet l v h0 ∨
                    (r_f ⋅ r).(rtm) !! t ≡ Some (to_tagKindR k, h) ∧
                      (k = tkUnique → t ≠ tg)).
      { move : Eqt. rewrite /r'.
        destruct k0; simpl.
        - rewrite /rtm /= HL.
          case (decide (t = tg)) => ?; [subst t|rewrite lookup_insert_ne //].
          + left. by destruct Eqttg.
          + right. naive_solver.
        - case (decide (t = tg)) => ?; [subst t|].
          + intros Eqt. right. split; [done|]. intros ?. subst k.
            move : Eqt. rewrite lookup_op Eqtg. by move => /tagKindR_exclusive_2.
          + right. naive_solver. }
      split.
      { simpl. destruct CASEt as [(?&?&?&?Eqh)|[Eqh NEQ]].
        - subst t k k0. apply (PINV tg tkUnique h0). by rewrite HL2.
        - move : Eqh. apply PINV. }
      intros l' s' Eqk'. split.
      { destruct CASEt as [(?&?&?&?Eqh)|[Eqh NEQ]].
        - subst t k k0. destruct (PINV tg tkUnique h0) as [? PI]; [by rewrite HL2|].
          have InD': l' ∈ dom (gset loc) h.
          { rewrite elem_of_dom.
            destruct (h !! l') eqn:Eql'; rewrite Eql'; [by eexists|by inversion Eqk']. }
          move : InD'. rewrite Eqh write_heaplet_dom elem_of_dom.
          intros [s0 Eqs0].
          have VALS := proj1 (proj1 (cmra_valid_op_r _ _ VALID)) tg.
          rewrite Eqtg in VALS.
          have VALs0: ✓ s0. { change (✓ (Some s0)). rewrite -Eqs0. apply VALS. }
          apply to_agree_uninj in VALs0 as [ss0 Eqss0].
          destruct (PI l' ss0) as [? _]; [|done]. by rewrite Eqs0 Eqss0.
        - specialize (PINV _ _ _ Eqh) as [? PINV].
          specialize (PINV _ _ Eqk') as [EQ _]. rewrite /r' /=. by destruct k0. }
      intros stk'. simpl.
      destruct (write_mem_lookup_case l v σt.(shp) l')
          as [[i [Lti [Eqi Eqmi]]]|[NEql Eql]]; last first.
      { (* l' is NOT written to *)
        destruct (for_each_lookup _ _ _ _ _ Eqα') as [_ [_ EQ]].
        rewrite EQL in NEql. rewrite (EQ _ NEql) Eql.
        destruct CASEt as [(?&?&?&?Eqh)|[Eqh ?]]; [|by apply (PINV t k h Eqh)].
        subst t k k0. apply (PINV tg tkUnique h0).
        - by rewrite HL2.
        - move : Eqk'. rewrite Eqh. rewrite -EQL in NEql.
          by rewrite (proj2 (write_heaplet_lookup l v h0) _ NEql). }
      (* l' is written to *)
      intros Eqstk' pm opro In' NDIS. subst l'.
      destruct (for_each_access1 _ _ _ _ _ _ _ Eqα' _ _ Eqstk')
        as (stk & Eqstk & SUB & ?).
      destruct (SUB _ In') as (it2 & In2 & Eqt2 & Eqp2 & NDIS2). simpl in *.
      destruct CASEt as [(?&?&?&?Eqh)|[Eqh NEQ]].
      + (* t = tg *)
        subst t k k0. rewrite -> Eqh in Eqk'. split.
        * have Eqs' := proj1 (write_heaplet_lookup l v h0) _ _ Lti Eqk'.
          rewrite (proj1 (write_mem_lookup l v σt.(shp)) _ Lti).
          destruct (v !! i) as [s''|] eqn: Eq''; [rewrite Eq''|by inversion Eqs'].
          apply Some_equiv_inj, to_agree_inj in Eqs'. by inversion Eqs'.
        * assert (∃ s0: scalar, h0 !! (l +ₗ i) ≡ Some (to_agree s0)) as [s0 Eq0].
          { assert (is_Some (h0 !! (l +ₗ i))) as [s0 Eqs0].
            { rewrite -(elem_of_dom (D:=gset loc)) -(write_heaplet_dom l v h0).
              move : Eqk'.
              destruct (write_heaplet l v h0 !! (l +ₗ i)) eqn: Eq'';
                rewrite Eq''; [intros _|by inversion 1].
              apply (elem_of_dom_2 _ _ _ Eq''). }
            rewrite Eqs0.
            destruct (to_agree_uninj s0) as [s1 Eq1]; [|by exists s1; rewrite -Eq1].
            apply (lookup_valid_Some h0 (l +ₗ i)); [|by rewrite Eqs0].
            apply (lookup_valid_Some (r_f.(rtm) ⋅ r.(rtm)) tg (to_tagKindR tkUnique, h0));
              [by apply (proj1 VALID)|by rewrite HL2]. }
          specialize (PINV tg tkUnique h0) as [Lt PI]; [by rewrite HL2|].
          specialize (PI _ _ Eq0) as [? PI].
          specialize (PI _ Eqstk it2.(perm) opro) as [Eql' HTOP].
          { rewrite /= Eqt2 Eqp2. by destruct it2. } { by rewrite (NDIS2 NDIS). }
          destruct (for_each_lookup_case _ _ _ _ _ Eqα' _ _ _ Eqstk Eqstk')
            as [?|[MR _]]; [by subst|]. clear -In' MR HTOP Eqstk WFT NDIS.
          destruct (access1 stk AccessWrite (Tagged tg) σt.(scs))
            as [[n stk1]|] eqn:Eqstk'; [|done]. simpl in MR. simplify_eq.
          destruct (state_wf_stack_item _ WFT _ _ Eqstk). move : Eqstk' HTOP.
          eapply access1_head_preserving; eauto.
      + (* invoke PINV for t *)
        exfalso. destruct (PINV t k h Eqh) as [Lt PI].
        specialize (PI _ _ Eqk') as [? PI].
        specialize (PI _ Eqstk it2.(perm) opro) as [Eql' HTOP].
        { rewrite /= Eqt2 Eqp2. by destruct it2. } { by rewrite (NDIS2 NDIS). }
        destruct k.
        * (* if k is Unique ∧ t ≠ tg, writing with tg must have popped t
            from top, contradicting In'. *)
          rewrite EQL in Lti. destruct (EQ1 _ _ Lti Eqstk) as [ss' [Eq' EQ3]].
          have ?: ss' = stk'. { rewrite Eqstk' in Eq'. by inversion Eq'. }
          subst ss'. clear Eq'. move : EQ3.
          case access1 as [[n1 stk1]|] eqn:EQ4; [|done].
          simpl. intros ?. simplify_eq.
          specialize (NEQ eq_refl).
          have ND := proj2 (state_wf_stack_item _ WFT _ _ Eqstk).
          move : In'.
          eapply (access1_write_remove_incompatible_head _ tg t _ _ _ ND);
            [by eexists|done..].
        * (* if k is Public => t is for SRO, and must also have been popped,
             contradicting In'. *)
          rewrite EQL in Lti. destruct (EQ1 _ _ Lti Eqstk) as [ss' [Eq' EQ3]].
          have ?: ss' = stk'. { rewrite Eqstk' in Eq'. by inversion Eq'. }
          subst ss'. clear Eq'. move : EQ3.
          case access1 as [[n1 stk1]|] eqn:EQ4; [|done].
          simpl. intros ?. simplify_eq.
          have ND := proj2 (state_wf_stack_item _ WFT _ _ Eqstk).
          move : In'.
          eapply (access1_write_remove_incompatible_active_SRO _ tg t _ _ _ ND); eauto.
    - (* cmap_inv : make sure tags in the new resource are still on top *)
      intros c cs Eqc'.
      have Eqc: (r_f ⋅ r).(rcm) !! c ≡ Some cs.
      { move  : Eqc'. rewrite /r'. by destruct k0. }
      specialize (CINV _ _ Eqc). simpl.
      clear -Eqα' CINV Eqtg VALID HL HL2. destruct cs as [[T|]| |]; [|done..].
      destruct CINV as [IN CINV]. split; [done|].
      intros t InT. specialize (CINV _ InT) as [? CINV]. split; [done|].
      intros k h.
      (* TODO: duplicated proofs *)
      rewrite /r'. destruct k0.
      + (* if tg was unique *)
        rewrite /rtm /= HL.
        case (decide (t = tg)) => ?.
        { subst tg. rewrite lookup_insert.
          intros [Eqk Eqh]%Some_equiv_inj. simpl in Eqk, Eqh.
          have Eqt : (r_f ⋅ r).(rtm) !! t ≡ Some (k, h0) by rewrite HL2 -Eqk.
          intros l'. rewrite -Eqh write_heaplet_dom. intros Inh.
          destruct (CINV _ _ Eqt _ Inh) as (stk' & pm' & Eqstk' & Instk' & NDIS).
          destruct (for_each_access1_active_preserving _ _ _ _ _ _ _ Eqα' _ _ Eqstk')
            as [stk [Eqstk AS]].
          exists stk, pm'. split; last split; [done|by apply AS|done]. }
        { rewrite lookup_insert_ne //.
          intros Eqt l' Inh.
          destruct (CINV _ _ Eqt _ Inh) as (stk' & pm' & Eqstk' & Instk' & NDIS).
          destruct (for_each_access1_active_preserving _ _ _ _ _ _ _ Eqα' _ _ Eqstk')
            as [stk [Eqstk AS]].
          exists stk, pm'. split; last split; [done|by apply AS|done]. }
      + (* if tg was public *)
        intros Eqt l' Inh.
        destruct (CINV _ _ Eqt _ Inh) as (stk' & pm' & Eqstk' & Instk' & NDIS).
        destruct (for_each_access1_active_preserving _ _ _ _ _ _ _ Eqα' _ _ Eqstk')
          as [stk [Eqstk AS]].
        exists stk, pm'. split; last split; [done|by apply AS|done].
    - (* srel *)
      rewrite /srel /=. destruct SREL as (?&?&?&?&EqDl&Eq).
      split; last split; last split; last split; last split; [done..| |].
      { rewrite write_mem_dom // EqDl -Eqrlm //. }
      intros l1 Eq1.
      destruct (write_mem_lookup l v σs.(shp)) as [EqN EqO]. rewrite /r'.
      destruct (write_mem_lookup_case l v σt.(shp) l1)
        as [[i [Lti [Eqi Eqmi]]]|[NEql Eql]].
      + subst l1. specialize (EqN _ Lti). (* rewrite EqN. *)
        have InD := (EqD _ Lti).
        rewrite (_: r_f.2 ⋅ r'.2 = (r_f ⋅ r').(rlm)) // in Eq1.
        rewrite -> Eqrlm in Eq1. specialize (Eq _ Eq1).
        destruct (lookup_lt_is_Some_2 _ _ Lti) as [s Eqs].
        destruct k0.
        * (* tg was unique, and (l +ₗ i) was written to *)
          destruct Eq as [PB|[t PV]].
          { left. intros st. simpl. intros Eqst.
            have ?: st = s. { rewrite Eqmi Eqs in Eqst. by inversion Eqst. }
            subst st. exists s. rewrite EqN. split; [done|].
            move : (PUBWRITE _ (elem_of_list_lookup_2 _ _ _ Eqs)).
            rewrite /arel /=. destruct s as [| |l0 t0|]; [done..| |done].
            intros [? [? Eqt0]]. repeat split; [done..|].
            destruct t0 as [t0|]; [|done].
            repeat split. destruct Eqt0 as [ht0 Eqt0].
            destruct (tmap_lookup_op_r_equiv_pub r_f.(rtm) r.(rtm)
                        _ _ (proj1 (proj1 VALID)) Eqt0) as [h' Eq'].
            exists (h' ⋅ ht0). rewrite /rtm /= HL lookup_insert_ne //.
            intros ?; subst t0. rewrite Eqtg in Eqt0.
            apply Some_equiv_inj in Eqt0 as [Eqt0 _]. inversion Eqt0. }
          { destruct PV as (c & T & h & Eqc & InT & Eqt & Inh).
            right. exists t, c, T.
            case (decide (t = tg)) => ?; [subst t|].
            - exists (write_heaplet l v h0). do 2 (split; [done|]). split.
              by rewrite /rtm /= HL lookup_insert.
              rewrite write_heaplet_dom.
              rewrite HL2 in Eqt. apply Some_equiv_inj in Eqt as [? Eqt].
              simpl in Eqt. by rewrite Eqt.
            - exists h. rewrite /rtm /= HL. do 2 (split; [done|]).
              rewrite lookup_insert_ne //. }
        * (* tg was public, and (l +ₗ i) was written to *)
          left. intros st. simpl. intros Eqst.
          have ?: st = s. { rewrite Eqmi Eqs in Eqst. by inversion Eqst. }
          subst st. exists s. rewrite EqN. split; [done|].
          (* we know that the values written must be publicly related *)
          apply (arel_mono r _ VALID).
          { apply cmra_included_r. }
          { apply PUBWRITE, (elem_of_list_lookup_2 _ _ _ Eqs). }
      + specialize (EqO _ NEql).
        (* have InD1': l1 ∈ dom (gset loc) σt.(shp)
          by rewrite elem_of_dom -Eql -(elem_of_dom (D:=gset loc)). *)
        have Eq1' : (r_f ⋅ r).(rlm) !! l1 ≡ Some $ to_locStateR lsShared.
        { move : Eq1. by destruct k0. }
        specialize (Eq _ Eq1'). rewrite /pub_loc EqO Eql.
        destruct k0; [|done].
        destruct Eq as [PB|[t PV]].
        * (* tg was unique, and l1 was NOT written to *)
          left. intros st Eqst. destruct (PB _ Eqst) as [ss [Eqss AREL]].
          exists ss. split; [done|]. move : AREL. rewrite /arel.
          destruct ss as [| |l0 t0|], st as [| |l3 t3|]; try done.
          intros [? [? Eqt]]. subst l3 t3. repeat split.
          destruct t0 as [t0|]; [|done].
          destruct Eqt as [h Eqt]. exists h.
          rewrite /rtm /= HL (lookup_insert_ne _ tg) //.
          intros ?. subst t0. move : Eqt. rewrite lookup_op Eqtg.
          by apply tagKindR_exclusive.
        * (* tg was public, and l1 was NOT written to *)
          right. destruct PV as (c & T & h & Eqc & InT & Eqt & Inl).
          exists t, c, T. simpl.
          case (decide (t = tg)) => ?; [subst t|].
          { eexists (write_heaplet l v h0).
            rewrite /rtm /= HL lookup_insert. repeat split; [done..|].
            rewrite lookup_op Eqtg in Eqt.
            by rewrite write_heaplet_dom (tagKindR_exclusive_heaplet _ _ _ Eqt). }
          { exists h. rewrite /rtm /= HL lookup_insert_ne //. }
    - intros l' s' t'. rewrite Eqrlm. intros Eq. rewrite /=.
      specialize (LINV _ _ _ Eq) as (?&?&?&?& h & Eqh).
      destruct (write_mem_lookup l v σs.(shp)) as [_ HLs].
      destruct (write_mem_lookup l v σt.(shp)) as [_ HLt].
      have NEQ: ∀ i, (i < length v)%nat → l' ≠ l +ₗ i.
      { intros i Lti EQ. rewrite EQL in Lti. specialize (SHR _ Lti).
        subst l'.
        move : Eq. rewrite SHR. intros Eqv%Some_equiv_inj. inversion Eqv. }
      destruct EQ2 as [_ EQ2].
      rewrite HLs // HLt // EQ2 //; [|rewrite -EQL //].
      do 4 (split; [done|]). rewrite /r'. destruct k0; simpl; [|by exists h].
      setoid_rewrite HL.
      case (decide (t' = tg)) => ?; [subst t'|].
      rewrite lookup_insert. by eexists.
      rewrite lookup_insert_ne //. by eexists.
  }
  left.
  apply: sim_body_result.
  intros. simpl. by apply POST.
Abort.


(** can probably be derived from [write_related_values]? *)
Lemma sim_body_write_owned
  fs ft (r r' r'' rs: resUR) h n l tg T s σs σt Φ:
  tsize T = 1%nat →
  r ≡ r' ⋅ res_tag tg tkUnique h →
  is_Some (h !! l) →
  arel rs s s → (* assuming to-write values are related *)
  r' ≡ r'' ⋅ rs →
  (∀ α', memory_written σt.(sst) σt.(scs) l (Tagged tg) (tsize T) = Some α' →
    let σs' := mkState (write_mem l [s] σs.(shp)) α' σs.(scs) σs.(snp) σs.(snc) in
    let σt' := mkState (write_mem l [s] σt.(shp)) α' σt.(scs) σt.(snp) σt.(snc) in
    tag_on_top σt.(sst) l tg →
    Φ (r' ⋅ res_tag tg tkUnique (<[l:=s]> h)) n (ValR [☠]%S) σs' (ValR [☠]%S) σt') →
  r ⊨{n,fs,ft}
    (Place l (Tagged tg) T <- #[s], σs) ≥ (Place l (Tagged tg) T <- #[s], σt) : Φ.
Proof.
Admitted.

(** Retag *)

Lemma retag_ref_change_1 h α cids c nxtp x rk mut T h' α' nxtp'
  (N2: rk ≠ TwoPhase) (TS: (O < tsize T)%nat) (FRZ: is_freeze T) :
  retag h α nxtp cids c x rk (Reference (RefPtr mut) T) = Some (h', α', nxtp') →
  ∃ l otag, h !! x = Some (ScPtr l otag) ∧
  ∃ rk' new,
    h' = <[x := ScPtr l new]>h ∧
    retag_ref h α cids nxtp l otag T rk' (adding_protector rk c) =
      Some (new, α', nxtp') ∧
    rk' = if mut then UniqueRef (is_two_phase rk) else SharedRef.
Proof.
  rewrite retag_equation_2 /=.
  destruct (h !! x) as [[| |l t|]|]; simpl; [done..| |done|done].
  destruct mut; (case retag_ref as [[[t1 α1] n1]|] eqn:Eq => [/=|//]);
    intros; simplify_eq; exists l, t; (split; [done|]);
    eexists; exists t1; done.
Qed.

Lemma retag_ref_change_2
  h α cids c nxtp l otag rk (mut: mutability) T new α' nxtp'
  (TS: (O < tsize T)%nat) (FRZ: is_freeze T) :
  let rk' := if mut then UniqueRef false else SharedRef in
  let opro := (adding_protector rk c) in
  retag_ref h α cids nxtp l otag T rk' opro = Some (new, α', nxtp') →
  nxtp' = S nxtp ∧ new = Tagged nxtp ∧
  reborrowN α cids l (tsize T) otag (Tagged nxtp)
            (if mut then Unique else SharedReadOnly) opro = Some α'.
Proof.
  intros rk' opro. rewrite /retag_ref. destruct (tsize T) as [|n] eqn:EqT; [lia|].
  destruct mut; simpl; [|rewrite visit_freeze_sensitive_is_freeze //];
    case reborrowN as [α1|] eqn:Eq1 => [/=|//]; intros; simplify_eq; by rewrite -EqT.
Qed.

Lemma retag_ref_change h α cids c nxtp x rk mut T h' α' nxtp'
  (N2: rk ≠ TwoPhase) (TS: (O < tsize T)%nat) (FRZ: is_freeze T) :
  retag h α nxtp cids c x rk (Reference (RefPtr mut) T) = Some (h', α', nxtp') →
  ∃ l otag, h !! x = Some (ScPtr l otag) ∧
    h' = <[x := ScPtr l (Tagged nxtp)]>h ∧
    nxtp' = S nxtp ∧
    reborrowN α cids l (tsize T) otag (Tagged nxtp)
            (if mut then Unique else SharedReadOnly) (adding_protector rk c) = Some α'.
Proof.
  intros RT.
  apply retag_ref_change_1 in RT
    as (l & otag & EqL & rk' & new & Eqh & RT &?); [|done..].
  subst. exists l, otag. split; [done|].
  rewrite (_: is_two_phase rk = false) in RT; [|by destruct rk].
  apply retag_ref_change_2 in RT as (?&?&?); [|done..]. by subst new.
Qed.

Lemma retag_ref_reborrowN
  (h: mem) α t cids c x l otg T rk (mut: mutability) α'
  (N2: rk ≠ TwoPhase) (TS: (O < tsize T)%nat) (FRZ: is_freeze T) :
  h !! x = Some (ScPtr l otg) →
  reborrowN α cids l (tsize T) otg (Tagged t)
     (if mut then Unique else SharedReadOnly) (adding_protector rk c) =
     Some α' →
  retag h α t cids c x rk (Reference (RefPtr mut) T) = Some (<[x:=ScPtr l (Tagged t)]> h, α', S t).
Proof.
  intros Eqx RB. rewrite retag_equation_2 Eqx /= /retag_ref.
  destruct (tsize T) eqn:EqT; [lia|].
  rewrite (_: is_two_phase rk = false); [|by destruct rk].
  destruct mut; simpl; [|rewrite visit_freeze_sensitive_is_freeze //]; rewrite EqT RB /= //.
Qed.

Lemma sim_body_retag_default fs ft r n x xtag mut T σs σt Φ
  (TS: (O < tsize T)%nat) (FRZ: is_freeze T) (Eqx: σs.(shp) = σt.(shp)) :
  let Tr := (Reference (RefPtr mut) T) in
  (∀ c cids hs' αs' nps' ht' αt' npt' (STACK: σt.(scs) = c :: cids),
    retag σt.(shp) σt.(sst) σt.(snp) σt.(scs) c x Default Tr
      = Some (ht', αt', npt') →
    retag σs.(shp) σs.(sst) σs.(snp) σs.(scs) c x Default Tr
      = Some (hs', αs', nps') →
    let σs' := mkState hs' αs' σs.(scs) nps' σs.(snc) in
    let σt' := mkState ht' αt' σt.(scs) npt' σt.(snc) in
      Φ r n (ValR [☠]%S) σs' (ValR [☠]%S) σt' : Prop) →
  r ⊨{n,fs,ft}
    (Retag (Place x xtag Tr) Default, σs) ≥
    (Retag (Place x xtag Tr) Default, σt) : Φ.
Proof.
  intros Tr POST. pfold. intros NT. intros.
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  split; [|done|].
  { right.
    edestruct NT as [[]|[es' [σs' STEPS]]]; [constructor 1|done|].
    (* inversion retag of src *)
    destruct (tstep_retag_inv _ _ _ _ _ _ _ _ _ STEPS)
      as (c & cids & h' & α' & nxtp' & Eqs & EqT & ? & ?). subst es'.
    apply retag_ref_change in EqT as (l & otg & Eqx' & Eqh' & Eqp' & RB); [|done..].
    subst h' nxtp'. destruct SREL as (Eqst & Eqnp & Eqcs & Eqnc &?).
    rewrite Eqx in Eqx'. rewrite Eqst Eqcs Eqnp in RB. rewrite Eqcs in Eqs.
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
  apply retag_ref_change in EqT as (l & otg & Eqx' & Eqh' & Eqp' & RB); [|done..].
  subst h' nxtp'.
  exists (#[☠])%V,
      (mkState (<[x:=ScPtr l (Tagged σs.(snp))]> σs.(shp)) α' σs.(scs) (S σs.(snp)) σs.(snc)).
  exists r, n. split; last split.
  { left. apply tc_once.
    destruct SREL as (Eqst & Eqnp & Eqcs & Eqnc &?).
    rewrite -Eqx in Eqx'. rewrite -Eqst -Eqcs -Eqnp in RB. rewrite -Eqcs in Eqs.
    eapply (head_step_fill_tstep _ []), retag1_head_step'; [eauto|].
    eapply retag_ref_reborrowN; eauto. }
  { split.
Abort.

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
