From iris.algebra Require Import local_updates.

From stbor.lang Require Import steps_progress steps_inversion steps_retag.
From stbor.sim Require Export instance.

Set Default Proof Using "Type".

(** MEM STEP -----------------------------------------------------------------*)

Lemma sim_body_alloc_local fs ft r n T σs σt Φ :
  let l := (fresh_block σt.(shp), 0) in
  let t := (Tagged σt.(snp)) in
  let σs' := mkState (init_mem l (tsize T) σs.(shp))
                     (init_stacks σs.(sst) l (tsize T) t) σs.(scs)
                     (S σs.(snp)) σs.(snc) in
  let σt' := mkState (init_mem l (tsize T) σt.(shp))
                     (init_stacks σt.(sst) l (tsize T) t) σt.(scs)
                     (S σt.(snp)) σt.(snc) in
  let r' : resUR := res_mapsto l ScPoison (init_stack t) in
  Φ (r ⋅ r') n (PlaceR l t T) σs' (PlaceR l t T) σt' : Prop →
  r ⊨{n,fs,ft} (Alloc T, σs) ≥ (Alloc T, σt) : Φ.
Proof.
Admitted.

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
  apply (sim_body_result _ _ _ _ (PlaceR _ _ T) (PlaceR _ _ T)). intros.
  apply POST; eauto. by rewrite /ts Eqnp.
Qed. *)

(** Copy *)
Lemma sim_body_copy_public fs ft r n l t Ts Tt σs σt Φ
  (EQS: tsize Ts = tsize Tt)
  (PUBLIC: ∃ (h: heapletR), r.(rtm) !! t ≡ Some (to_tagKindR tkPub, h))
  (SHR: ∀ i, (i < tsize Tt)%nat → r.(rlm) !! (l +ₗ i) ≡ Some $ to_locStateR lsShared) :
  (∀ vs vt r',
    read_mem l (tsize Ts) σs.(shp) = Some vs →
    read_mem l (tsize Tt) σt.(shp) = Some vt →
    ∀ α', memory_read σt.(sst) σt.(scs) l (Tagged t) (tsize Tt) = Some α' →
      let σs' := mkState σs.(shp) α' σs.(scs) σs.(snp) σs.(snc) in
      let σt' := mkState σt.(shp) α' σt.(scs) σt.(snp) σt.(snc) in
      vrel (r ⋅ r') vs vt → Φ (r ⋅ r') n (ValR vs) σs' (ValR vt) σt' : Prop) →
  r ⊨{n,fs,ft} (Copy (Place l (Tagged t) Ts), σs) ≥ (Copy (Place l (Tagged t) Tt), σt) : Φ.
Proof.
  intros POST. pfold.
  intros NT. intros.
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  split; [|done|].
  { right.
    destruct (NT (Copy (Place l (Tagged t) Ts)) σs) as [[]|[es' [σs' STEPS]]];
      [done..|].
    destruct (tstep_copy_inv _ _ _ _ _ _ _ STEPS)
      as (vs & α' & ? & Eqvs & Eqα' & ?). subst es'.
    destruct (read_mem_is_Some l (tsize Tt) σt.(shp)) as [vt Eqvt].
    { intros m. rewrite (srel_heap_dom _ _ _ WFS WFT SREL) -EQS.
      apply (read_mem_is_Some' l (tsize Ts) σs.(shp)). by eexists. }
    have Eqα'2: memory_read σt.(sst) σt.(scs) l (Tagged t)  (tsize Tt) = Some α'.
    { destruct SREL as (Eqst&?&Eqcs&?). by rewrite -Eqst -Eqcs -EQS. }
    exists (#vt)%E, (mkState σt.(shp) α' σt.(scs) σt.(snp) σt.(snc)).
    by eapply (head_step_fill_tstep _ []), copy_head_step'. }
  constructor 1. intros.
  destruct (tstep_copy_inv _ _ _ _ _ _ _ STEPT) as (vt & α' & ? & Eqvt & Eqα' & ?).
  subst et'.
  destruct (read_mem_is_Some l (tsize Ts) σs.(shp)) as [vs Eqvs].
  { intros m. rewrite -(srel_heap_dom _ _ _ WFS WFT SREL) EQS.
    apply (read_mem_is_Some' l (tsize Tt) σt.(shp)). by eexists. }
  have Eqα'2: memory_read σs.(sst) σs.(scs) l (Tagged t)  (tsize Ts) = Some α'.
  { destruct SREL as (Eqst&?&Eqcs&?). by rewrite Eqst Eqcs EQS. }
  set σs' := mkState σs.(shp) α' σs.(scs) σs.(snp) σs.(snc).
  have STEPS: (Copy (Place l (Tagged t)  Ts), σs) ~{fs}~> ((#vs)%E, σs').
  { by eapply (head_step_fill_tstep _ []), copy_head_step'. }
  have CORE : (r_f ⋅ r) ≡ r_f ⋅ r ⋅ core (r_f ⋅ r) by rewrite cmra_core_r.
  assert (VREL': vrel (core (r_f ⋅ r)) vs vt).
  { destruct PUBLIC as [h PUB].
    destruct (tmap_lookup_op_r_equiv_pub r_f.(rtm) r.(rtm) t h) as [h0 Eqh0];
      [apply VALID|done|].
    destruct (PINV _ _ _ Eqh0) as [Lt PB].
    destruct SREL as (Eqst & Eqnp & Eqcs & Eqnc & PRIV).
    destruct (read_mem_values _ _ _ _ Eqvs) as [Eqls HLs].
    destruct (read_mem_values _ _ _ _ Eqvt) as [Eqlt HLt].
    apply Forall2_same_length_lookup. split; [by rewrite Eqls Eqlt|].
    intros i ss st Hss Hst.
    have HLLs := lookup_lt_Some _ _ _ Hss. have HLLt := lookup_lt_Some _ _ _ Hst.
    rewrite -Eqls in HLs. specialize (HLs _ HLLs). rewrite Hss in HLs.
    rewrite -Eqlt in HLt. specialize (HLt _ HLLt). rewrite Hst in HLt.
    rewrite -Eqlt in SHR.
    have SHR' := lmap_lookup_op_r _ _ (proj2 VALID) _ _ (SHR _ HLLt).
    specialize (PRIV _ (elem_of_dom_2 _ _ _ HLt) SHR')
      as [PUBl|[t' PV]].
    { destruct (PUBl _ HLt) as [ss' [Eqss' AREL]].
      rewrite HLs in Eqss'. symmetry in Eqss'. simplify_eq. move: AREL.
      destruct ss as [| |l1 [t1|]|], st as [| |l2 [t2|]|]; auto; simpl; [|by intros [?[]]].
      intros [? [? [h' Eqh']]]. simplify_eq. do 2 (split; [done|]).
      exists h'. by apply tmap_lookup_core_pub. }
    destruct PV as (c' & T' & h' & Eqci & InT' & Eqh' & Inl).
     (* impossible: t' is protected by c' which is still active.
      So t ≠ t' and protected(t',c') is on top of (l +ₗ i), so access with t is UB *)
    exfalso.
    have NEQ: t' ≠ t.
    { intros ?. subst t'.
      apply (tmap_lookup_op_r_equiv_pub r_f.(rtm)) in PUB as [? PUB];
        [|by apply VALID].
      rewrite -> PUB in Eqh'. apply Some_equiv_inj in Eqh' as [Eqk' ?].
      inversion Eqk'. }
    specialize (CINV _ _ Eqci) as [Inc' CINV].
    specialize (CINV _ InT') as [Ltt' CINV].
    specialize (CINV _ _ Eqh' _ Inl) as (stk & pm & Eqstk & Instk & NDIS).
    specialize (PINV _ _ _ Eqh') as [_ PINV].
    have VALh' : ✓ h'.
    { apply (Some_valid (to_tagKindR tkUnique,h')).
      rewrite -Some_valid -Eqh'. apply VALID. }
    destruct (heapletR_elem_of_dom _ _ VALh' Inl) as [s Eqs].
    specialize (PINV _ _ Eqs) as [_ PINV].
    specialize (PINV _ Eqstk _ _ Instk NDIS) as (Eqss & HD).
    destruct (for_each_lookup _ _ _ _ _ Eqα') as [EQ1 _].
    rewrite Eqlt in HLLt.
    specialize (EQ1 _ _ HLLt Eqstk) as (stk' & Eqstk' & EQ2).
    move : EQ2. case access1 as [[n1 stk1]|] eqn:EQ3; [|done].
    simpl. inversion 1. subst stk1.
    have ND := proj2 (state_wf_stack_item _ WFT _ _ Eqstk).
    admit.
  }
  exists (Val vs), σs', (r ⋅ (core (r_f ⋅ r))), (S n). split; last split.
  { left. by constructor 1. }
  { rewrite cmra_assoc -CORE.
    split; last split; last split; last split; last split; last split.
    - by apply (tstep_wf _ _ _ STEPS WFS).
    - by apply (tstep_wf _ _ _ STEPT WFT).
    - done.
    - intros t1 k h Eqt. specialize (PINV t1 k h Eqt) as [Lt PI]. subst σt'. simpl.
      split; [done|]. intros l' s' Eqk'.
      specialize (PI _ _ Eqk') as [? PI]. split; [done|].
      intros stk' Eqstk'.
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
      destruct (access1 stk AccessRead (Tagged t) σt.(scs)) as [[n stk1]|] eqn:Eqstk';
        [|done]. simpl in MR. simplify_eq.
      destruct (state_wf_stack_item _ WFT _ _ Eqstk). move : Eqstk' HTOP.
      destruct k.
      + eapply access1_head_preserving; eauto.
      + eapply access1_active_SRO_preserving; eauto.
    - intros c cs Eqc. specialize (CINV _ _ Eqc). subst σt'. simpl.
      clear -Eqα' CINV. destruct cs as [[T|]| |]; [|done..].
      destruct CINV as [IN CINV]. split; [done|].
      intros t1 InT. specialize (CINV _ InT) as [? CINV]. split; [done|].
      intros k h Eqt l' Inh.
      destruct (CINV _ _ Eqt _ Inh) as (stk' & pm' & Eqstk' & Instk' & NDIS).
      destruct (for_each_access1_active_preserving _ _ _ _ _ _ _ Eqα' _ _ Eqstk')
        as [stk [Eqstk AS]].
      exists stk, pm'. split; last split; [done| |done]. by apply AS.
    - subst σt'. rewrite /srel /=. by destruct SREL as (?&?&?&?&?).
    - intros ??? IN. specialize (LINV _ _ _ IN) as [Eq1 Eq2]. by subst σt'. }
  left.
  apply (sim_body_result _ _ _ _ (ValR vs) (ValR vt)). intros.
  have VREL2: vrel (r ⋅ (core (r_f ⋅ r))) vs vt.
  { eapply vrel_mono; [done| |exact VREL']. apply cmra_included_r. }
  subst σt'. apply POST; eauto.
Abort.

Lemma sim_body_copy_raw fs ft r n l tg Ts Tt σs σt Φ
  (EQS: tsize Ts = tsize Tt) :
  (∀ vs vt,
    read_mem l (tsize Ts) σs.(shp) = Some vs →
    read_mem l (tsize Tt) σt.(shp) = Some vt →
    ∀ α', memory_read σt.(sst) σt.(scs) l tg (tsize Tt) = Some α' →
      let σs' := mkState σs.(shp) α' σs.(scs) σs.(snp) σs.(snc) in
      let σt' := mkState σt.(shp) α' σt.(scs) σt.(snp) σt.(snc) in
      Φ r n (ValR vs) σs' (ValR vt) σt' : Prop) →
  r ⊨{n,fs,ft} (Copy (Place l tg Ts), σs) ≥ (Copy (Place l tg Tt), σt) : Φ.
Proof.
  intros POST. pfold.
  intros NT. intros.
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  split; [|done|].
  { right.
    destruct (NT (Copy (Place l tg Ts)) σs) as [[]|[es' [σs' STEPS]]]; [done..|].
    destruct (tstep_copy_inv _ _ _ _ _ _ _ STEPS)
      as (vs & α' & ? & Eqvs & Eqα' & ?).
    subst es'.
    destruct (read_mem_is_Some l (tsize Tt) σt.(shp)) as [vt Eqvt].
    { intros m. rewrite (srel_heap_dom _ _ _ WFS WFT SREL) -EQS.
      apply (read_mem_is_Some' l (tsize Ts) σs.(shp)). by eexists. }
    have Eqα'2: memory_read σt.(sst) σt.(scs) l tg (tsize Tt) = Some α'.
    { destruct SREL as (Eqst&?&Eqcs&?). by rewrite -Eqst -Eqcs -EQS. }
    exists (#vt)%E, (mkState σt.(shp) α' σt.(scs) σt.(snp) σt.(snc)).
    by eapply (head_step_fill_tstep _ []), copy_head_step'. }
  constructor 1. intros.
  destruct (tstep_copy_inv _ _ _ _ _ _ _ STEPT) as (vt & α' & ? & Eqvt & Eqα' & ?).
  subst et'.
  destruct (read_mem_is_Some l (tsize Ts) σs.(shp)) as [vs Eqvs].
  { intros m. rewrite -(srel_heap_dom _ _ _ WFS WFT SREL) EQS.
    apply (read_mem_is_Some' l (tsize Tt) σt.(shp)). by eexists. }
  have Eqα'2: memory_read σs.(sst) σs.(scs) l tg (tsize Ts) = Some α'.
  { destruct SREL as (Eqst&?&Eqcs&?). by rewrite Eqst Eqcs EQS. }
  set σs' := mkState σs.(shp) α' σs.(scs) σs.(snp) σs.(snc).
  have STEPS: (Copy (Place l tg Ts), σs) ~{fs}~> ((#vs)%E, σs').
  { by eapply (head_step_fill_tstep _ []), copy_head_step'. }
  exists (Val vs), σs', r, (S n). split; last split.
  { left. by constructor 1. }
  { split; last split; last split; last split; last split; last split.
    - by apply (tstep_wf _ _ _ STEPS WFS).
    - by apply (tstep_wf _ _ _ STEPT WFT).
    - done.
    - intros t k h Eqt. specialize (PINV t k h Eqt) as [Lt PI]. subst σt'. simpl.
      split; [done|]. intros l' s' Eqk'. specialize (PI _ _ Eqk') as [? PI].
      split; [done|]. intros stk' Eqstk'.
      destruct (for_each_access1 _ _ _ _ _ _ _ Eqα' _ _ Eqstk')
        as (stk & Eqstk & SUB & ?).
      intros pm opro In' NDIS.
      destruct (SUB _ In') as (it2 & In2 & Eqt2 & Eqp2 & NDIS2).
      destruct (PI _ Eqstk it2.(perm) opro) as [Eql' HTOP].
      { simpl in *. rewrite /= Eqt2 Eqp2. by destruct it2. }
      { simpl in *. by rewrite (NDIS2 NDIS). }
      split; [done|].
      destruct (for_each_lookup_case _ _ _ _ _ Eqα' _ _ _ Eqstk Eqstk')
        as [?|[MR _]]; [by subst|]. clear -In' MR HTOP Eqstk WFT NDIS.
      destruct (access1 stk AccessRead tg σt.(scs)) as [[n stk1]|] eqn:Eqstk';
        [|done]. simpl in MR. simplify_eq.
      destruct (state_wf_stack_item _ WFT _ _ Eqstk). move : Eqstk' HTOP.
      destruct k.
      + eapply access1_head_preserving; eauto.
      + eapply access1_active_SRO_preserving; eauto.
    - intros c cs Eqc. specialize (CINV _ _ Eqc). subst σt'. simpl.
      clear -Eqα' CINV. destruct cs as [[T|]| |]; [|done..].
      destruct CINV as [IN CINV]. split; [done|].
      intros t InT. specialize (CINV _ InT) as [? CINV]. split; [done|].
      intros k h Eqt l' Inh.
      destruct (CINV _ _ Eqt _ Inh) as (stk' & pm' & Eqstk' & Instk' & NDIS).
      destruct (for_each_access1_active_preserving _ _ _ _ _ _ _ Eqα' _ _ Eqstk')
        as [stk [Eqstk AS]].
      exists stk, pm'. split; last split; [done| |done]. by apply AS.
    - subst σt'. rewrite /srel /=. by destruct SREL as (?&?&?&?&?).
    - intros ??? IN. specialize (LINV _ _ _ IN) as [Eq1 Eq2]. by subst σt'. }
  left. pfold. split; last first.
  { constructor 1. intros vt' ? STEPT'. exfalso.
    have ?: to_result (Val vt) = None.
    { eapply (tstep_reducible_not_result ft _ σt'); eauto. by do 2 eexists. }
    done. }
  { move => ? /= Eqvt'. symmetry in Eqvt'. simplify_eq.
    exists (ValR vs), σs', r, n. split; last split.
    - right. split; [lia|]. eauto.
    - eauto.
    - by apply POST. }
  { left. by eexists. }
Qed.

(** Write *)
Fixpoint write_heaplet (l: loc) (v: value) (h: gmapR loc (agreeR scalarC)) :=
  match v with
  | [] => h
  | s :: v =>
      write_heaplet (l +ₗ 1) v (if h !! l then <[l := to_agree s]> h else h)
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

Lemma write_heaplet_valid l v h:
  ✓ h → ✓ (write_heaplet l v h).
Proof.
  revert l h. induction v as [|s v IH]; intros l h VALID; simpl; [done|].
  apply IH. destruct (h !! l) eqn:Eql; [|done]. by apply insert_valid.
Qed.

Lemma write_heaplet_lookup (l: loc) (vl: value) (h: heapletR) :
  (∀ (i: nat) s, (i < length vl)%nat →
    write_heaplet l vl h !! (l +ₗ i) ≡ Some s →
    Some s ≡ to_agree <$> vl !! i) ∧
  (∀ (l': loc), (∀ (i: nat), (i < length vl)%nat → l' ≠ l +ₗ i) →
    write_heaplet l vl h !! l' ≡ h !! l').
Proof.
  revert l h. induction vl as [|v vl IH]; move => l h; simpl;
    [split; [intros; by lia|done]|].
  destruct (IH (l +ₗ 1) (if h !! l then <[l:=to_agree v]> h else h)) as [IH1 IH2].
  split.
  - intros i s Lt. destruct i as [|i].
    + rewrite shift_loc_0_nat /=. rewrite IH2; [|].
      * destruct (h !! l) eqn:Eql; [by rewrite lookup_insert|].
        rewrite Eql; by inversion 1.
      * move => ? _.
        rewrite shift_loc_assoc -{1}(shift_loc_0 l) => /shift_loc_inj ?. by lia.
    + intros Eq.  rewrite /= -IH1; [eauto|lia|].
      by rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
  - intros l' Lt. rewrite IH2.
    + destruct (h !! l) eqn:Eql; [|done].
      rewrite lookup_insert_ne; [done|].
      move => ?. subst l'. apply (Lt O); [lia|by rewrite shift_loc_0_nat].
    + move => i Lti. rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
      apply Lt. by lia.
Qed.

Lemma sim_body_write_related_values
  fs ft (r: resUR) k0 h0 n l tg Ts Tt v σs σt Φ
  (EQS: tsize Ts = tsize Tt)
  (Eqtg: r.(rtm) !! tg = Some (to_tagKindR k0, h0))
  (SHR: ∀ i, (i < tsize Tt)%nat → r.(rlm) !! (l +ₗ i) ≡ Some $ to_locStateR lsShared)
  (* assuming to-write values are related *)
  (PUBWRITE: ∀ s, s ∈ v → arel r s s) :
  let r' := if k0 then
            ((<[tg := (to_tagKindR tkUnique,  write_heaplet l v h0)]> r.(rtm),
              r.(rcm)), r.(rlm))
            else r in
  (∀ α', memory_written σt.(sst) σt.(scs) l (Tagged tg) (tsize Tt) = Some α' →
    let σs' := mkState (write_mem l v σs.(shp)) α' σs.(scs) σs.(snp) σs.(snc) in
    let σt' := mkState (write_mem l v σt.(shp)) α' σt.(scs) σt.(snp) σt.(snc) in
    Φ r' n ((#[☠])%V) σs' ((#[☠]%V)) σt' : Prop) →
  r ⊨{n,fs,ft}
    (Place l (Tagged tg) Ts <- #v, σs) ≥ (Place l (Tagged tg) Tt <- #v, σt) : Φ.
Proof.
  intros r' POST. pfold.
  intros NT. intros.
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  split; [|done|].
  { right.
    edestruct NT as [[]|[es' [σs' STEPS]]]; [constructor 1|done|].
    destruct (tstep_write_inv _ _ _ _ _ _ _ _ STEPS)
      as (α' & ? & Eqα' & EqD & IN & EQL & ?).
    subst es'. setoid_rewrite <-(srel_heap_dom _ _ _ WFS WFT SREL) in EqD.
    destruct SREL as (Eqst&Eqnp&Eqcs&Eqnc&AREL).
    rewrite Eqst Eqcs EQS in Eqα'. rewrite -EQL in EQS.
    rewrite EQS in EqD. rewrite Eqnp in IN.
    exists (#[☠])%V,
           (mkState (write_mem l v σt.(shp)) α' σt.(scs) σt.(snp) σt.(snc)).
    by eapply (head_step_fill_tstep _ []), write_head_step'. }
  constructor 1. intros.
  destruct (tstep_write_inv _ _ _ _ _ _ _ _ STEPT)
    as (α' & ? & Eqα' & EqD & IN & EQL & ?). subst et'.
  set σs' := mkState (write_mem l v σs.(shp)) α' σs.(scs) σs.(snp) σs.(snc).
  have STEPS: ((Place l (Tagged tg) Ts <- v)%E, σs) ~{fs}~> ((#[☠])%V, σs').
  { setoid_rewrite (srel_heap_dom _ _ _ WFS WFT SREL) in EqD.
    destruct SREL as (Eqst&Eqnp&Eqcs&Eqnc&AREL).
    rewrite -Eqst -Eqcs -EQS in Eqα'. rewrite -EQS in EQL.
    rewrite EQL in EqD. rewrite -Eqnp in IN.
    eapply (head_step_fill_tstep _ []), write_head_step'; eauto. }
  have HL: if k0 then ∀ kh, r_f.(rtm) ⋅ <[tg:=kh]> r.(rtm) = <[tg:=kh]> (r_f.(rtm) ⋅ r.(rtm)) else True.
  { destruct k0; [|done]. intros.
    rewrite (tmap_insert_op_r r_f.(rtm) r.(rtm) tg h0) //. apply VALID. }
  have HL2: if k0 then  (r_f.(rtm) ⋅ r.(rtm)) !! tg = Some (to_tagKindR tkUnique, h0) else True.
  { destruct k0; [|done].
    by apply (tmap_lookup_op_r _ _ _ _ (proj1 (proj1 VALID)) Eqtg). }
  exists (#[☠])%V, σs', r', (S n). split; last split.
  { left. by constructor 1. }
  { split; last split; last split; last split; last split; last split.
    - by apply (tstep_wf _ _ _ STEPS WFS).
    - by apply (tstep_wf _ _ _ STEPT WFT).
    - (* valid *)
      rewrite /r'. destruct k0; [|done]. do 2 (split; [|apply VALID]).
      eapply tmap_valid; eauto; [|apply VALID]. split; [done|].
      apply write_heaplet_valid.
      have VL := (proj1 (proj1 (cmra_valid_op_r _ _ VALID)) tg).
      rewrite Eqtg in VL. apply VL.
    - (* tmap_inv *)
      intros t k h Eqt.
      have Eqttg: t = tg → k0 = tkUnique → k = k0 ∧ h ≡ write_heaplet l v h0.
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
      { subst σt'. simpl. destruct CASEt as [(?&?&?&?Eqh)|[Eqh NEQ]].
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
          have VALS := proj1 (proj1 (cmra_valid_op_r _ _ VALID)) tg. rewrite Eqtg in VALS.
          have VALs0: ✓ s0. { change (✓ (Some s0)). rewrite -Eqs0. apply VALS. }
          apply to_agree_uninj in VALs0 as [ss0 Eqss0].
          destruct (PI l' ss0) as [? _]; [|done]. by rewrite Eqs0 Eqss0.
        - specialize (PINV _ _ _ Eqh) as [? PINV].
          specialize (PINV _ _ Eqk') as [EQ _]. rewrite /r' /=. by destruct k0. }
      intros stk'. subst σt'. simpl.
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
          destruct (for_each_lookup _ _ _ _ _ Eqα') as [EQ1 _].
          rewrite EQL in Lti. destruct (EQ1 _ _ Lti Eqstk) as [ss' [Eq' EQ2]].
          have ?: ss' = stk'. { rewrite Eqstk' in Eq'. by inversion Eq'. }
          subst ss'. clear Eq'. move : EQ2. case access1 as [[n1 stk1]|] eqn:EQ3; [|done].
          simpl. intros ?. simplify_eq.
          specialize (NEQ eq_refl).
          have ND := proj2 (state_wf_stack_item _ WFT _ _ Eqstk).
          move : In'.
          eapply (access1_write_remove_incompatible_head _ tg t _ _ _ ND);
            [by eexists|done..].
        * (* if k is Public => t is for SRO, and must also have been popped,
             contradicting In'. *)
          destruct (for_each_lookup _ _ _ _ _ Eqα') as [EQ1 _].
          rewrite EQL in Lti. destruct (EQ1 _ _ Lti Eqstk) as [ss' [Eq' EQ2]].
          have ?: ss' = stk'. { rewrite Eqstk' in Eq'. by inversion Eq'. }
          subst ss'. clear Eq'. move : EQ2. case access1 as [[n1 stk1]|] eqn:EQ3; [|done].
          simpl. intros ?. simplify_eq.
          have ND := proj2 (state_wf_stack_item _ WFT _ _ Eqstk).
          move : In'.
          eapply (access1_write_remove_incompatible_active_SRO _ tg t _ _ _ ND); eauto.
    - (* cmap_inv : make sure tags in the new resource are still on top *)
      intros c cs Eqc'.
      have Eqc: (r_f ⋅ r).(rcm) !! c ≡ Some cs.
      { move  : Eqc'. rewrite /r'. by destruct k0. }
      specialize (CINV _ _ Eqc). subst σt'. simpl.
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
      subst σt'. rewrite /srel /=. destruct SREL as (?&?&?&?&Eq).
      repeat split; [done..|].
      intros l1 InD1 Eq1.
      destruct (write_mem_lookup l v σs.(shp)) as [EqN EqO]. rewrite /r'.
      destruct (write_mem_lookup_case l v σt.(shp) l1)
        as [[i [Lti [Eqi Eqmi]]]|[NEql Eql]].
      + subst l1. specialize (EqN _ Lti). (* rewrite EqN. *)
        have InD := (EqD _ Lti).
        have Eq1' : (r_f ⋅ r).(rlm) !! (l +ₗ i) ≡ Some $ to_locStateR lsShared
          by destruct k0. specialize (Eq _ InD Eq1').
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
        have InD1': l1 ∈ dom (gset loc) σt.(shp)
          by rewrite elem_of_dom -Eql -(elem_of_dom (D:=gset loc)).
        have Eq1' : (r_f ⋅ r).(rlm) !! l1 ≡ Some $ to_locStateR lsShared.
        { move : Eq1. by destruct k0. }
        specialize (Eq _ InD1' Eq1'). rewrite /pub_loc EqO Eql.
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
    - intros l' s' stk' Eq.
      have Eq' : rlm (r_f ⋅ r) !! l' ≡ Some (to_locStateR (lsLocal s' stk')) by destruct k0.
      specialize (LINV _ _ _ Eq').
      subst σt'. rewrite /=.
      destruct (write_mem_lookup l v σs.(shp)) as [_ HLs].
      destruct (write_mem_lookup l v σt.(shp)) as [_ HLt].
      have ?: ∀ i, (i < length v)%nat → l' ≠ l +ₗ i.
      { intros i Lti EQ. rewrite EQL in Lti. specialize (SHR _ Lti).
        subst l'. apply (lmap_lookup_op_r r_f.(rlm)) in SHR; [|apply VALID].
        move : Eq'. rewrite SHR. intros Eqv%Some_equiv_inj. inversion Eqv. }
      rewrite HLs // HLt //.
  }
  left.
  eapply (sim_body_result fs ft r' n (ValR [☠%S]) (ValR [☠%S])).
  intros. simpl. subst σt'. by apply POST.
Qed.

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
      Φ r n ((#[☠])%V) σs' ((#[☠]%V)) σt' : Prop) →
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
  r ⋅ r' ⊨{n,fs,ft} (es, σs') ≥ (et, σt') : Φ →
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
  exists n. split; last split; cycle 2.
  { (* sim cont *)  by punfold SIM. }
  { (* STEP src *)  left. by apply tc_once. }
  (* WSAT new *)
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  rewrite assoc.
  split; last split; last split; last split; last split; last split.
  { (* WF src *)    by apply (tstep_wf _ _ _ STEPS WFS). }
  { (* WF tgt *)    by apply (tstep_wf _ _ _ STEPT WFT). }
  { (* VALID *)
    apply (local_update_discrete_valid_frame (r_f ⋅ r) ε r'); [|done].
    by rewrite right_id. }
  { (* tmap_inv *)
    move => t k h /=. rewrite /rtm /= right_id. move => /PINV [? PI].
    split; [done|]. intros ???. rewrite right_id. by apply PI. }
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
    do 2 (split; [done|]). do 2 (split; [simpl; by f_equal|]).
    move => l InD. rewrite {1}/r' /= right_id => SHR.
    destruct (SREL _ InD SHR) as [PUB|[t [c [T [h [PRI [? ?]]]]]]]; [left|right].
    - move => st /PUB [ss [Eqss AREL]]. exists ss. split; [done|]. move : AREL.
      rewrite /arel /=.
      destruct st, ss as [| |l2 [|]|]; auto.
      by setoid_rewrite (right_id _ _ (r_f.(rtm) ⋅ r.(rtm))).
    - exists t, c, T, h. rewrite /rtm /= right_id. split; [|done].
      rewrite /rcm /= (comm _ (r_f.(rcm) ⋅ r.(rcm))) -insert_singleton_op //.
      rewrite lookup_insert_ne // => Eqc. subst c.
      apply (lt_irrefl σt.(snc)), (cinv_lookup_in _ _ _ _ WFT CINV PRI). }
  { intros ???. rewrite /lmap_inv /= right_id. apply LINV. }
Qed.

(** EndCall *)
Lemma end_call_tstep_src_tgt fs ft r σs σt (vs vt: value) es' σs' :
  wsat r σs σt →
  (EndCall vs, σs) ~{fs}~> (es', σs') →
  reducible ft (EndCall vt) σt.
Proof.
  intros WSAT STEPS.
  edestruct (tstep_end_call_inv _ vs _ _ _ (ltac:(by eexists))
                STEPS) as (vs' & Eqvs & ? & c & cids & Eqc & Eqs).
  subst. simpl in Eqvs. symmetry in Eqvs. simplify_eq.
  destruct WSAT as (?&?&?&?&?&SREL&?). destruct SREL as (? & ? & Eqcs' & ?).
  exists (#vt)%E, (mkState σt.(shp) σt.(sst) cids σt.(snp) σt.(snc)).
  eapply (head_step_fill_tstep _ []).
  econstructor. by econstructor. econstructor. by rewrite -Eqcs'.
Qed.

Lemma sim_body_end_call fs ft r n vs vt σs σt Φ :
  (* return values are related *)
  vrel r vs vt →
  (* and any private location w.r.t to the current call id ownership must be related *)
  end_call_sat r σs σt →
  (∀ c1 c2 cids1 cids2, σs.(scs) = c1 :: cids1 → σt.(scs) = c2 :: cids2 →
      let σs' := mkState σs.(shp) σs.(sst) cids1 σs.(snp) σs.(snc) in
      let σt' := mkState σt.(shp) σt.(sst) cids2 σt.(snp) σt.(snc) in
      let r2' := match (r.(rcm) !! c2) with
                 | Some (Cinl (Excl T)) => <[c2 := to_callStateR csPub]> r.(rcm)
                 | _ => r.(rcm)
                 end in
      Wf σt → vrel_expr ((r.(rtm), r2'), r.(rlm)) vs vt →
      Φ ((r.(rtm), r2'), r.(rlm)) n (ValR vs) σs' (ValR vt) σt' : Prop) →
  r ⊨{n,fs,ft} (EndCall (Val vs), σs) ≥ (EndCall (Val vt), σt) : Φ.
Proof.
  intros VREL ESAT POST. pfold. intros NT r_f WSAT.
  split; [|done|].
  { right.
    destruct (NT (EndCall #vs) σs) as [[]|[es' [σs' STEPS]]]; [done..|].
    move : WSAT STEPS. apply end_call_tstep_src_tgt. }
  constructor 1. intros et' σt' STEPT.
  destruct (tstep_end_call_inv _ #vt _ _ _ (ltac:(by eexists)) STEPT)
    as (vt' & Eqvt & ? & c & cids & Eqc & Eqs).
  subst. simpl in Eqvt. symmetry in Eqvt. simplify_eq.
  rewrite /end_call_sat Eqc in ESAT.
  destruct (ESAT _ eq_refl) as [[cs Eqcs] ESAT']. clear ESAT.
  set σs' := (mkState σs.(shp) σs.(sst) cids σs.(snp) σs.(snc)).
  have STEPS: (EndCall #vs, σs) ~{fs}~> ((#vs)%E, σs').
  { destruct WSAT as (?&?&?&?&?&SREL&?). destruct SREL as (? & ? & Eqcs' & ?).
    eapply (head_step_fill_tstep _ []).
    econstructor. by econstructor. econstructor. by rewrite Eqcs'. }
  exists (Val vs), σs'.
  set r2' := match (r.(rcm) !! c) with
             | Some (Cinl (Excl T)) => <[c := to_callStateR csPub]> r.(rcm)
             | _ => r.(rcm)
             end.
  exists ((r.(rtm), r2'), r.(rlm)), (S n).
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL & LINV).
  split; last split.
  { left. by constructor 1. }
  { have VALID': ✓ (r_f ⋅ ((r.(rtm), r2'), r.(rlm))).
    { apply (local_update_discrete_valid_frame _ _ _ VALID).
      destruct (r.(rcm) !! c) as [[[T|]| |]|] eqn:Eqr2; rewrite /r2';
        [|by destruct r_f as [[]], r as [[]]..].
      destruct r_f as [[r_f1 r_f2] r_f3], r as [[r1 r2] r3]. rewrite 2!pair_op /=.
      apply prod_local_update_1, prod_local_update_2.
      rewrite (cmap_insert_op_r r_f2 r2 c T); [|apply VALID|exact Eqr2].
      apply (insert_local_update _ _ _
              (to_callStateR (csOwned T)) (to_callStateR (csOwned T)));
        [|done|by apply exclusive_local_update].
      apply cmap_lookup_op_r; [apply VALID|exact Eqr2]. }
    destruct r_f as [[r_f1 r_f2] r_f3].
    split; last split; last split; last split; last split; last split.
    - by apply (tstep_wf _ _ _ STEPS WFS).
    - by apply (tstep_wf _ _ _ STEPT WFT).
    - done.
    - rewrite pair_op. apply PINV.
    - rewrite pair_op. intros c1 cs1. simpl.
      case (decide (c1 = c)) => [->|NEqc]; last first.
      + rewrite (_: (r_f2 ⋅ r2') !! c1 = (r_f2 ⋅ r.(rcm)) !! c1); last first.
        { rewrite /r2'. destruct (r.(rcm) !! c) as [[[T|]| |]|]; [|done..].
          by rewrite 2!lookup_op lookup_insert_ne. }
        intros Eqcs1. move : (CINV _ _ Eqcs1). clear -NEqc Eqc.
        destruct cs1 as [[T|]| |]; [|done..]. rewrite Eqc.
        move => [/elem_of_cons IN ?]. split; [|done].
        destruct IN; [by subst|done].
      + intros Eqcs1.
        have VALID1: ✓ cs1. { rewrite -Some_valid -Eqcs1. apply VALID'. }
        destruct cs1 as [[T|]| |]; [|done| |done]; last first.
        { apply (state_wf_cid_agree _ WFT). rewrite Eqc. by left. }
        (* TODO: move out *)
        exfalso. move : Eqcs1. rewrite /r2' lookup_op.
        destruct (r.(rcm) !! c) as [[[T'|]| |]|] eqn:Eqc2;
          [rewrite lookup_insert|rewrite Eqc2..|done]; clear;
          (destruct (r_f2 !! c) as [cs|] eqn:Eqrf2; rewrite Eqrf2 ;
            [rewrite -Some_op /=; intros Eq%Some_equiv_inj
            |rewrite left_id /=; intros Eq%Some_equiv_inj;
              by inversion Eq; simplify_eq]);
          destruct cs as [[]| |]; by inversion Eq; simplify_eq.
    - destruct SREL as (Eqst & Eqnp & Eqcs' & Eqnc & Eqhp).
      do 4 (split; [done|]). rewrite /= /r2'.
      destruct (r.(rcm) !! c) as [[[T|]| |]|] eqn:Eqc2; [|apply Eqhp..].
      intros l InD SHR.
      specialize (Eqhp _ InD SHR) as [PUB|[t PV]]; [by left|].
      destruct PV as (c' & T' & h & Eqc' & InT' & Eqt & Inh). simpl in *.
      case (decide (c' = c)) => ?; last first.
      { right. exists t, c', T', h. repeat split; [|done..].
        by rewrite /= lookup_op lookup_insert_ne // -lookup_op. }
      subst c'.
      have Eq2 := cmap_lookup_op_r r_f2 r.(rcm) _ _ (proj2 (proj1 VALID)) Eqc2.
      rewrite Eq2 in Eqc'.
      apply Some_equiv_inj, Cinl_inj, Excl_inj, leibniz_equiv_iff in Eqc'.
      subst T'. specialize (ESAT' ((r_f1, r_f2), r_f3) VALID T).
      rewrite /= Eq2 in ESAT'.
      left. intros st Eqs.
      destruct (ESAT' (ltac:(done)) _ InT' _ Eqt _ _ Inh Eqs) as [ss [Eqss AR]].
      by exists ss.
    - intros ???. rewrite /=. apply LINV. }
  (* result *)
  left. apply (sim_body_result _ _ _ _ (ValR vs) (ValR vt)).
  have ?: vrel_expr ((r.(rtm), r2'), r.(rlm)) vs vt by do 2 eexists; eauto.
  intros VALID'.
  eapply POST; eauto. destruct SREL as (?&?&Eqs&?). by rewrite Eqs.
Qed.

Lemma sim_body_end_call_elim' fs ft r n vs vt σs σt Φ :
  r ⊨{n,fs,ft} (EndCall (Val vs), σs) ≥ (EndCall (Val vt), σt) : Φ →
  ∀ r_f et' σt' (WSAT: wsat (r_f ⋅ r) σs σt)
    (NT: never_stuck fs (EndCall (Val vs)) σs)
    (STEPT: (EndCall (Val vt), σt) ~{ft}~> (et', σt')),
  ∃ r' idx' σs', (EndCall (Val vs), σs) ~{fs}~>+ (Val vs, σs') ∧ et' = Val vt ∧
    Φ r' idx' (ValR vs) σs' (ValR vt) σt' ∧
    wsat (r_f ⋅ r') σs' σt'.
Proof.
  intros SIM r_f et' σt' WSAT NT STEPT.
  punfold SIM.
  specialize (SIM NT _ WSAT) as [NOSK TERM STEPSS].
  inversion STEPSS; last first.
  { exfalso. clear -CALLTGT. symmetry in CALLTGT.
    apply fill_end_call_decompose in CALLTGT as [[]|[K' [? Eq]]]; [done|].
    destruct (fill_result ft K' (Call #[ScFnPtr fid] el_tgt)) as [[] ?];
      [rewrite Eq; by eexists|done]. }
  specialize (STEP _ _ STEPT) as (es1 & σs1 & r1 & n1 & STEP1 & WSAT1 & SIMV).
  have STEPK: (EndCall #vs, σs) ~{fs}~>* (es1, σs1).
  { destruct STEP1 as [|[]]. by apply tc_rtc. by simplify_eq. }
  have NT1 := never_stuck_tstep_rtc _ _ _ _ _ STEPK NT.
  pclearbot. punfold SIMV.
  specialize (SIMV NT1 _ WSAT1) as [ST1 TE1 STEPS1].
  apply tstep_end_call_inv in STEPT as (? & Eq1 &? & ? & ? & ? & ?);
        [|by eexists]. simpl in Eq1. symmetry in Eq1. simplify_eq.
  specialize (TE1 vt eq_refl) as (vs2 & σs2 & r2 & idx2 & STEP2 & WSAT2 & POST).
  exists r2, idx2, σs2.
  have ?: vs2 = vs.
  { clear -STEP1 STEP2.
    destruct STEP1 as [STEP1|[Eq11 Eq12]]; [|simplify_eq].
    - apply tstep_end_call_inv_tc in STEP1 as (? & Eq1 &? & ? & ? & ? & ?);
        [|by eexists]. simpl in Eq1.
      simplify_eq. destruct STEP2 as [?%result_tstep_tc_stuck|[]]; [done|].
      simplify_eq.
      have Eq := to_of_result vs2. rewrite -H1 /= in Eq. by simplify_eq.
    - have Eq := to_of_result vs2.
      destruct STEP2 as [STEP2|[? STEP2]].
      + apply tstep_end_call_inv_tc in STEP2 as (? & Eq' &? & ? & ? & ? & ?);
          [|by eexists].
        simpl in Eq'. simplify_eq.
        rewrite H /= in Eq. by simplify_eq.
      + simplify_eq. by rewrite -H0 in Eq. }
  subst vs2. split; [|done].
  destruct STEP1 as [|[]], STEP2 as [|[]]; simplify_eq.
  - eapply tc_rtc_l; eauto.
  - done.
  - done.
Qed.

Lemma sim_body_end_call_elim fs ft r n vs vt σs σt Φ :
  r ⊨{n,fs,ft} (EndCall (Val vs), σs) ≥ (EndCall (Val vt), σt) : Φ →
  ∀ r_f σs' σt' (WSAT: wsat (r_f ⋅ r) σs σt)
    (NT: never_stuck fs (EndCall (Val vs)) σs)
    (STEPS: (EndCall (Val vs), σs) ~{fs}~> (Val vs, σs'))
    (STEPT: (EndCall (Val vt), σt) ~{ft}~> (Val vt, σt')),
  ∃ r' idx', Φ r' idx' (ValR vs) σs' (ValR vt) σt' ∧ wsat (r_f ⋅ r') σs' σt'.
Proof.
  intros SIM r_f σs' σt' WSAT NT STEPS STEPT.
  punfold SIM.
  specialize (SIM NT _ WSAT) as [NOSK TERM STEPSS].
  inversion STEPSS; last first.
  { exfalso. clear -CALLTGT. symmetry in CALLTGT.
    apply fill_end_call_decompose in CALLTGT as [[]|[K' [? Eq]]]; [done|].
    destruct (fill_result ft K' (Call #[ScFnPtr fid] el_tgt)) as [[] ?];
      [rewrite Eq; by eexists|done]. }
  specialize (STEP _ _ STEPT) as (es1 & σs1 & r1 & n1 & STEP1 & WSAT1 & SIMV).
  have STEPK: (EndCall #vs, σs) ~{fs}~>* (es1, σs1).
  { destruct STEP1 as [|[]]. by apply tc_rtc. by simplify_eq. }
  have NT1 := never_stuck_tstep_rtc _ _ _ _ _ STEPK NT.
  pclearbot. punfold SIMV.
  specialize (SIMV NT1 _ WSAT1) as [ST1 TE1 STEPS1].
  specialize (TE1 vt eq_refl) as (vs2 & σs2 & r2 & idx2 & STEP2 & WSAT2 & POST).
  exists r2, idx2.
  assert (σs2 = σs' ∧ vs2 = vs) as [].
  { clear -STEP1 STEP2 STEPS.
    apply tstep_end_call_inv in STEPS as (? & ? &? & ? & ? & ? & ?);
      [|by eexists].
    destruct STEP1 as [STEP1|[Eq11 Eq12]]; [|simplify_eq].
    - apply tstep_end_call_inv_tc in STEP1 as (? & ? &? & ? & ? & ? & ?);
        [|by eexists].
      simplify_eq. destruct STEP2 as [?%result_tstep_tc_stuck|[]]; [done|].
      simplify_eq.
      rewrite H1 in H5. simplify_eq. split; [done|].
      have Eq := to_of_result vs2. rewrite -H2 in Eq. by simplify_eq.
    - have Eq := to_of_result vs2. 
      destruct STEP2 as [STEP2|[? STEP2]].
      + apply tstep_end_call_inv_tc in STEP2 as (? & ? &? & ? & ? & ? & ?);
          [|by eexists].
        rewrite H1 in H3. simplify_eq. split; [done|].
        rewrite H2 in Eq. by simplify_eq.
      + simplify_eq. by rewrite -H2 in Eq. }
  subst σs2 vs2. done.
Qed.

(** PURE STEP ----------------------------------------------------------------*)

(** Call - step over *)
Lemma sim_body_step_over_call fs ft
  (Ks: list (ectxi_language.ectx_item (bor_ectxi_lang fs)))
  (Kt: list (ectxi_language.ectx_item (bor_ectxi_lang ft)))
  rc rv n fid els xlt et et' elt HCt σs σt Φ
  (VS  : Forall (λ ei, is_Some (to_value ei)) els)
  (VREL: Forall2 (vrel_expr rv) els elt)
  (FT: ft !! fid = Some (@FunV xlt et HCt))
  (VT : Forall (λ ei, is_Some (to_value ei)) elt)
  (ST: subst_l xlt elt et = Some et') :
  (∀ r' vs vt σs' σt' (VRET: vrel r' vs vt) (STACK: σt.(scs) = σt'.(scs)), ∃ n',
    rc ⋅ r' ⊨{n',fs,ft} (fill Ks (Val vs), σs') ≥ (fill Kt (Val vt), σt') : Φ) →
  rc ⋅ rv ⊨{n,fs,ft}
    (fill Ks (Call #[ScFnPtr fid] els), σs) ≥ (fill Kt (Call #[ScFnPtr fid] elt), σt) : Φ.
Proof.
  intros CONT. pfold. intros NT r_f WSAT. split.
  { right. exists (fill Kt (EndCall (InitCall et'))), σt.
     eapply (head_step_fill_tstep _ Kt). econstructor. by econstructor. }
  { intros vt. by rewrite fill_not_result. }
  eapply (sim_local_body_step_over_call _ _ _ _ _ _ _ _ _ _ _ _ _
            Ks _ fid elt els); eauto; [done|].
  intros r' ? ? σs' σt' (vs&vt&?&?&VR) STACK. simplify_eq.
  destruct (CONT _ _ _ σs' σt' VR STACK) as [n' ?].
  exists n'. by left.
Qed.

(** Call - step into *)
Lemma sim_body_step_into_call fs ft
  r n fid xls es HCs els es' xlt et HCt elt et' σs σt Φ
  (FS: fs !! fid = Some (@FunV xls es HCs))
  (VS : Forall (λ ei, is_Some (to_value ei)) els)
  (SS: subst_l xls els es = Some es')
  (FT: ft !! fid = Some (@FunV xlt et HCt))
  (VT : Forall (λ ei, is_Some (to_value ei)) elt)
  (ST: subst_l xlt elt et = Some et') :
  r ⊨{n,fs,ft} (EndCall (InitCall es'), σs) ≥ (EndCall (InitCall et'), σt) : Φ →
  r ⊨{n,fs,ft} (Call #[ScFnPtr fid] els, σs) ≥ (Call #[ScFnPtr fid] elt, σt) : Φ.
Proof.
  intros CONT. pfold. intros NT r_f WSAT. split; [|done|].
  { right. do 2 eexists. eapply (head_step_fill_tstep _ []).
    econstructor 1. econstructor; eauto. }
  econstructor 1. intros et1 σt' STEPT.
  destruct (tstep_call_inv _ _ _ _ _ _ VT STEPT) as (?&?&?&?&?&?&?&?). subst; simplify_eq.
  exists (EndCall (InitCall es')), σs, r, n. split; last split; [|done|by left].
  left. constructor 1.
  eapply (head_step_fill_tstep _ []). econstructor.
  by apply (CallBS _ _ _ els xls es HCs).
Qed.

(** Let *)
Lemma sim_body_let fs ft r n x es1 es2 et1 et2 σs σt Φ :
  terminal es1 → terminal et1 →
  r ⊨{n,fs,ft} (subst x es1 es2, σs) ≥ (subst x et1 et2, σt) : Φ →
  r ⊨{n,fs,ft} (let: x := es1 in es2, σs) ≥ ((let: x := et1 in et2), σt) : Φ.
Proof.
  intros TS TT SIM. pfold.
  intros NT r_f WSAT. split; [|done|].
  { right. do 2 eexists. eapply (head_step_fill_tstep _ []).
    econstructor 1. econstructor; eauto. }
  constructor 1. intros.
  destruct (tstep_let_inv _ _ _ _ _ _ _ TT STEPT). subst et' σt'.
  exists (subst x es1 es2), σs, r, n. split.
  { left. constructor 1. eapply (head_step_fill_tstep _ []).
    by econstructor; econstructor. }
  split; [done|]. by left.
Qed.

Lemma sim_body_let_val fs ft r n x (vs1 vt1: value) es2 et2 σs σt Φ :
  r ⊨{n,fs,ft} (subst x vs1 es2, σs) ≥ (subst x vt1 et2, σt) : Φ →
  r ⊨{n,fs,ft} (let: x := vs1 in es2, σs) ≥ ((let: x := vt1 in et2), σt) : Φ.
Proof. apply sim_body_let; eauto. Qed.

(** Ref *)
Lemma sim_body_ref fs ft r n l tgs tgt Ts Tt σs σt Φ :
  r ⊨{n,fs,ft} (#[ScPtr l tgs], σs) ≥ (#[ScPtr l tgt], σt) : Φ →
  r ⊨{n,fs,ft} ((& (Place l tgs Ts))%E, σs) ≥ ((& (Place l tgt Tt))%E, σt) : Φ.
Proof.
  intros SIM. pfold.
  intros NT r_f WSAT. split; [|done|].
  { right.
    destruct (NT (& (Place l tgs Ts))%E σs) as [[]|[es' [σs' STEPS]]]; [done..|].
    destruct (tstep_ref_inv _ _ _ _ _ _ _ STEPS) as [? [? IS]]. subst es' σs'.
    have ?: is_Some (σt.(shp) !! l).
    { clear -WSAT IS. move : IS.
      by rewrite -2!(elem_of_dom (D:=gset loc)) -wsat_heap_dom. }
    exists #[ScPtr l tgt]%E, σt.
    eapply (head_step_fill_tstep _ []). by econstructor; econstructor. }
  constructor 1. intros.
  destruct (tstep_ref_inv _ _ _ _ _ _ _ STEPT) as [? [? IS]]. subst et' σt'.
  have ?: is_Some (σs.(shp) !! l).
  { clear -WSAT IS. move : IS.
    by rewrite -2!(elem_of_dom (D:=gset loc)) wsat_heap_dom. }
  exists #[ScPtr l tgs]%E, σs, r, n. split.
  { left. constructor 1. eapply (head_step_fill_tstep _ []).
    by econstructor; econstructor. }
  split; [done|]. by left.
Qed.

(** Deref *)
Lemma sim_body_deref fs ft r n l tgs tgt Ts Tt σs σt Φ
  (EQS: tsize Ts = tsize Tt) :
  r ⊨{n,fs,ft} (Place l tgs Ts, σs) ≥ (Place l tgt Tt, σt) : Φ →
  r ⊨{n,fs,ft} (Deref #[ScPtr l tgs] Ts, σs) ≥ (Deref #[ScPtr l tgt] Tt, σt) : Φ.
Proof.
  intros SIM. pfold.
  intros NT r_f WSAT. split; [|done|].
  { right.
    destruct (NT (Deref #[ScPtr l tgs] Ts) σs) as [[]|[es' [σs' STEPS]]]; [done..|].
    destruct (tstep_deref_inv _ _ _ _ _ _ _ STEPS) as [? [? IS]]. subst es' σs'.
    have ?: (∀ (i: nat), (i < tsize Tt)%nat → l +ₗ i ∈ dom (gset loc) σt.(shp)).
    { clear -WSAT IS EQS. rewrite -EQS. move => i /IS. by rewrite -wsat_heap_dom. }
    exists (Place l tgt Tt), σt.
    eapply (head_step_fill_tstep _ []). by econstructor; econstructor. }
  constructor 1. intros.
  destruct (tstep_deref_inv _ _ _ _ _ _ _ STEPT) as [? [? IS]]. subst et' σt'.
  have ?: (∀ (i: nat), (i < tsize Ts)%nat → l +ₗ i ∈ dom (gset loc) σs.(shp)).
  { clear -WSAT IS EQS. rewrite EQS. move => i /IS. by rewrite wsat_heap_dom. }
  exists (Place l tgs Ts), σs, r, n. split.
  { left. constructor 1. eapply (head_step_fill_tstep _ []).
    by econstructor; econstructor. }
  split; [done|]. by left.
Qed.
