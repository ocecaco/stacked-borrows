From iris.algebra Require Import local_updates.

From stbor.lang Require Import steps_progress steps_inversion.
From stbor.sim Require Import local invariant.

Set Default Proof Using "Type".

Notation "r ⊨{ n , fs , ft } ( es , σs ) ≥ ( et , σt ) : Φ" :=
  (sim_local_body wsat vrel_expr fs ft r n%nat es%E σs et%E σt Φ)
  (at level 70, format "r  ⊨{ n , fs , ft }  ( es ,  σs )  ≥  ( et ,  σt )  :  Φ").

Notation "⊨{ fs , ft } f1 ≥ᶠ f2" :=
  (sim_local_fun wsat vrel_expr fs ft f1 f2)
  (at level 70, format "⊨{ fs , ft }  f1  ≥ᶠ  f2").

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


Lemma sim_body_bind fs ft r n
  (Ks: list (ectxi_language.ectx_item (bor_ectxi_lang fs)))
  (Kt: list (ectxi_language.ectx_item (bor_ectxi_lang ft))) es et σs σt Φ :
  r ⊨{n,fs,ft} (es, σs) ≥ (et, σt)
    : (λ r' n' es' σs' et' σt',
        r' ⊨{n',fs,ft} (fill Ks es', σs') ≥ (fill Kt et', σt') : Φ) →
  r ⊨{n,fs,ft} (fill Ks es, σs) ≥ (fill Kt et, σt) : Φ.
Proof.
  revert r n Ks Kt es et σs σt Φ. pcofix CIH.
  intros r1 n Ks Kt es et σs σt Φ SIM. pfold. punfold SIM. intros NT ??.
  have NT2 := never_stuck_fill_inv _ _ _ _ NT.
  destruct (SIM NT2 _ WSAT) as [NTT TM ST]. clear SIM. split.
  { destruct NTT as [[vt Eqvt]|RED].
    - rewrite -(of_to_result _ _ Eqvt).
      destruct (TM _ Eqvt) as (vs' & σs' & r' & idx' & SS' & WSAT' & CONT).
      have STEPK: (fill (Λ:=bor_ectxi_lang fs) Ks es, σs)
                ~{fs}~>* (fill (Λ:=bor_ectxi_lang fs) Ks vs', σs').
      { apply (fill_tstep_rtc fs Ks es). destruct SS' as [|[? Eq]].
        by apply tc_rtc. clear -Eq. by simplify_eq. }
      punfold CONT.
      have NT3:= never_stuck_tstep_rtc _ _ _ _ _ STEPK NT.
      destruct (CONT NT3 _ WSAT') as [NTT' _ _]. done.
    - right. by eapply tstep_reducible_fill. }
  { (* Kt[et] is a value *)
    clear ST. intros vt Eqvt.
    destruct (fill_result _ Kt et) as [Tt ?]; [by eexists|].
    subst Kt. simpl in *.
    destruct (TM _ Eqvt) as (vs' & σs' & r' & idx' & SS' & WSAT' & CONT).
    punfold CONT.
    have STEPK: (fill (Λ:=bor_ectxi_lang fs) Ks es, σs)
                ~{fs}~>* (fill (Λ:=bor_ectxi_lang fs) Ks vs', σs').
    { apply (fill_tstep_rtc fs Ks es). destruct SS' as [|[? Eq]].
      by apply tc_rtc. clear -Eq. by simplify_eq. }
    have NT3:= never_stuck_tstep_rtc _ _ _ _ _ STEPK NT.
    destruct (CONT NT3 _ WSAT') as [NTT' TM' ST'].
    destruct (TM' vt) as (vs2 & σs2 & r2 & idx2 & SS2 & ?);
      [by apply to_of_result|].
    exists vs2, σs2, r2, idx2. split; [|done].
    destruct SS2 as [|[Lt Eq]].
    - left. eapply tc_rtc_l; eauto.
    - clear -SS' Eq Lt. sflib.unguardH SS'. sflib.unguard.
      inversion Eq as [Eq1]. clear Eq. subst.
      destruct SS' as [SS'|[? SS']].
      + left. by apply fill_tstep_tc.
      + simplify_eq. right. split; [|done]. lia.
  }
  (* Kt[et] makes a step *)
  inversion_clear ST as [|Ks1 Kt1].
  { (* step into Kt[et] *)
   destruct (to_result et) as [vt|] eqn:Eqvt.
    - (* et is value *)
      have ? : et = of_result vt. { symmetry. by apply of_to_result. }
      subst et. clear Eqvt.
      destruct (TM _ eq_refl) as (vs' & σs' & r' & idx' & SS' & WSAT' & CONT').
      clear TM.
      have STEPK: (fill (Λ:=bor_ectxi_lang fs) Ks es, σs)
                  ~{fs}~>* (fill (Λ:=bor_ectxi_lang fs) Ks vs', σs').
      { apply (fill_tstep_rtc fs Ks es). destruct SS' as [|[? Eq]].
        by apply tc_rtc. clear -Eq. by simplify_eq. }
      have NT3:= never_stuck_tstep_rtc _ _ _ _ _ STEPK NT.
      punfold CONT'.
      destruct (CONT' NT3 _ WSAT') as [NTT' TM' ST']. clear CONT' WSAT' STEP.
      inversion ST' as [|Ks1 Kt1].
      + constructor 1. intros.
        destruct (STEP _ _ STEPT) as (es2 & σs2 & r2 & idx2 & SS2 & WSAT2 & CONT2).
        exists es2, σs2, r2, idx2. split; last split; [|done|].
        { clear -SS2 SS' STEPK.
          destruct SS2 as [|[]]; [|destruct SS' as [|[]]].
          - left. eapply tc_rtc_l; eauto.
          - simplify_eq. left. by apply fill_tstep_tc.
          - simplify_eq. right. split; [|done]. lia. }
        { pclearbot. left. eapply paco7_mon_bot; eauto. }
      + eapply (sim_local_body_step_over_call _ _ _ _ _ _ _ _ _ _ _ _ _
            Ks1 Kt1 fid el_tgt _ _ _ _ CALLTGT); eauto; [by etrans|].
        intros r4 vs4 vt4 σs4 σt4 VREL4.
        destruct (CONT _ _ _ σs4 σt4 VREL4) as [idx4 CONT4].
        exists idx4. pclearbot. left.  eapply paco7_mon_bot; eauto.
    - (* et makes a step *)
      constructor 1. intros.
      destruct (fill_tstep_inv _ _ _ _ _ _ Eqvt STEPT) as [et2 [? STEP2]].
      subst et'.
      destruct (STEP _ _ STEP2) as (es' & σs' & r' & idx' & SS' & WSAT' & CONT').
      exists (fill Ks es'), σs', r', idx'. split; last split; [|done|].
      + clear -SS'. destruct SS' as [|[]].
        * left. by apply fill_tstep_tc.
        * simplify_eq. right. split; [|done]. lia.
      + pclearbot. right. by apply CIH. }
  { (* Kt[et] has a call, and we step over the call *)
    eapply (sim_local_body_step_over_call _ _ _ _ _ _ _ _ _ _ _ _ _
            (Ks1 ++ Ks) (Kt1 ++ Kt) fid el_tgt); [by rewrite CALLTGT fill_app|..];
            eauto; [rewrite fill_app; by apply fill_tstep_rtc|].
    intros r' vs' vt' σs' σt' VREL'.
    destruct (CONT _ _ _ σs' σt' VREL') as [idx' CONT2]. clear CONT.
    exists idx'. rewrite 2!fill_app.
    pclearbot. right. by apply CIH. }
Qed.

(** MEM STEP -----------------------------------------------------------------*)

(** Copy *)
Lemma sim_body_copy fs ft r n l tg Ts Tt σs σt Φ
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
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL).
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
  { split; last split; last split; last split; last split.
    - by apply (tstep_wf _ _ _ STEPS WFS).
    - by apply (tstep_wf _ _ _ STEPT WFT).
    - done.
    - intros t k h Eqt. destruct (PINV t k h Eqt) as [Lt PI]. subst σt'. simpl.
      split; [done|]. intros l' s' Eqk' stk' Eqstk'.
      destruct (for_each_access1 _ _ _ _ _ _ _ Eqα' _ _ Eqstk')
        as (stk & Eqstk & SUB & ?).
      intros pm opro In' NDIS.
      destruct (SUB _ In') as (it2 & In2 & Eqt2 & Eqp2 & NDIS2).
      destruct (PI _ _ Eqk' _ Eqstk it2.(perm) opro) as [Eql' HTOP].
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
      intros t InT k h Eqt l' Inh.
      destruct (CINV _ InT _ _ Eqt _ Inh) as (stk' & pm' & Eqstk' & Instk').
      destruct (for_each_access1_active_preserving _ _ _ _ _ _ _ Eqα' _ _ Eqstk')
        as [stk [Eqstk AS]].
      exists stk, pm'. split; [done|]. by apply AS.
    - subst σt'. rewrite /srel /=. by destruct SREL as (?&?&?&?&?). }
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

Lemma ptrmap_valid (r_f r: ptrmapUR) t h0 kh
  (Eqtg: r !! t = Some (to_tagKindR tkUnique, h0)) (VN: ✓ kh) :
  ✓ (r_f ⋅ r) → ✓ (r_f ⋅ (<[t:= kh]> r)).
Proof.
  intros VALID.
  apply (local_update_discrete_valid_frame _ _ _ VALID).
  have EQ := (ptrmap_insert_op_r _ _ _ _ kh VALID Eqtg). rewrite EQ.
  eapply (insert_local_update _ _ _
          (to_tagKindR tkUnique, h0) (to_tagKindR tkUnique, h0));
          [|exact Eqtg|by apply exclusive_local_update].
  by rewrite (ptrmap_lookup_op_r _ _ _ _ VALID Eqtg).
Qed.

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
  (Eqtg: r.1 !! tg = Some (to_tagKindR k0, h0))
  (* assuming to-write values are related.
    TODO: this is strong, since we should be able to write unrelated values
      if we privately owns the heaplet we're writing to. *)
  (PUBWRITE: ∀ s, s ∈ v → arel r s s) :
  let r' := if k0 then
            (<[tg := (to_tagKindR tkUnique,  write_heaplet l v h0)]> r.1, r.2)
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
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL).
  split; [|done|].
  { right.
    destruct (NT (Place l (Tagged tg) Ts <- #v)%E σs)
      as [[]|[es' [σs' STEPS]]]; [done..|].
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
  have HL: if k0 then ∀ kh, r_f.1 ⋅ <[tg:=kh]> r.1 = <[tg:=kh]> (r_f.1 ⋅ r.1) else True.
  { destruct k0; [|done]. intros.
    rewrite (ptrmap_insert_op_r r_f.1 r.1 tg h0) //. apply VALID. }
  have HL2: if k0 then  (r_f.1 ⋅ r.1) !! tg = Some (to_tagKindR tkUnique, h0) else True.
  { destruct k0; [|done].
    by apply (ptrmap_lookup_op_r _ _ _ _ (proj1 VALID) Eqtg). }
  exists (#[☠])%V, σs', r', (S n). split; last split.
  { left. by constructor 1. }
  { split; last split; last split; last split; last split.
    - by apply (tstep_wf _ _ _ STEPS WFS).
    - by apply (tstep_wf _ _ _ STEPT WFT).
    - (* valid *)
      rewrite /r'. destruct k0; [|done]. split; simpl; [|apply VALID].
      eapply ptrmap_valid; eauto; [|apply VALID]. split; [done|].
      apply write_heaplet_valid.
      have VL := (proj1 (cmra_valid_op_r _ _ VALID) tg).
      rewrite Eqtg in VL. apply VL.
    - (* ptrmap_inv *)
      intros t k h Eqt.
      have Eqttg: t = tg → k0 = tkUnique → k = k0 ∧ h ≡ write_heaplet l v h0.
      { intros. subst t k0. move  : Eqt. rewrite /= HL lookup_insert.
        intros [Eq1 Eq2]%Some_equiv_inj.
        simpl in Eq1, Eq2. rewrite Eq2. repeat split; [|done].
        destruct k; [done|inversion Eq1]. }
      have CASEt : (t = tg ∧ k0 = tkUnique ∧ k = k0 ∧ h ≡ write_heaplet l v h0 ∨
                    (r_f ⋅ r).1 !! t ≡ Some (to_tagKindR k, h) ∧ (k = tkUnique → t ≠ tg)).
      { move : Eqt. rewrite /r'.
        destruct k0; simpl.
        - rewrite /= HL.
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
      intros l' s' Eqk' stk'. subst σt'. simpl.
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
            apply (lookup_valid_Some (r_f.1 ⋅ r.1) tg (to_tagKindR tkUnique, h0));
              [by apply (proj1 VALID)|by rewrite HL2]. }
          destruct (PINV tg tkUnique h0) as [Lt PI]; [by rewrite HL2|].
          destruct (PI _ _ Eq0 _ Eqstk it2.(perm) opro) as [Eql' HTOP].
          { rewrite /= Eqt2 Eqp2. by destruct it2. } { by rewrite (NDIS2 NDIS). }
          destruct (for_each_lookup_case _ _ _ _ _ Eqα' _ _ _ Eqstk Eqstk')
            as [?|[MR _]]; [by subst|]. clear -In' MR HTOP Eqstk WFT NDIS.
          destruct (access1 stk AccessWrite (Tagged tg) σt.(scs))
            as [[n stk1]|] eqn:Eqstk'; [|done]. simpl in MR. simplify_eq.
          destruct (state_wf_stack_item _ WFT _ _ Eqstk). move : Eqstk' HTOP.
          eapply access1_head_preserving; eauto.
      + (* invoke PINV for t *)
        exfalso. destruct (PINV t k h Eqh) as [Lt PI].
        destruct (PI _ _ Eqk' _ Eqstk it2.(perm) opro) as [Eql' HTOP].
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
      have Eqc: (r_f ⋅ r).2 !! c ≡ Some cs.
      { move  : Eqc'. rewrite /r'. by destruct k0. }
      specialize (CINV _ _ Eqc). subst σt'. simpl.
      clear -Eqα' CINV Eqtg VALID HL HL2. destruct cs as [[T|]| |]; [|done..].
      destruct CINV as [IN CINV]. split; [done|].
      intros t InT k h. specialize (CINV _ InT k).
      (* TODO: duplicated proofs *)
      rewrite /r'. destruct k0.
      + (* if tg was unique *)
        rewrite HL.
        case (decide (t = tg)) => ?.
        { subst tg. rewrite lookup_insert.
          intros [Eqk Eqh]%Some_equiv_inj. simpl in Eqk, Eqh.
          have Eqt : (r_f ⋅ r).1 !! t ≡ Some (k, h0) by rewrite HL2 -Eqk.
          intros l'. rewrite -Eqh write_heaplet_dom. intros Inh.
          destruct (CINV _ Eqt _ Inh) as (stk' & pm' & Eqstk' & Instk').
          destruct (for_each_access1_active_preserving _ _ _ _ _ _ _ Eqα' _ _ Eqstk')
            as [stk [Eqstk AS]].
          exists stk, pm'. split; [done|]. by apply AS. }
        { rewrite lookup_insert_ne //.
          intros Eqt l' Inh.
          destruct (CINV _ Eqt _ Inh) as (stk' & pm' & Eqstk' & Instk').
          destruct (for_each_access1_active_preserving _ _ _ _ _ _ _ Eqα' _ _ Eqstk')
            as [stk [Eqstk AS]].
          exists stk, pm'. split; [done|]. by apply AS. }
      + (* if tg was public *)
        intros Eqt l' Inh.
        destruct (CINV _ Eqt _ Inh) as (stk' & pm' & Eqstk' & Instk').
        destruct (for_each_access1_active_preserving _ _ _ _ _ _ _ Eqα' _ _ Eqstk')
          as [stk [Eqstk AS]].
        exists stk, pm'. split; [done|]. by apply AS.
    - (* srel *)
      subst σt'. rewrite /srel /=. destruct SREL as (?&?&?&?&Eq).
      repeat split; [done..|].
      intros l1 st1 Eq1.
      destruct (write_mem_lookup l v σs.(shp)) as [EqN EqO]. rewrite /r'.
      destruct (write_mem_lookup_case l v σt.(shp) l1)
        as [[i [Lti [Eqi Eqmi]]]|[NEql Eql]].
      + subst l1. specialize (EqN _ Lti). rewrite EqN.
        have InD := (EqD _ Lti). apply elem_of_dom in InD as [st Eqst].
        specialize (Eq _ _ Eqst).
        destruct (lookup_lt_is_Some_2 _ _ Lti) as [s Eqs].
        have ?: st1 = s. { rewrite Eqmi Eqs in Eq1. by inversion Eq1. } subst st1.
        destruct k0.
        * (* tg was unique, and (l +ₗ i) was written to *)
          destruct Eq as [[ss [Eqss AREL]]|[t PV]].
          { left. exists s. split; [done|].
            move : (PUBWRITE _ (elem_of_list_lookup_2 _ _ _ Eqs)).
            rewrite /arel /=. destruct s as [| |l0 t0|]; [done..| |done].
            intros [? [? Eqt0]]. repeat split; [done..|].
            destruct t0 as [t0|]; [|done].
            repeat split. destruct Eqt0 as [ht0 Eqt0].
            destruct (ptrmap_lookup_op_r_equiv_pub r_f.1 r.1 _ _ (proj1 VALID) Eqt0)
              as [h' Eq'].
            exists (h' ⋅ ht0). rewrite HL lookup_insert_ne //.
            intros ?; subst t0. rewrite Eqtg in Eqt0.
            apply Some_equiv_inj in Eqt0 as [Eqt0 _]. inversion Eqt0. }
          { destruct PV as (c & T & h & Eqc & InT & Eqt & Inh).
            right. exists t, c, T.
            case (decide (t = tg)) => ?; [subst t|].
            - exists (write_heaplet l v h0). do 2 (split; [done|]). split.
              by rewrite /= HL lookup_insert. rewrite write_heaplet_dom.
              rewrite HL2 in Eqt. apply Some_equiv_inj in Eqt as [? Eqt].
              simpl in Eqt. by rewrite Eqt.
            - exists h. rewrite /= HL. do 2 (split; [done|]).
              rewrite lookup_insert_ne //. }
        * (* tg was public, and (l +ₗ i) was written to *)
          left. exists s. split; [done|].
          (* we know that the values written must be publicly related *)
          apply (arel_mono r _ VALID).
          { apply cmra_included_r. }
          { apply PUBWRITE, (elem_of_list_lookup_2 _ _ _ Eqs). }
      + specialize (EqO _ NEql). rewrite EqO. rewrite Eql in Eq1.
        specialize (Eq _ _ Eq1). destruct k0; [|done].
        destruct Eq as [[ss [Eqss AREL]]|[t PV]].
        * (* tg was unique, and l1 was NOT written to *)
          left. exists ss. split; [done|]. move : AREL. rewrite /arel.
          destruct ss as [| |l0 t0|], st1 as [| |l3 t3|]; try done.
          intros [? [? Eqt]]. subst l3 t3. repeat split.
          destruct t0 as [t0|]; [|done].
          destruct Eqt as [h Eqt]. exists h.
          rewrite /= HL (lookup_insert_ne _ tg) //.
          intros ?. subst t0. move : Eqt. rewrite lookup_op Eqtg.
          by apply tagKindR_exclusive.
        * (* tg was public, and l1 was NOT written to *)
          right. destruct PV as (c & T & h & Eqc & InT & Eqt & Inl).
          exists t, c, T. simpl.
          case (decide (t = tg)) => ?; [subst t|].
          { eexists (write_heaplet l v h0).
            rewrite HL lookup_insert. repeat split; [done..|].
            rewrite lookup_op Eqtg in Eqt.
            by rewrite write_heaplet_dom (tagKindR_exclusive_heaplet _ _ _ Eqt). }
          { exists h. rewrite HL lookup_insert_ne //. }
  }
  left.
  (* TODO: wp_value like rule *)
  pfold. split; last first.
  { constructor 1. intros vt' ? STEPT'. exfalso.
    have ?: to_result #[☠]%V = None.
    { eapply (tstep_reducible_not_result ft _ σt'); eauto. by do 2 eexists. }
    done. }
  { move => ? /= Eqvt'. symmetry in Eqvt'. simplify_eq.
    exists (ValR [☠%S]), σs', r', n. split; last split.
    - right. split; [lia|]. eauto.
    - eauto.
    - by apply POST. }
  { left. by eexists. }
Qed.

(** InitCall *)
Lemma sim_body_init_call fs ft r n es et σs σt Φ :
  let σs' := mkState σs.(shp) σs.(sst) (σs.(snc) :: σs.(scs)) σs.(snp) (S σs.(snc)) in
  let σt' := mkState σt.(shp) σt.(sst) (σt.(snc) :: σt.(scs)) σt.(snp) (S σt.(snc)) in
  let r'  : resUR := (∅, {[σt.(snc) := to_callStateR (csOwned ∅)]}) in
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
  have FRESH: (r_f ⋅ r).2 !! σt.(snc) = None.
  { destruct ((r_f ⋅ r).2 !! σt.(snc)) as [cs|] eqn:Eqcs; [|done].
    exfalso. destruct WSAT as (WFS & WFT & ? & ? & CINV & ?).
    apply (lt_irrefl σt.(snc)), (cinv_lookup_in_eq _ _ _ _ WFT CINV Eqcs). }
  have LOCAL: (r_f ⋅ r ⋅ ε, ε) ~l~> (r_f ⋅ r ⋅ r', r').
  { apply prod_local_update_2.
    rewrite /= right_id (comm _ (_ ⋅ _)) -insert_singleton_op //.
    by apply alloc_singleton_local_update. }
  exists n. split; last split; cycle 2.
  { (* sim cont *)  by punfold SIM. }
  { (* STEP src *)  left. by apply tc_once. }
  (* WSAT new *)
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL).
  rewrite assoc.
  split; last split; last split; last split; last split.
  { (* WF src *)    by apply (tstep_wf _ _ _ STEPS WFS). }
  { (* WF tgt *)    by apply (tstep_wf _ _ _ STEPT WFT). }
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
    - rewrite lookup_insert_ne // => /CINV. destruct cs as [[]| |]; [|done|lia|done].
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
      apply (lt_irrefl σt.(snc)), (cinv_lookup_in _ _ _ _ WFT CINV PRI). }
Qed.

(** EndCall *)
Lemma sim_body_end_call fs ft r n vs vt σs σt :
  (* return values are related *)
  vrel r vs vt →
  (* and any private location w.r.t to the current call id ownership must be related *)
  (∀ c, hd_error σt.(scs) = Some c → is_Some (r.2 !! c) ∧
    (∀ r_f, ✓ (r_f ⋅ r) →
    ∀ T, (r_f ⋅ r).2 !! c ≡ Some (Cinl (Excl T)) → ∀ (t: ptr_id), t ∈ T →
    ∀ h, (r_f ⋅ r).1 !! t ≡  Some (to_tagKindR tkUnique, h) →
    ∀ l st, l ∈ dom (gset loc) h → σt.(shp) !! l = Some st →
    ∃ ss, σs.(shp) !! l = Some ss ∧ arel (r_f ⋅ r) ss st)) →
  r ⊨{n,fs,ft} (EndCall (Val vs), σs) ≥ (EndCall (Val vt), σt) :
    (λ r _ vs _ vt _, vrel_expr r (of_result vs) (of_result vt)).
Proof.
  intros VREL Hr. pfold. intros NT r_f WSAT.
  split; [|done|].
  { right.
    destruct (NT (EndCall #vs) σs) as [[]|[es' [σs' STEPS]]]; [done..|].
    destruct (tstep_end_call_inv _ #vs _ _ _ (ltac:(by eexists)) STEPS)
      as (vs' & Eqvs & ? & c & cids & Eqc & Eqs).
    subst. simpl in Eqvs. symmetry in Eqvs. simplify_eq.
    destruct WSAT as (?&?&?&?&?&SREL). destruct SREL as (? & ? & Eqcs' & ?).
    exists (#vt)%E, (mkState σt.(shp) σt.(sst) cids σt.(snp) σt.(snc)).
    eapply (head_step_fill_tstep _ []).
    econstructor. by econstructor. econstructor. by rewrite -Eqcs'. }
  constructor 1. intros et' σt' STEPT.
  destruct (tstep_end_call_inv _ #vt _ _ _ (ltac:(by eexists)) STEPT)
    as (vt' & Eqvt & ? & c & cids & Eqc & Eqs).
  subst. simpl in Eqvt. symmetry in Eqvt. simplify_eq.
  rewrite Eqc in Hr. destruct (Hr _ eq_refl) as [[cs Eqcs] Hr']. clear Hr.
  set σs' := (mkState σs.(shp) σs.(sst) cids σs.(snp) σs.(snc)).
  have STEPS: (EndCall #vs, σs) ~{fs}~> ((#vs)%E, σs').
  { destruct WSAT as (?&?&?&?&?&SREL). destruct SREL as (? & ? & Eqcs' & ?).
    eapply (head_step_fill_tstep _ []).
    econstructor. by econstructor. econstructor. by rewrite Eqcs'. }
  exists (Val vs), σs'.
  set r2' := match (r.2 !! c) with
             | Some (Cinl (Excl T)) => <[c := to_callStateR csPub]> r.2
             | _ => r.2
             end.
  exists (r.1, r2'), (S n). split; last split.
  { left. by constructor 1. }
  { destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL).
    destruct r_f as [r_f1 r_f2].
    have VALID': ✓ ((r_f1, r_f2) ⋅ (r.1, r2')).
    { apply (local_update_discrete_valid_frame _ _ _ VALID).
      destruct (r.2 !! c) as [[[T|]| |]|] eqn:Eqr2; rewrite /r2'; [|by destruct r..].
      destruct r as [r1 r2]. rewrite 2!pair_op.
      apply prod_local_update_2.
      rewrite (cmap_insert_op_r r_f2 r2 c T); [|apply VALID|exact Eqr2].
      apply (insert_local_update _ _ _
              (to_callStateR (csOwned T)) (to_callStateR (csOwned T)));
        [|done|by apply exclusive_local_update].
      apply cmap_lookup_op_r; [apply VALID|exact Eqr2]. }
    split; last split; last split; last split; last split.
    - by apply (tstep_wf _ _ _ STEPS WFS).
    - by apply (tstep_wf _ _ _ STEPT WFT).
    - done.
    - rewrite pair_op. apply PINV.
    - rewrite pair_op. intros c1 cs1. simpl.
      case (decide (c1 = c)) => [->|NEqc]; last first.
      + rewrite (_: (r_f2 ⋅ r2') !! c1 = (r_f2 ⋅ r.2) !! c1); last first.
        { rewrite /r2'. destruct (r.2 !! c) as [[[T|]| |]|]; [|done..].
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
        destruct (r.2 !! c) as [[[T'|]| |]|] eqn:Eqc2;
          [rewrite lookup_insert|rewrite Eqc2..|done]; clear;
          (destruct (r_f2 !! c) as [cs|] eqn:Eqrf2; rewrite Eqrf2 ;
            [rewrite -Some_op /=; intros Eq%Some_equiv_inj
            |rewrite left_id /=; intros Eq%Some_equiv_inj;
              by inversion Eq; simplify_eq]);
          destruct cs as [[]| |]; by inversion Eq; simplify_eq.
    - destruct SREL as (Eqst & Eqnp & Eqcs' & Eqnc & Eqhp).
      do 4 (split; [done|]). rewrite /= /r2'.
      destruct (r.2 !! c) as [[[T|]| |]|] eqn:Eqc2; [|apply Eqhp..].
      intros l st Eqs. destruct (Eqhp _ _ Eqs) as [[ss [Eqss VR]]|[t PV]].
      + left. by exists ss.
      + destruct PV as (c' & T' & h & Eqc' & InT' & Eqt & Inh). simpl in *.
        case (decide (c' = c)) => ?; last first.
        { right. exists t, c', T', h. repeat split; [|done..].
          by rewrite /= lookup_op lookup_insert_ne // -lookup_op. }
        subst c'.
        have Eq2 := cmap_lookup_op_r r_f2 r.2 _ _ (proj2 VALID) Eqc2.
        rewrite Eq2 in Eqc'.
        apply Some_equiv_inj, Cinl_inj, Excl_inj, leibniz_equiv_iff in Eqc'.
        subst T'. specialize (Hr' (r_f1, r_f2) VALID T). rewrite /= Eq2 in Hr'.
        destruct (Hr' (ltac:(done)) _ InT' _ Eqt _ _ Inh Eqs) as [ss [Eqss AR]].
        left. by exists ss. }
  left. pfold. split; last first.
  { constructor 1. intros vt' σt' STEPT'. exfalso.
    have ?: to_result (Val vt) = None.
    { eapply (tstep_reducible_not_result ft). by do 2 eexists. }
    done. }
  { move => ? /= Eqvt. symmetry in Eqvt. simplify_eq.
    exists (ValR vs). do 2 eexists. exists n. split; last split.
    { right. split; [lia|]. eauto. }
    { eauto. }
    exists vs, vt. do 2 (split; [done|]). by apply (Forall2_impl _ _ _ _ VREL). }
  { left. by eexists. }
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
  (∀ r' vs vt σs' σt' (VRET: vrel r' vs vt), ∃ n',
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
  intros r' ? ? σs' σt' (vs&vt&?&?&VR). simplify_eq.
  destruct (CONT _ _ _ σs' σt' VR) as [n' ?]. exists n'. by left.
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
  r ⊨{n,fs,ft} (( *{Ts} #[ScPtr l tgs])%E, σs) ≥ (( *{Tt} #[ScPtr l tgt])%E, σt) : Φ.
Proof.
  intros SIM. pfold.
  intros NT r_f WSAT. split; [|done|].
  { right.
    destruct (NT ( *{Ts} #[ScPtr l tgs])%E σs) as [[]|[es' [σs' STEPS]]]; [done..|].
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
