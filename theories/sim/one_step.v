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

Lemma never_stuck_fill_inv fs
  (K: list (ectxi_language.ectx_item (bor_ectxi_lang fs))) e σ :
  never_stuck fs (fill K e) σ → never_stuck fs e σ.
Proof.
  intros NT e' σ' STEP. specialize (NT _ _ (fill_tstep fs K _ _ _ _ STEP)).
  destruct (to_result e') as [v'|] eqn:Eq'; [left; by eexists|right].
  destruct NT as [NT|RED].
  { exfalso. move : NT => [?]. apply (fill_not_result _ K) in Eq'. by rewrite Eq'. }
  move : RED. by apply reducible_fill.
Qed.

Lemma never_stuck_step fs e σ e' σ':
  (e, σ) ~{fs}~>* (e', σ') → never_stuck fs e σ → never_stuck fs e' σ'.
Proof.
  intros ST. remember (e, σ) as x. remember (e', σ') as y.
  revert x y ST e σ e' σ' Heqx Heqy.
  induction 1 as [|? [e1 σ1] ? S1 ? IH];
    intros e σ e' σ' H1 H2; subst; simplify_eq; [done|].
  intros NT. eapply IH; eauto. clear IH ST e' σ'.
  intros e' σ' STEP. apply NT. etrans; [by apply rtc_once|exact STEP].
Qed.

Lemma sim_body_bind fs ft r n
  (Ks: list (ectxi_language.ectx_item (bor_ectxi_lang fs)))
  (Kt: list (ectxi_language.ectx_item (bor_ectxi_lang ft))) es et σs σt Φ :
  r ⊨{n,fs,ft} (es, σs) ≤ (et, σt)
    : (λ r' n' es' σs' et' σt',
        r' ⊨{n',fs,ft} (fill Ks es', σs') ≤ (fill Kt et', σt') : Φ) →
  r ⊨{n,fs,ft} (fill Ks es, σs) ≤ (fill Kt et, σt) : Φ.
Proof.
  revert r n Ks Kt es et σs σt Φ. pcofix CIH.
  intros r1 n Ks Kt es et σs σt Φ SIM. pfold. punfold SIM. intros NT ??.
  have NT2 := never_stuck_fill_inv _ _ _ _ NT.
  destruct (SIM NT2 _ WSAT) as [TM ST]. clear SIM. split.
  { (* Kt[et] is a value *)
    clear ST. intros vt Eqvt.
    destruct (fill_result _ Kt et) as [Tt ?]; [by eexists|].
    subst Kt. simpl in *.
    destruct (TM _ Eqvt) as (vs' & σs' & r' & idx' & SS' & WSAT' & CONT).
    punfold CONT.
    have STEPK: (fill (Λ:=bor_ectxi_lang fs) Ks es, σs)
                ~{fs}~>* (fill (Λ:=bor_ectxi_lang fs) Ks vs', σs').
    { apply (fill_tstep fs Ks es). destruct SS' as [|[? Eq]]. by apply tc_rtc.
      clear -Eq. simplify_eq. constructor 1. }
    have NT3:= never_stuck_step _ _ _ _ _ STEPK NT.
    destruct (CONT NT3 _ WSAT') as [TM' ST'].
    destruct (TM' vt) as (vs2 & σs2 & r2 & idx2 & SS2 & ?);
      [by apply to_of_result|].
    exists vs2, σs2, r2, idx2. split; [|done].
    destruct SS2 as [|[Lt Eq]].
    - left. eapply tc_rtc_l; eauto.
    - clear -SS' Eq Lt. inversion Eq as [Eq1]. clear Eq. subst. rewrite Eq1.
      clear vs2 Eq1. destruct SS' as [SS'|[? SS']].
      + left. by apply fill_tstep_tc.
      + simplify_eq. right. split; [|done]. lia. }
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
      { apply (fill_tstep fs Ks es). destruct SS' as [|[? Eq]]. by apply tc_rtc.
        clear -Eq. simplify_eq. constructor 1. }
      have NT3:= never_stuck_step _ _ _ _ _ STEPK NT.
      punfold CONT'.
      destruct (CONT' NT3 _ WSAT') as [TM' ST']. clear CONT' WSAT' STEP.
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
      + apply (sim_local_body_step_over_call _ _ _ _ _ _ _ _ _ _ _ _ _
            Ks1 Kt1 fid el_tgt); [done|].
        intros FAT. destruct (STEPOVER FAT) as
          (els & σs3 & rc3 & rv3 & SS3 & FAS3 & WSAT3 & VREL3 & CONT3).
        exists els, σs3, rc3, rv3. split.
        { clear -SS3 STEPK. etrans; eauto. }
        do 3 (split; [done|]).
        intros r_f4 vs4 vt4 σs4 σt4 VREL4.
        destruct (CONT3 _ _ _ σs4 σt4 VREL4) as [idx4 CONT4].
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
    apply (sim_local_body_step_over_call _ _ _ _ _ _ _ _ _ _ _ _ _
            (Ks1 ++ Ks) (Kt1 ++ Kt) fid el_tgt); [by rewrite CALLTGT fill_app|].
    intros FAT.
    destruct (STEPOVER FAT) as (els & σ1s & rc &rv & SS & FAS & WSAT1 & FAV & CONT).
    clear STEPOVER.
    exists els, σ1s, rc, rv. split.
    { rewrite fill_app. by apply fill_tstep. }
    do 3 (split; [done|]).
    intros. destruct (CONT _ _ _ σs' σt' VRET) as [idx' CONT2]. clear CONT.
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
  r ⊨{n,fs,ft} (Copy (Place l tg Ts), σs) ≤ (Copy (Place l tg Tt), σt) : Φ.
Proof.
  intros POST. pfold.
  intros NT. intros. split; [done|]. constructor 1. intros.
  destruct (tstep_copy_inv _ _ _ _ _ _ _ STEPT) as (vt & α' & ? & Eqvt & Eqα' & ?).
  subst et'.
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL).
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
      intros pm opro In'. destruct (SUB _ In') as (it2 & In2 & Eqt2 & Eqp2).
      destruct (PI _ _ Eqk' _ Eqstk it2.(perm) opro) as [Eql' HTOP].
      { simpl in *. rewrite /= Eqt2 Eqp2. by destruct it2. }
      split; [done|].
      destruct (for_each_lookup_case _ _ _ _ _ Eqα' _ _ _ Eqstk Eqstk')
        as [?|MR]; [by subst|]. revert MR HTOP.
      admit.
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
    { apply (tstep_reducible_not_result ft). naive_solver. } done. }
  move => ? /= Eqvt'. symmetry in Eqvt'. simplify_eq.
  exists (ValR vs), σs', r, n. split; last split.
  { right. split; [lia|]. eauto. }
  { eauto. }
  { by apply POST. }
Abort.

(** InitCall *)
Lemma sim_body_init_call fs ft r n es et σs σt Φ :
  let σs' := mkState σs.(shp) σs.(sst) (σs.(snc) :: σs.(scs)) σs.(snp) (S σs.(snc)) in
  let σt' := mkState σt.(shp) σt.(sst) (σt.(snc) :: σt.(scs)) σt.(snp) (S σt.(snc)) in
  let r'  : resUR := (∅, {[σt.(snc) := to_callStateR (csOwned ∅)]}) in
  r ⋅ r' ⊨{n,fs,ft} (EndCall es, σs') ≤ (EndCall et, σt') : Φ →
  r ⊨{n,fs,ft} (InitCall es, σs) ≤ (InitCall et, σt) : Φ.
Proof.
  intros σs' σt1 r' SIM. pfold.
  intros NT. intros. split; [done|]. constructor 1. intros.
  exists (EndCall es), σs', (r ⋅ r').
  destruct (tstep_init_call_inv _ _ _ _ _ STEPT). subst et' σt'.
  have STEPS: (InitCall es, σs) ~{fs}~> (EndCall es, σs').
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
  r ⊨{n,fs,ft} (EndCall (Val vs), σs) ≤ (EndCall (Val vt), σt) :
    (λ r _ vs _ vt _, vrel_expr r (of_result vs) (of_result vt)).
Proof.
  intros VREL Hr. pfold. intros NT r_f WSAT. split; [done|].
  constructor 1. intros et' σt' STEPT.
  destruct (tstep_end_call_inv ft (Val vt) et' σt σt')
    as (vt' & Eqvt & ? & c & cids & Eqc & Eqs); [by eexists|done|].
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
    { apply (tstep_reducible_not_result ft). naive_solver. } done. }
  move => ? /= Eqvt. symmetry in Eqvt. simplify_eq.
  exists (ValR vs). do 2 eexists. exists n. split; last split.
  { right. split; [lia|]. eauto. }
  { eauto. }
  exists vs, vt. do 2 (split; [done|]). by apply (Forall2_impl _ _ _ _ VREL).
Qed.

(** PURE STEP ----------------------------------------------------------------*)

(** Call - step over *)
Lemma sim_body_step_over_call fs ft
  (Ks: list (ectxi_language.ectx_item (bor_ectxi_lang fs)))
  (Kt: list (ectxi_language.ectx_item (bor_ectxi_lang ft)))
  rc rv n fid els elt σs σt Φ
  (VS  : Forall (λ ei, is_Some (to_value ei)) els)
  (VREL: Forall2 (vrel_expr rv) els elt) :
  (∀ r' vs vt σs' σt' (VRET: vrel r' vs vt), ∃ n',
    rc ⋅ r' ⊨{n',fs,ft} (fill Ks (Val vs), σs') ≤ (fill Kt (Val vt), σt') : Φ) →
  rc ⋅ rv ⊨{n,fs,ft}
    (fill Ks (Call #[ScFnPtr fid] els), σs) ≤ (fill Kt (Call #[ScFnPtr fid] elt), σt) : Φ.
Proof.
  intros CONT. pfold. intros NT r_f WSAT. split.
  { intros vt. by rewrite fill_not_result. }
  econstructor 2; [eauto|].
  intros VT. exists els, σs, rc, rv. split; [by apply rtc_refl|].
  do 3 (split; [done|]).
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
  r ⊨{n,fs,ft} (InitCall es', σs) ≤ (InitCall et', σt) : Φ →
  r ⊨{n,fs,ft} (Call #[ScFnPtr fid] els, σs) ≤ (Call #[ScFnPtr fid] elt, σt) : Φ.
Proof.
  intros CONT. pfold. intros NT r_f WSAT. split; [done|].
  econstructor 1. intros et1 σt' STEPT.
  destruct (tstep_call_inv _ _ _ _ _ _ VT STEPT) as (?&?&?&?&?&?&?&?). subst; simplify_eq.
  exists (InitCall es'), σs, r, n. split; last split; [|done|by left].
  left. constructor 1.
  eapply (head_step_fill_tstep _ []). econstructor.
  by apply (CallBS _ _ _ els xls es HCs).
Qed.

(** Let *)
Lemma sim_body_let fs ft r n x es1 es2 et1 et2 σs σt Φ :
  terminal es1 → terminal et1 →
  r ⊨{n,fs,ft} (subst x es1 es2, σs) ≤ (subst x et1 et2, σt) : Φ →
  r ⊨{n,fs,ft} (let: x := es1 in es2, σs) ≤ ((let: x := et1 in et2), σt) : Φ.
Proof.
  intros TS TT SIM. pfold.
  intros NT r_f WSAT. split; [done|]. constructor 1. intros.
  destruct (tstep_let_inv _ _ _ _ _ _ _ TT STEPT). subst et' σt'.
  exists (subst x es1 es2), σs, r, n. split.
  { left. constructor 1. eapply (head_step_fill_tstep _ []).
    by econstructor; econstructor. }
  split; [done|]. by left.
Qed.

(** Ref *)
Lemma sim_body_ref fs ft r n l tgs tgt Ts Tt σs σt Φ :
  r ⊨{n,fs,ft} (#[ScPtr l tgs], σs) ≤ (#[ScPtr l tgt], σt) : Φ →
  r ⊨{n,fs,ft} ((& (Place l tgs Ts))%E, σs) ≤ ((& (Place l tgt Tt))%E, σt) : Φ.
Proof.
  intros SIM. pfold.
  intros NT r_f WSAT. split; [done|]. constructor 1. intros.
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
  r ⊨{n,fs,ft} (Place l tgs Ts, σs) ≤ (Place l tgt Tt, σt) : Φ →
  r ⊨{n,fs,ft} (( *{Ts} #[ScPtr l tgs])%E, σs) ≤ (( *{Tt} #[ScPtr l tgt])%E, σt) : Φ.
Proof.
  intros SIM. pfold.
  intros NT r_f WSAT. split; [done|]. constructor 1. intros.
  destruct (tstep_deref_inv _ _ _ _ _ _ _ STEPT) as [? [? IS]]. subst et' σt'.
  have ?: (∀ (i: nat), (i < tsize Ts)%nat → l +ₗ i ∈ dom (gset loc) σs.(shp)).
  { clear -WSAT IS EQS. rewrite EQS. move => i /IS. by rewrite wsat_heap_dom. }
  exists (Place l tgs Ts), σs, r, n. split.
  { left. constructor 1. eapply (head_step_fill_tstep _ []).
    by econstructor; econstructor. }
  split; [done|]. by left.
Qed.
