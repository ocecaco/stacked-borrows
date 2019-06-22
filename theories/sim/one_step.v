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
  { exfalso. move : NT => [?]. apply (fill_no_result _ K) in Eq'. by rewrite Eq'. }
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
  { (* et is terminal *)
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
  (* et makes a step *)
  inversion_clear ST as [|Ks1 Kt1].
  { (* step into *)
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
  { (* step over call *)
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
