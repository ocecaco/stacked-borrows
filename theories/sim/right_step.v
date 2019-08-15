From iris.algebra Require Import local_updates.

From stbor.lang Require Import steps_progress steps_inversion steps_retag.
From stbor.sim Require Export instance body.

Set Default Proof Using "Type".

Section right.
Implicit Types Φ: resUR → nat → result → state → result → state → Prop.

Lemma sim_body_let_r fs ft r n x es et1 et2 vt1 σs σt Φ :
  IntoResult et1 vt1 →
  r ⊨{n,fs,ft} (es, σs) ≥ (subst' x et1 et2, σt) : Φ →
  r ⊨{S n,fs,ft} (es, σs) ≥ (let: x := et1 in et2, σt) : Φ.
Proof.
  intros TT%into_result_terminal CONT. pfold.
  intros NT r_f WSAT. split; [|done|].
  { right. do 2 eexists. eapply (head_step_fill_tstep _ []).
    econstructor 1. eapply LetBS; eauto. }
  constructor 1. intros.
  destruct (tstep_let_inv _ _ _ _ _ _ _ TT STEPT). subst et' σt'.
  exists es, σs, r, n. split; last split.
  - right. split; [lia|done].
  - done.
  - by left.
Qed.

Lemma sim_body_deref_r fs ft r n es (rs: result) l t T σs σt Φ :
  IntoResult es rs →
  (Φ r n rs σs (PlaceR l t T) σt) →
  r ⊨{S n,fs,ft} (es, σs) ≥ (Deref #[ScPtr l t] T, σt) : Φ.
Proof.
  intros TS POST. pfold.
  intros NT r_f WSAT. split; [|done|].
  { right. exists (Place l t T), σt.
    eapply (head_step_fill_tstep _ []). econstructor; econstructor. }
  constructor 1. intros.
  destruct (tstep_deref_inv _ (ValR _) _ _ _ _ STEPT) as (l' & t' & ? & ? & ?).
  simplify_eq.
  exists es, σs, r, n. split; last split.
  - right. split; [lia|done].
  - done.
  - left. apply : sim_body_result.
    intros. by eapply POST.
Qed.


Lemma sim_body_copy_local_unique_r
  fs ft (r r': resUR) (h: heaplet) n (l: loc) t k T (ss st: scalar) es σs σt Φ
  (LU: k = tkLocal ∨ k = tkUnique) :
  tsize T = 1%nat →
  tag_on_top σt.(sst) l t →
  r ≡ r' ⋅ res_tag t k h →
  h !! l = Some (ss, st) →
  (r ⊨{n,fs,ft} (es, σs) ≥ (#[st], σt) : Φ : Prop) →
  r ⊨{S n,fs,ft} (es, σs) ≥ (Copy (Place l (Tagged t) T), σt) : Φ.
Proof.
  intros LenT TOP Eqr Eqs CONT. pfold.
  intros NT r_f WSAT. have WSAT1 := WSAT.

  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL).

  (* some lookup properties *)
  have VALIDr := cmra_valid_op_r _ _ VALID. rewrite ->Eqr in VALIDr.
  have HLtr: r.(rtm) !! t ≡ Some (to_tgkR k, to_agree <$> h).
  { rewrite Eqr. destruct LU; subst k.
    - eapply tmap_lookup_op_local_included; [apply VALIDr|apply cmra_included_r|].
      rewrite res_tag_lookup //.
    - eapply tmap_lookup_op_uniq_included; [apply VALIDr|apply cmra_included_r|].
      rewrite res_tag_lookup //. }
  have HLtrf: (r_f ⋅ r).(rtm) !! t ≡ Some (to_tgkR k, to_agree <$> h).
  { destruct LU; subst k.
    - apply tmap_lookup_op_r_local_equiv; [apply VALID|done].
    - apply tmap_lookup_op_r_uniq_equiv; [apply VALID|done]. }

  (* we can make the read in tgt because tag_on_top *)
  destruct TOP as [opro TOP].
  destruct (σt.(sst) !! l) as [stk|] eqn:Eqstk; [|done]. simpl in TOP.

  specialize (PINV _ _ _ HLtrf) as [Lt PINV].
  specialize (PINV l ss st). rewrite lookup_fmap Eqs in PINV.
  specialize (PINV ltac:(done)) as [Eqss [? HD]].
  { simpl. destruct LU; subst k; [done|].
    exists stk, Unique, opro. split; last split; [done| |done].
    destruct stk; [done|]. simpl in TOP. simplify_eq. by left. }

  destruct (tag_unique_head_access σt.(scs) stk (Tagged t) opro AccessRead)
      as [ns Eqstk'].
  { destruct stk; [done|]. simpl in TOP. simplify_eq. by eexists. }

  have Eqα : memory_read σt.(sst) σt.(scs) l (Tagged t) (tsize T) = Some σt.(sst).
  { rewrite LenT /memory_read /= shift_loc_0_nat Eqstk /= Eqstk' /= insert_id //. }
  have READ: read_mem l (tsize T) σt.(shp) = Some [st].
  { rewrite LenT read_mem_equation_1 /= Eqss //. }

  have STEPT: (Copy (Place l (Tagged t) T), σt) ~{ft}~> ((#[st])%E, σt).
  { destruct σt.
    eapply (head_step_fill_tstep _ []); eapply copy_head_step'; eauto. }

  split; [right; by do 2 eexists|done|].
  constructor 1. intros et' σt' STEPT'.
  destruct (tstep_copy_inv _ (PlaceR _ _ _) _ _ _ STEPT')
      as (l1&t1&T1& vs1 & α1 & EqH & ? & Eqvs & Eqα' & ?).
  symmetry in EqH. simplify_eq.
  have Eqσt: mkState σt.(shp) σt.(sst) σt.(scs) σt.(snp) σt.(snc) = σt
    by destruct σt. rewrite Eqσt. rewrite Eqσt in STEPT'. clear Eqσt.
  exists es, σs, r, n. split; last split; [|done|].
  - right. split; [lia|done].
  - by left.
Qed.

Lemma sim_body_copy_unique_r
  fs ft (r r': resUR) (h: heaplet) n (l: loc) t T (ss st: scalar) es σs σt Φ :
  tsize T = 1%nat →
  tag_on_top σt.(sst) l t →
  r ≡ r' ⋅ res_tag t tkUnique h →
  h !! l = Some (ss, st) →
  (r ⊨{n,fs,ft} (es, σs) ≥ (#[st], σt) : Φ : Prop) →
  r ⊨{S n,fs,ft} (es, σs) ≥ (Copy (Place l (Tagged t) T), σt) : Φ.
Proof. apply sim_body_copy_local_unique_r. by right. Qed.

Lemma vsP_res_mapsto_tag_on_top (r: resUR) l t s σs σt :
  (r ⋅ res_loc l [s] t) ={σs,σt}=> (λ _ _ σt, tag_on_top σt.(sst) l t : Prop).
Proof.
  intros r_f. rewrite cmra_assoc.
  intros (WFS & WFT & VALID & PINV & CINV & SREL).
  have Hrf: (r_f ⋅ r ⋅ res_loc l [s] t).(rtm) !! t ≡
    Some (to_tgkR tkLocal, to_hplR (write_hpl l [s] ∅)).
  { move : (proj1 VALID t).
    rewrite lookup_op res_tag_lookup.
    intros Eq%exclusive_Some_r. by rewrite Eq left_id. apply _. }
  specialize (PINV _ _ _ Hrf) as [? PINV]. destruct s as [ss st].
  specialize (PINV l ss st) as (Eq1 & Eq2 & PO); [|done|].
  { by rewrite lookup_fmap /= lookup_insert. }
  simpl in PO.
  rewrite /tag_on_top PO /=. by eexists.
Qed.

Lemma sim_body_copy_local_r fs ft r r' n l t ty ss st es σs σt Φ :
  tsize ty = 1%nat →
  r ≡ r' ⋅ res_loc l [(ss, st)] t →
  (r ⊨{n,fs,ft} (es, σs) ≥ (#[st], σt) : Φ) →
  r ⊨{S n,fs,ft}
    (es, σs) ≥ (Copy (Place l (Tagged t) ty), σt)
  : Φ.
Proof.
  intros Hty Hr. rewrite Hr. intros CONT.
  eapply viewshiftP_sim_local_body; [apply vsP_res_mapsto_tag_on_top|].
  simpl. intros TOP. move : CONT.
  eapply (sim_body_copy_local_unique_r _ _ _ r'); [by left|..] ; eauto.
  - by instantiate (1:= (write_hpl l [(ss, st)] ∅)).
  - by rewrite lookup_insert.
Qed.

End right.
