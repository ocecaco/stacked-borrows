From stbor.lang Require Export defs steps_wf.
From stbor.sim Require Export cmra.

Set Default Proof Using "Type".

Instance dom_proper `{Countable K} {A : cmraT} :
  Proper ((≡) ==> (≡)) (dom (M:=gmap K A) (gset K)).
Proof.
  intros m1 m2 Eq. apply elem_of_equiv. intros i.
  by rewrite !elem_of_dom Eq.
Qed.

(** Public scalar relation *)
Definition arel (r: resUR) (s1 s2: scalar) : Prop :=
  match s1, s2 with
  | ScPoison, ScPoison => True
  | ScInt n1, ScInt n2 => n1 = n2
  | ScFnPtr n1, ScFnPtr n2 => n1 = n2
  | ScPtr l1 tg1, ScPtr l2 tg2 =>
      l1 = l2 ∧ tg1 = tg2 ∧
      match tg1 with
      | Untagged => True
      | Tagged t => ∃ h, r.(rtm) !! t ≡ Some (to_tgkR tkPub, h)
      end
  | _, _ => False
  end.

Definition tmap_inv (r: resUR) (σs σt: state) : Prop :=
  ∀ (t: ptr_id) (k: tag_kind) h, r.(rtm) !! t ≡ Some (to_tgkR k, h) →
    (t < σt.(snp))%nat ∧
    ∀ (l: loc) (ss st: scalar),
      h !! l ≡ Some (to_agree (ss, st)) →
      ∀ (stk: stack), σt.(sst) !! l = Some stk →
        ∀ pm opro, mkItem pm (Tagged t) opro ∈ stk → pm ≠ Disabled →
          (* as long as the tag [t] is in the stack [stk] (Disabled is
            considered not in), then its heaplet [h] agree with the state [σ] *)
          σt.(shp) !! l = Some st ∧
          σs.(shp) !! l = Some ss ∧
          (* If [k] is Unique, then [t] must be Unique at the top of [stk].
            Otherwise if [k] is Pub, then [t] can be among the top SRO items. *)
          match k with
          | tkUnique => ∃ stk', stk = mkItem Unique (Tagged t) opro :: stk'
          | tkPub => t ∈ active_SRO stk
          end.

Definition cmap_inv (r: resUR) (σ: state) : Prop :=
  ∀ (c: call_id) (cs: callStateR), r.(rcm) !! c ≡ Some cs →
  match cs with
  (* if c is a private call id *)
  | Excl T =>
      c ∈ σ.(scs) ∧
      (* for any tag [t] owned by [c] *)
      ∀ (t: ptr_id) tls, T !! t = Some tls →
        (t < σ.(snp))%nat ∧
        (* and any [l] protected by [t] *)
        ∀ l, l ∈ tls →
        (* then a [c]-protector must be in the stack of [l] *)
          ∃ stk pm, σ.(sst) !! l = Some stk ∧
          mkItem pm (Tagged t) (Some c) ∈ stk ∧ pm ≠ Disabled
  | _ => False
  end.

Definition lmap_inv (r: resUR) (σs σt: state) : Prop :=
  ∀ t (tls: gset loc), r.(rlm) !! t ≡ Some (Excl tls) →
    (t < σt.(snp))%nat ∧
    (∀ l, l ∈ tls → σt.(sst) !! l = Some (init_stack (Tagged t))).

(* [l] is private w.r.t to some tag [t] if [t] is uniquely owned and protected
  by some call id [c] and [l] is in [t]'s heaplet [h]. *)
Definition priv_loc (r: resUR) (l: loc) (t: ptr_id) :=
  ∃ h, r.(rtm) !! t ≡ Some (to_tgkR tkUnique, h) ∧
    l ∈ dom (gset loc) h ∧
    ((* local *)
      (∃ tls : gset loc, r.(rlm) !! t ≡ Some (Excl tls) ∧ l ∈ tls) ∨
     (* protector *)
      (∃ (c: call_id) (T: gmap ptr_id (gset loc)) tls,
        r.(rcm) !! c ≡ Some (Excl T) ∧ T !! t = Some tls ∧ l ∈ tls)).

Definition pub_loc (r: resUR) (l: loc) (σs σt: state) :=
  ∀ st, σt.(shp) !! l = Some st → ∃ ss, σs.(shp) !! l = Some ss ∧ arel r ss st.

(** State relation *)
Definition srel (r: resUR) (σs σt: state) : Prop :=
  σs.(sst) = σt.(sst) ∧ σs.(snp) = σt.(snp) ∧
  σs.(scs) = σt.(scs) ∧ σs.(snc) = σt.(snc) ∧
  ∀ (l: loc), l ∈ dom (gset loc) σt.(shp) →
    pub_loc r l σs σt ∨ (∃ (t: ptr_id), priv_loc r l t).

Definition wsat (r: resUR) (σs σt: state) : Prop :=
  (* Wellformedness *)
  Wf σs ∧ Wf σt ∧ ✓ r ∧
  (* Invariants *)
  tmap_inv r σs σt ∧ cmap_inv r σt ∧ srel r σs σt ∧ lmap_inv r σs σt.

(** Value relation for function arguments/return values *)
(* Values passed among functions are public *)
Definition vrel (r: resUR) (v1 v2: value) := Forall2 (arel r) v1 v2.

(** Condition for resource before EndCall *)
(* The call id [c] to be end must not have any privately protected locations. *)
Definition end_call_sat (r: resUR) (c: call_id) : Prop :=
  r.(rcm) !! c ≡ Some (Excl ∅).

Lemma res_end_call_sat r c :
  ✓ r → res_cs c ∅ ≼ r → end_call_sat r c.
Proof.
  intros Hval [r' EQ]. rewrite /end_call_sat EQ.
  destruct r' as [[tmap' cmap'] lmap'].
  rewrite /res_cs !pair_op /= /rcm /= /to_cmUR fmap_insert fmap_empty insert_empty.
  apply cmap_lookup_op_l_equiv; last by rewrite lookup_insert.
  destruct r as [[tmap cmap] lmap].
  destruct EQ as [[EQt EQc] EQl]. simplify_eq/=.
  move : Hval. rewrite /to_cmUR fmap_insert fmap_empty insert_empty.
  intros Hval. apply Hval.
Qed.

Definition init_res : resUR := res_cs O ∅.

Lemma wsat_init_state : wsat init_res init_state init_state.
Proof.
  split; last split; last split; last split; last split; last split.
  - apply wf_init_state.
  - apply wf_init_state.
  - split; [|done]. split; [done|]. intros ?; simpl.
    rewrite /to_cmUR lookup_fmap. destruct i.
    + rewrite lookup_singleton //.
    + rewrite lookup_singleton_ne //.
  - intros ??? HL. exfalso. move : HL. rewrite /= lookup_empty. by inversion 1.
  - intros ??. simpl. rewrite /rcm /init_res /= /to_cmUR lookup_fmap.
    destruct c.
    + rewrite lookup_singleton. intros Eq%Some_equiv_inj.
      destruct cs; inversion Eq. simplify_eq.
      split; [by rewrite elem_of_list_singleton|]. intros ??. set_solver.
    + rewrite lookup_singleton_ne //. by inversion 1.
  - do 4 (split; [done|]). intros l. rewrite /= dom_empty. set_solver.
  - intros ?? HL. exfalso. move : HL. rewrite /= lookup_empty. by inversion 1.
Qed.

Lemma arel_ptr l tg :
  arel (res_tag tg tkPub ∅) (ScPtr l (Tagged tg)) (ScPtr l (Tagged tg)).
Proof.
  simpl. do 2 (split; first done).
  exists ∅. rewrite /res_tag /rtm /=.
  rewrite lookup_insert fmap_empty. done.
Qed.

Lemma arel_eq (r: resUR) (s1 s2: scalar) :
  arel r s1 s2 → s1 = s2.
Proof. destruct s1 as [| |? []|], s2 as [| |? []|]; simpl; try done; naive_solver. Qed.

Lemma vrel_eq (r: resUR) (v1 v2: value) :
  vrel r v1 v2 → v1 = v2.
Proof.
  revert v2. induction v1 as [|s1 v1 IH]; intros v2 FA.
  { apply Forall2_nil_inv_l in FA. by subst. }
  destruct v2 as [|s2 v2]. { by apply Forall2_nil_inv_r in FA. }
  apply Forall2_cons_inv in FA as [Eq1 Eq2].
  f_equal. by apply (arel_eq _ _ _ Eq1). by apply IH.
Qed.

Lemma arel_mono (r1 r2 : resUR) (VAL: ✓ r2) :
  r1 ≼ r2 → ∀ s1 s2, arel r1 s1 s2 → arel r2 s1 s2.
Proof.
  intros Le s1 s2. rewrite /arel.
  destruct s1 as [| |l1 t1|], s2 as [| |l2 t2|]; auto.
  intros [Eql [Eqt PV]]. subst. repeat split.
  destruct t2 as [t2|]; [|done].
  destruct PV as [h HL].
  have HL1: Some (to_tgkR tkPub, h) ≼ r2.(rtm) !! t2.
  { rewrite -HL. apply lookup_included, prod_included.
    by apply prod_included in Le as []. }
  apply option_included in HL1 as [?|[th1 [[tk2 h2] [? [Eq1 INCL]]]]]; [done|].
  simplify_eq. exists h2. rewrite Eq1 (_: tk2 ≡ to_tgkR tkPub) //.
  apply tag_kind_incl_eq; [done|].
  move : INCL => [[/=<- _//]|/prod_included [/= /csum_included Eq _]].
  - apply csum_included. naive_solver.
  - have VL2: ✓ tk2.
    { apply (pair_valid tk2 h2). rewrite -pair_valid.
      apply (lookup_valid_Some r2.(rtm) t2); [apply VAL|]. by rewrite Eq1. }
    destruct Eq as [|[|Eq]]; [by subst|naive_solver|].
    destruct Eq as [?[[][? [? ?]]]]. simplify_eq.
    apply csum_included. naive_solver.
Qed.

Lemma vrel_mono (r1 r2 : resUR) (VAL: ✓ r2) :
  r1 ≼ r2 → ∀ v1 v2, vrel r1 v1 v2 → vrel r2 v1 v2.
Proof. intros Le v1 v2 VREL. by apply (Forall2_impl _ _ _ _ VREL), arel_mono. Qed.

Lemma priv_loc_mono (r1 r2 : resUR) (VAL: ✓ r2) :
  r1 ≼ r2 → ∀ l t, priv_loc r1 l t → priv_loc r2 l t.
Proof.
  intros LE l t (h & Eqh & InD & PRIV).
  do 2 (apply prod_included in LE as [LE ]).
  do 2 (apply pair_valid in VAL as [VAL ]).
  exists h. split; last split; [|done|].
  { by apply (tmap_lookup_op_uniq_included r1.(rtm)). }
  destruct PRIV as [(tls & ? & ?)|(c & T & tls & ? & ?)]; [left|right].
  - exists tls. split; [|done]. by eapply lmap_lookup_op_included.
  - exists c, T, tls. split; [|done]. by apply (cmap_lookup_op_unique_included r1.(rcm)).
Qed.

Instance tmap_inv_proper : Proper ((≡) ==> (=) ==> (=) ==> iff) tmap_inv.
Proof.
  intros r1 r2 [[Eqt Eqc] Eqm] ? σ ? ???. subst. rewrite /tmap_inv.
  by setoid_rewrite Eqt.
Qed.

Instance cmap_inv_proper : Proper ((≡) ==> (=) ==> iff) cmap_inv.
Proof.
  intros r1 r2 [[Eqt Eqc] Eqm]  ? σ ?. subst. rewrite /cmap_inv.
  setoid_rewrite Eqc.
  split; intros EQ ?? Eq; specialize (EQ _ _ Eq); destruct cs; eauto.
Qed.

Instance arel_proper : Proper ((≡) ==> (=) ==> (=) ==> iff) arel.
Proof. rewrite /arel. solve_proper. Qed.

Instance priv_loc_proper : Proper ((≡) ==> (=) ==> (=) ==> iff) priv_loc.
Proof. rewrite /priv_loc. solve_proper. Qed.

Instance pub_loc_proper : Proper ((≡) ==> (=) ==> (=) ==> (=) ==> iff) pub_loc.
Proof. rewrite /pub_loc. intros ???Eq?????????. subst. by setoid_rewrite Eq. Qed.

Instance srel_proper : Proper ((≡) ==> (=) ==> (=) ==> iff) srel.
Proof.
  intros r1 r2 Eqr ??????. subst. rewrite /srel.
  split; move => [-> [-> [-> [->]]]]; by setoid_rewrite Eqr.
Qed.

Instance lmap_inv_proper  : Proper ((≡) ==> (=) ==> (=) ==> iff) lmap_inv.
Proof. intros r1 r2 Eqr ??????. subst. rewrite /lmap_inv. by setoid_rewrite Eqr. Qed.

Instance wsat_proper : Proper ((≡) ==> (=) ==> (=) ==> iff) wsat.
Proof. solve_proper. Qed.

Lemma cinv_lookup_in (r: resUR) (σ: state) c cs:
  Wf σ → cmap_inv r σ → r.(rcm) !! c ≡ Some cs → (c < σ.(snc))%nat.
Proof.
  intros WF CINV EQ. specialize (CINV c cs EQ).
  destruct cs; [|done..]. destruct CINV. by apply WF.
Qed.

Lemma cinv_lookup_in_eq (r: resUR) (σ: state) c cs:
  Wf σ → cmap_inv r σ → r.(rcm) !! c = Some cs → (c < σ.(snc))%nat.
Proof.
  intros WF CINV EQ. eapply cinv_lookup_in; eauto. by rewrite EQ.
Qed.

Lemma srel_heap_dom r σs σt :
  Wf σs → Wf σt → srel r σs σt → dom (gset loc) σt.(shp) ≡ dom (gset loc) σs.(shp).
Proof.
  intros WFS WFT (EQS&?).
  rewrite (state_wf_dom _ WFS) (state_wf_dom _ WFT) EQS //.
Qed.

Lemma wsat_heap_dom r σs σt :
  wsat r σs σt → dom (gset loc) σt.(shp) ≡ dom (gset loc) σs.(shp).
Proof. intros (?&?&?&?&?&?&?). by eapply srel_heap_dom. Qed.

Lemma arel_persistent r a1 a2 :
  arel r a1 a2 → arel (core r) a1 a2.
Proof.
  destruct a1, a2; try done. simpl.
  destruct tg; last done.
  intros (<- & <- & [h Hlk]).
  split; first done. split; first done.
  exists (core h). move: Hlk.
  destruct r as [[tmap cmap] lmap].
  change (core (tmap, cmap, lmap)) with (core tmap, core cmap, core lmap).
  rewrite /rtm /=. rewrite lookup_core=>->.
  rewrite /core /core' /=.
  rewrite {1}/pcore /cmra_pcore /=. rewrite /prod_pcore //.
Qed.

Lemma vrel_persistent r v1 v2 :
  vrel r v1 v2 → vrel (core r) v1 v2.
Proof.
  rewrite /vrel=>Hrel. eapply Forall2_impl; first done.
  eauto using arel_persistent.
Qed.

Lemma vrel_list_persistent r vl1 vl2 :
  Forall2 (vrel r) vl1 vl2 → Forall2 (vrel (core r)) vl1 vl2.
Proof.
  intros Hrel. eapply Forall2_impl; first done.
  eauto using vrel_persistent.
Qed.

Lemma vrel_length r vs vt :
  vrel r vs vt → length vs = length vt.
Proof. intros. eapply Forall2_length; eauto. Qed.

Lemma vrel_tag_included r vs vt t:
  vrel r vs vt → vs <<t t ↔ vt <<t t.
Proof.
  intros VREL.
  split; intros IN l1 t1 [i Eqi]%elem_of_list_lookup;
    [destruct (Forall2_lookup_r _ _ _ _ _ VREL Eqi) as (ss & Eqss & AREL)
    |destruct (Forall2_lookup_l _ _ _ _ _ VREL Eqi) as (ss & Eqss & AREL)];
    apply elem_of_list_lookup_2 in Eqss;
    destruct ss as [| |ls ts|]; try done;
    specialize (IN _ _ Eqss);
    destruct t1, ts; try done; naive_solver.
Qed.

Lemma arel_res_tag_overwrite r t h1 h2 ss st :
  arel (r ⋅ res_tag t tkUnique h1) ss st →
  arel (r ⋅ res_tag t tkUnique h2) ss st.
Proof.
  destruct ss as [| |? [t1|]|], st as [| |? []|]; simpl; auto; [|naive_solver].
  intros (?&?& h & Eqh). do 2 (split; [done|]).
  case (decide (t1 = t)) => ?; [subst t1|].
  - exfalso. move : Eqh. rewrite lookup_op res_tag_lookup.
    apply tagKindR_exclusive.
  - exists h. move : Eqh.
    by do 2 (rewrite lookup_op res_tag_lookup_ne; [|done]).
Qed.
