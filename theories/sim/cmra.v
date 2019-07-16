From iris.algebra Require Export local_updates.
From iris.algebra Require Export cmra gmap gset csum agree excl big_op.

From stbor.lang Require Export lang.

Set Default Proof Using "Type".

(** Tag map that connect tags to the heaplet that they govern *)
Inductive tag_kind := tkUnique | tkPub.
(* Ex() + Ag() *)
Definition tagKindR := csumR (exclR unitO) unitR.

Definition to_tgkR (tk: tag_kind) : tagKindR :=
  match tk with tkUnique => Cinl (Excl ()) | tkPub => Cinr () end.

Definition heaplet := gmap loc (scalar * scalar).
Definition tmap := gmap ptr_id (tag_kind * heaplet).
Definition heapletR := gmapR loc (agreeR (prodO scalarO scalarO)).
(* ptr_id ⇀ TagKind * (loc ⇀ Ag(Scalar * Scalar)) *)
Definition tmapUR := gmapUR ptr_id (prodR tagKindR heapletR).

Definition to_hplR (h: heaplet) : heapletR := fmap to_agree h.
Definition to_tmUR (tm: tmap) : tmapUR :=
  fmap (λ kh, (to_tgkR kh.1, to_hplR kh.2)) tm.


Definition tag_locs := gmap ptr_id (gset loc).

(** CallId map that protects tags and their associated heaplet *)
(* Ex(tag ⇀ gset loc) *)
Definition callStateR := exclR (gmapO ptr_id (gsetO loc)).
Definition cmap := gmap call_id tag_locs.
(* call_id ⇀ CallState *)
Definition cmapUR := gmapUR call_id callStateR.
Definition to_cmUR (cm: cmap) : cmapUR := fmap Excl cm.

(** Local map that protects tags and their associated heaplet *)
Definition lmapUR := gmapUR ptr_id (exclR (gsetO loc)).
Definition to_lmUR (lm: tag_locs) : lmapUR := fmap Excl lm.

Definition res := (tmap * cmap * tag_locs)%type.
Definition resUR := prodUR (prodUR tmapUR cmapUR) lmapUR.

Definition rtm (r: resUR) : tmapUR := r.1.1.
Definition rcm (r: resUR) : cmapUR := r.1.2.
Definition rlm (r: resUR) : lmapUR := r.2.

Instance rtm_proper : Proper ((≡) ==> (≡)) rtm.
Proof. solve_proper. Qed.
Instance rcm_proper : Proper ((≡) ==> (≡)) rcm.
Proof. solve_proper. Qed.
Instance rlm_proper : Proper ((≡) ==> (≡)) rlm.
Proof. solve_proper. Qed.

Lemma local_update_discrete_valid_frame `{CmraDiscrete A} (r_f r r' : A) :
  ✓ (r_f ⋅ r) → (r_f ⋅ r, r) ~l~> (r_f ⋅ r', r') → ✓ (r_f ⋅ r').
Proof.
  intros VALID UPD. apply cmra_discrete_valid.
  apply (UPD O (Some r_f)); [by apply cmra_discrete_valid_iff|by rewrite /= comm].
Qed.

(** tag_kind properties *)
Lemma to_tgkR_valid k : valid (to_tgkR k).
Proof. by destruct k. Qed.

Lemma tag_kind_incl_eq (k1 k2: tagKindR):
  ✓ k2 → k1 ≼ k2 → k1 ≡ k2.
Proof.
  move => VAL /csum_included [? |[[? [? [? [? Eq]]]]|[[] [[] [? [? LE]]]]]];
    subst; [done|..|done].
  exfalso. eapply exclusive_included; [..|apply Eq|apply VAL]. apply _.
Qed.

Lemma tagKindR_exclusive (h0 h: heapletR) mb :
  mb ⋅ Some (to_tgkR tkUnique, h0) ≡ Some (to_tgkR tkPub, h) → False.
Proof.
  destruct mb as [[k ?]|]; [rewrite -Some_op pair_op|rewrite left_id];
    intros [Eq _]%Some_equiv_inj.
  - destruct k as [[]| |]; inversion Eq.
  - inversion Eq.
Qed.

Lemma tagKindR_exclusive_2 (h0 h: heapletR) mb :
  mb ⋅ Some (to_tgkR tkPub, h0) ≡ Some (to_tgkR tkUnique, h) → False.
Proof.
  destruct mb as [[k ?]|]; [rewrite -Some_op pair_op|rewrite left_id];
    intros [Eq _]%Some_equiv_inj.
  - destruct k as [[]| |]; inversion Eq.
  - inversion Eq.
Qed.

Lemma tagKindR_exclusive_heaplet' (h0 h: heapletR) mb k1 :
  mb ⋅ Some (to_tgkR tkUnique, h0) ≡ Some (to_tgkR k1, h) →
  h0 ≡ h ∧ k1 = tkUnique.
Proof.
  destruct mb as [[k ?]|]; [rewrite -Some_op pair_op|rewrite left_id];
    intros [Eq1 Eq2]%Some_equiv_inj.
  - destruct k as [[[]|]| |], k1 ; inversion Eq1; simplify_eq.
  - destruct k1; by inversion Eq1.
Qed.

Lemma tagKindR_exclusive_heaplet (h0 h: heapletR) mb :
  Some mb ⋅ Some (to_tgkR tkUnique, h0) ≡ Some (to_tgkR tkUnique, h) → False.
Proof.
  destruct mb as [c ]. rewrite -Some_op pair_op. intros [Eq _]%Some_equiv_inj.
  destruct c; inversion Eq; simpl in *; simplify_eq.
Qed.

Lemma tagKindR_valid (k: tagKindR) :
  valid k → ∃ k', k = to_tgkR k'.
Proof.
  destruct k as [[[]|]|[]|]; [|done|..|done]; intros VAL.
  - by exists tkUnique.
  - by exists tkPub.
Qed.

(** cmap properties *)
Lemma cmap_lookup_op_r (cm1 cm2: cmapUR) c (Tls: tag_locs)
  (VALID: ✓ (cm1 ⋅ cm2)) :
  cm2 !! c = Some (Excl Tls) → (cm1 ⋅ cm2) !! c = Some (Excl Tls).
Proof.
  intros HL. move : (VALID c). rewrite lookup_op HL.
  destruct (cm1 !! c) as [cs'|] eqn:Eqc; rewrite Eqc; [|done].
  rewrite -Some_op Some_valid.
  destruct cs'; auto; try inversion 1.
Qed.

Lemma cmap_lookup_op_l (cm1 cm2: cmapUR) c (Tls: tag_locs)
  (VALID: ✓ (cm1 ⋅ cm2)) :
  cm1 !! c = Some (Excl Tls) → (cm1 ⋅ cm2) !! c = Some (Excl Tls).
Proof.
  intros HL. move : (VALID c). rewrite lookup_op HL.
  destruct (cm2 !! c) as [cs'|] eqn:Eqc; rewrite Eqc; [|done].
  rewrite -Some_op Some_valid.
  destruct cs'; auto; try inversion 1.
Qed.

Lemma cmap_lookup_op_l_equiv (cm1 cm2: cmapUR) c (Tls: tag_locs)
  (VALID: ✓ (cm1 ⋅ cm2)) :
  cm1 !! c ≡ Some (Excl Tls) → (cm1 ⋅ cm2) !! c ≡ Some (Excl Tls).
Proof.
  intros HL. move : (VALID c). rewrite lookup_op HL.
  destruct (cm2 !! c) as [cs'|] eqn:Eqc; rewrite Eqc; [|done].
  rewrite -Some_op Some_valid.
  destruct cs'; auto; try inversion 1.
Qed.

Lemma cmap_lookup_op_unique_included (cm1 cm2: cmapUR) c (Tls: tag_locs)
  (VALID: ✓ cm2) (INCL: cm1 ≼ cm2) :
  cm1 !! c ≡ Some (Excl Tls) → cm2 !! c ≡ Some (Excl Tls).
Proof.
  destruct INCL as [cm' Eq]. rewrite Eq. apply cmap_lookup_op_l_equiv.
  by rewrite -Eq.
Qed.

Lemma cmap_insert_op_r (cm1 cm2: cmapUR) c Tls cs
  (VALID: ✓ (cm1 ⋅ cm2)):
  cm2 !! c = Some (Excl Tls) →
  cm1 ⋅ <[c:=cs]> cm2 = <[c:=cs]> (cm1 ⋅ cm2).
Proof.
  intros HL. apply (map_eq (cm1 ⋅ <[c:=cs]> cm2)). intros c'.
  move : (VALID c). rewrite 2!lookup_op HL.
  destruct (cm1 !! c) eqn:Eqc; rewrite Eqc; [inversion 1..|].
  intros VL.
  case (decide (c' = c)) => [->|?].
  - by rewrite 2!lookup_insert Eqc.
  - do 2 (rewrite lookup_insert_ne //). by rewrite lookup_op.
Qed.

Lemma callStateR_exclusive_Some (Tls1 Tls2: tag_locs) (cs: callStateR) :
  Some cs ⋅ Some (Excl Tls1) ≡ Some (Excl Tls2) → False.
Proof.
  rewrite -Some_op. intros Eq%Some_equiv_inj.
  destruct cs; inversion Eq; simplify_eq.
Qed.

Lemma callStateR_exclusive_eq (Tls1 Tls2: tag_locs) mb :
  mb ⋅ Some (Excl Tls1) ≡ Some (Excl Tls2) → Tls1 = Tls2.
Proof.
  destruct mb. by intros ?%callStateR_exclusive_Some.
  rewrite left_id. intros Eq%Some_equiv_inj. by simplify_eq.
Qed.

(** tmap properties *)
Lemma tmap_insert_op_r (pm1 pm2: tmapUR) t h0 kh
  (VALID: ✓ (pm1 ⋅ pm2)) :
  pm2 !! t = Some (to_tgkR tkUnique, h0) →
  pm1 ⋅ <[t:=kh]> pm2 = <[t:=kh]> (pm1 ⋅ pm2).
Proof.
  intros HL. apply (map_eq (pm1 ⋅ <[t:=kh]> pm2)). intros t'.
  move : (VALID t). rewrite 2!lookup_op HL.
  destruct (pm1 !! t) as [[k1 h1]|] eqn:Eqt; rewrite Eqt.
  - rewrite -Some_op pair_op. intros [?%exclusive_r]; [done|apply _].
  - intros VL.
    case (decide (t' = t)) => [->|?].
    + by rewrite 2!lookup_insert Eqt.
    + do 2 (rewrite lookup_insert_ne //). by rewrite lookup_op.
Qed.

Lemma tmap_lookup_op_r (pm1 pm2: tmapUR) t h0
  (VALID: ✓ (pm1 ⋅ pm2)) :
  pm2 !! t = Some (to_tgkR tkUnique, h0) →
  (pm1 ⋅ pm2) !! t = Some (to_tgkR tkUnique, h0).
Proof.
  intros HL. move : (VALID t). rewrite lookup_op HL.
  destruct (pm1 !! t) as [[k1 h1]|] eqn:Eqt; rewrite Eqt; [|done].
  rewrite -Some_op pair_op. intros [?%exclusive_r]; [done|apply _].
Qed.

Lemma tmap_lookup_op_l_uniq_equiv (pm1 pm2: tmapUR) t h0
  (VALID: ✓ (pm1 ⋅ pm2)):
  pm1 !! t ≡ Some (to_tgkR tkUnique, h0) →
  (pm1 ⋅ pm2) !! t ≡ Some (to_tgkR tkUnique, h0).
Proof.
  intros HL. move : (VALID t). rewrite lookup_op HL.
  destruct (pm2 !! t) as [[k2 h2]|] eqn:Eqt; rewrite Eqt; [|done].
  rewrite -Some_op pair_op. intros [?%exclusive_l]; [done|apply _].
Qed.

Lemma tmap_lookup_op_uniq_included (pm1 pm2: tmapUR) t h0
  (VALID: ✓ pm2) (INCL: pm1 ≼ pm2):
  pm1 !! t ≡ Some (to_tgkR tkUnique, h0) →
  pm2 !! t ≡ Some (to_tgkR tkUnique, h0).
Proof.
  destruct INCL as [cm' Eq]. rewrite Eq. apply tmap_lookup_op_l_uniq_equiv.
  by rewrite -Eq.
Qed.

Lemma tmap_lookup_op_r_uniq_equiv (pm1 pm2: tmapUR) t h0
  (VALID: ✓ (pm1 ⋅ pm2)) :
  pm2 !! t ≡ Some (to_tgkR tkUnique, h0) →
  (pm1 ⋅ pm2) !! t ≡ Some (to_tgkR tkUnique, h0).
Proof.
  intros HL. eapply tmap_lookup_op_uniq_included; [done|..|exact HL].
  by apply cmra_included_r.
Qed.


Lemma tmap_lookup_op_r_equiv_pub (pm1 pm2: tmapUR) t h2
  (VALID: ✓ (pm1 ⋅ pm2)):
  pm2 !! t ≡ Some (to_tgkR tkPub, h2) →
  ∃ h1, (pm1 ⋅ pm2) !! t ≡ Some (to_tgkR tkPub, h1 ⋅ h2).
Proof.
  intros HL. move : (VALID t). rewrite lookup_op.
  destruct (pm1 !! t) as [[k1 h1]|] eqn:Eqt; rewrite Eqt; rewrite -> HL.
  - rewrite -Some_op pair_op. move => [ VL1 ?]. exists h1. simpl in VL1.
    rewrite HL -Some_op pair_op.
    by rewrite -(tag_kind_incl_eq (to_tgkR tkPub) _ VL1 (cmra_included_r _ _)).
  - intros _. exists (∅: gmap loc _). by rewrite 2!left_id HL.
Qed.

Lemma tmap_valid (r_f r: tmapUR) t h0 kh
  (Eqtg: r !! t = Some (to_tgkR tkUnique, h0)) (VN: ✓ kh) :
  ✓ (r_f ⋅ r) → ✓ (r_f ⋅ (<[t:= kh]> r)).
Proof.
  intros VALID.
  apply (local_update_discrete_valid_frame _ _ _ VALID).
  have EQ := (tmap_insert_op_r _ _ _ _ kh VALID Eqtg). rewrite EQ.
  eapply (insert_local_update _ _ _
          (to_tgkR tkUnique, h0) (to_tgkR tkUnique, h0));
          [|exact Eqtg|by apply exclusive_local_update].
  by rewrite (tmap_lookup_op_r _ _ _ _ VALID Eqtg).
Qed.

(** heaplet *)
Lemma to_hplR_valid h : ✓ (to_hplR h).
Proof.
  intros l. rewrite /to_hplR lookup_fmap.
  destruct (h !! l) eqn:Eq; rewrite Eq //.
Qed.

Lemma to_hplR_lookup h l s :
  to_hplR h !! l ≡ Some (to_agree s) → h !! l = Some s.
Proof.
  rewrite /to_hplR lookup_fmap.
  destruct (h !! l) as [s'|] eqn:Eqs; rewrite Eqs /=; [|by inversion 1].
  intros Eq%Some_equiv_inj%to_agree_inj%leibniz_equiv_iff. by subst s'.
Qed.

Lemma heapletR_elem_of_dom (h: heapletR) l (VALID: valid h) :
  l ∈ dom (gset loc) h → ∃ s, h !! l ≡ Some (to_agree s).
Proof.
  rewrite elem_of_dom. intros [sa Eqs]. move : (VALID l). rewrite Eqs.
  intros [s Eq]%to_agree_uninj. exists s. by rewrite Eq.
Qed.

(** lmap *)
Lemma lmap_lookup_op_r (lm1 lm2 : lmapUR)
  (VALID: ✓ (lm1 ⋅ lm2)) t ls :
  lm2 !! t ≡ Some ls → (lm1 ⋅ lm2) !! t ≡ Some ls.
Proof.
  intros Eq. move : (VALID t). rewrite lookup_op Eq.
  destruct (lm1 !! t) as [ls2|] eqn:Eql; rewrite Eql; [|by rewrite left_id].
  rewrite -Some_op.
  destruct ls, ls2; simpl; try inversion 1.
Qed.

Lemma lmap_lookup_op_l (lm1 lm2 : lmapUR)
  (VALID: ✓ (lm1 ⋅ lm2)) t ls :
  lm1 !! t ≡ Some ls → (lm1 ⋅ lm2) !! t ≡ Some ls.
Proof.
  intros Eq. move : (VALID t). rewrite lookup_op Eq.
  destruct (lm2 !! t) as [ls2|] eqn:Eql; rewrite Eql; [|by rewrite right_id].
  rewrite -Some_op.
  destruct ls, ls2; simpl; try inversion 1.
Qed.

Lemma lmap_lookup_op_included (lm1 lm2 : lmapUR) t ls
  (VALID: ✓ lm2) (INCL: (lm1 : lmapUR) ≼ (lm2 : lmapUR)):
  lm1 !! t ≡ Some ls → lm2 !! t ≡ Some ls.
Proof.
  destruct INCL as [cm' Eq]. rewrite Eq. apply lmap_lookup_op_l. by rewrite -Eq.
Qed.

Lemma lmap_exclusive_eq_l (tls: gset loc)
  (c: (exclR (gsetO loc))) (mb: optionR (exclR (gsetO loc))) :
  Some c ⋅ mb ≡ Some (Excl tls) → c ≡ Excl tls.
Proof.
  intros Eq.
  have VALID: valid (Some c ⋅ mb) by rewrite Eq. move :Eq.
  destruct c, mb as [[]|]; simplify_eq; try done.
  rewrite right_id. by intros ?%Some_equiv_inj.
Qed.

(** The Core *)

Lemma heaplet_core (h: heapletR) : core h = h.
Proof.
  apply (map_eq (M:=gmap loc)).
  intros l. rewrite lookup_core.
  by destruct (h !! l) as [s|] eqn:Eql; rewrite Eql.
Qed.

Lemma tmap_lookup_core_pub (pm: tmapUR) t h:
  pm !! t ≡ Some (to_tgkR tkPub, h) →
  core pm !! t ≡ Some (to_tgkR tkPub, h).
Proof. intros Eq. rewrite lookup_core Eq /core /= core_id //. Qed.

(** Resources that we own. *)

Definition res_tag tg tk (h: heaplet) : resUR :=
  ({[tg := (to_tgkR tk, to_agree <$> h)]}, ε, ε).

Definition res_cs (c: call_id) (cs: tag_locs) : resUR :=
  (ε, to_cmUR {[c := cs]}, ε).

Fixpoint locs_seq (l:loc) (n:nat) : gset loc :=
  match n with
  | O => ∅
  | S n => {[l]} ∪ locs_seq (l +ₗ 1) n
  end.

Definition res_loc l n t : resUR := (ε, to_lmUR {[t := locs_seq l n]}).

Fixpoint write_hpl l (v: list (scalar * scalar)) (h: heaplet) : heaplet :=
  match v with
  | [] => h
  | sst :: v' => write_hpl (l +ₗ 1) v' (<[l:=sst]> h)
  end.

Definition res_mapsto (l:loc) (v: list (scalar * scalar)) (t: ptr_id) : resUR :=
  res_loc l (length v) t ⋅ res_tag t tkUnique (write_hpl l v ∅).

(** res_tag *)
Lemma res_tag_alloc_local_update lsf t k h
  (FRESH: lsf.(rtm) !! t = None) :
  (lsf, ε) ~l~> (lsf ⋅ res_tag t k h, res_tag t k h).
Proof.
  destruct lsf as [[tm cm] lm]. rewrite 2!pair_op right_id right_id.
  apply prod_local_update_1, prod_local_update_1.
  rewrite cmra_comm -insert_singleton_op //.
  apply alloc_singleton_local_update; [done|].
  split. by destruct k. apply to_hplR_valid.
Qed.

Lemma res_tag_uniq_insert_local_update_inner (tm: tmapUR) t k2 (h1 h2: heaplet):
  tm !! t = None →
  (tm ⋅ {[t := (to_tgkR tkUnique, to_hplR h1)]},
    {[t := (to_tgkR tkUnique, to_hplR h1)]}) ~l~>
  (tm ⋅ {[t := (to_tgkR k2, to_hplR h2)]}, {[t := (to_tgkR k2, to_hplR h2)]}).
Proof.
  intros.
  do 2 rewrite (cmra_comm tm) -insert_singleton_op //.
  rewrite -(insert_insert tm t (_, to_agree <$> h2)
                               (Cinl (Excl ()), to_agree <$> h1)).
  eapply (singleton_local_update (<[t := _]> tm : tmapUR)).
  - by rewrite lookup_insert.
  - apply exclusive_local_update.
    split; [apply to_tgkR_valid|apply to_hplR_valid].
Qed.

Lemma res_tag_uniq_local_update (r: resUR) t h k' h'
  (NONE: r.(rtm) !! t = None) :
  (r ⋅ res_tag t tkUnique h, res_tag t tkUnique h) ~l~>
  (r ⋅ res_tag t k' h', res_tag t k' h').
Proof.
  destruct r as [[tm cm] lm].
  apply prod_local_update_1, prod_local_update_1. rewrite /=.
  by apply res_tag_uniq_insert_local_update_inner.
Qed.

Lemma res_tag_1_insert_local_update (r: resUR) (l: loc) s1 s2 (t: ptr_id)
  (NONE: r.(rtm) !! t = None):
  (r ⋅ res_tag t tkUnique {[l := s1]}, res_tag t tkUnique {[l := s1]}) ~l~>
  (r ⋅ res_tag t tkUnique {[l := s2]}, res_tag t tkUnique {[l := s2]}).
Proof. by apply res_tag_uniq_local_update. Qed.

Lemma res_tag_1_insert_local_update_r (r: resUR) r' (l: loc) s1 s2 (t: ptr_id)
  (NONE: r.(rtm) !! t = None):
  (r ⋅ res_tag t tkUnique {[l := s1]}, (ε, r') ⋅ res_tag t tkUnique {[l := s1]}) ~l~>
  (r ⋅ res_tag t tkUnique {[l := s2]}, (ε, r') ⋅ res_tag t tkUnique {[l := s2]}).
Proof.
  destruct r as [[tm cm] lm].
  apply prod_local_update_1, prod_local_update_1. rewrite /= 2!left_id.
  by apply (res_tag_uniq_insert_local_update_inner _ _ tkUnique).
Qed.

Lemma res_tag_lookup (k: tag_kind) (h: heaplet) (t: ptr_id) :
  (res_tag t k h).(rtm) !! t ≡ Some (to_tgkR k, to_agree <$> h).
Proof. by rewrite lookup_insert. Qed.

Lemma res_tag_lookup_ne (k: tag_kind) (h: heaplet) (t t': ptr_id) (NEQ: t' ≠ t) :
  (res_tag t k h).(rtm) !! t' ≡ None.
Proof. by rewrite lookup_insert_ne. Qed.

(** res_mapsto *)

Lemma res_loc_lookup l n t :
  (res_loc l n t).(rlm) !! t ≡ Some (Excl $ locs_seq l n).
Proof. rewrite /= lookup_fmap lookup_insert //. Qed.

Lemma res_mapsto_llookup l v t :
  (res_mapsto l v t).(rlm) !! t ≡ Some (Excl $ locs_seq l (length v)).
Proof. rewrite lookup_op res_loc_lookup //. Qed.

Lemma res_mapsto_tlookup l v (t: ptr_id) :
  (res_mapsto l v t).(rtm) !! t ≡
    Some (to_tgkR tkUnique, to_agree <$> (write_hpl l v ∅)).
Proof. by rewrite lookup_op /= lookup_empty left_id lookup_insert. Qed.

Lemma res_mapsto_tlookup_ne l v (t t': ptr_id) (NEQ: t' ≠ t) :
  (res_mapsto l v t).(rtm) !! t' ≡ None.
Proof. by rewrite lookup_op /= lookup_empty left_id lookup_insert_ne. Qed.

(** allocating locals *)

Lemma res_loc_alloc_local_update (lm: lmapUR) (t: ptr_id) ls :
  lm !! t = None →
  (lm, ε) ~l~> (lm ⋅ (to_lmUR {[t := ls]}), (to_lmUR {[t := ls]})).
Proof.
  intros FRESH.
  rewrite /to_lmUR fmap_insert fmap_empty insert_empty
          (cmra_comm _  {[t := _]}) -insert_singleton_op //.
  by apply alloc_local_update.
Qed.

Lemma res_mapsto_alloc_local_update r l v t:
  r.(rtm) !! t = None → r.(rlm) !! t = None →
  (r, ε) ~l~> (r ⋅ res_mapsto l v t, res_mapsto l v t).
Proof.
  intros FRESH1 FRESH2. destruct r as [[tm cm] lm].
  rewrite /res_mapsto (cmra_comm (res_loc _ _ _)).
  etrans.
  - by apply (res_tag_alloc_local_update _ t tkUnique (write_hpl l v ∅)).
  - rewrite !pair_op !right_id left_id /=.
    by apply prod_local_update_2, res_loc_alloc_local_update.
Qed.

(** deallocating locals *)

Lemma res_loc_dealloc_local_update (lm: lmapUR) t ls:
  lm !! t = None →
  (lm ⋅ (to_lmUR {[t := ls]}), to_lmUR {[t := ls]}) ~l~> (lm, ε).
Proof.
  intros ?.
  rewrite /to_lmUR fmap_insert fmap_empty insert_empty
          (cmra_comm _  {[t := _]}) -insert_singleton_op; [|done].
  etrans.
  - eapply (delete_local_update_cancelable _ _ t); [|by rewrite lookup_insert..].
    apply _.
  - rewrite 2!delete_insert_delete delete_empty delete_notin //.
Qed.

Lemma res_mapsto_res_tag (r: resUR) l v t k' h'
  (NONE1: r.(rlm) !! t = None)
  (NONE2: r.(rtm) !! t = None):
  (r ⋅ res_mapsto l v t, res_mapsto l v t) ~l~>
  (r ⋅ res_tag t k' h', res_tag t k' h').
Proof.
  rewrite /res_mapsto. destruct r as [[tm cm] lm].
  rewrite (cmra_comm (res_loc _ _ _)) cmra_assoc. etrans.
  - apply prod_local_update_2. rewrite /= right_id left_id.
    by apply res_loc_dealloc_local_update.
  - rewrite !pair_op /= !right_id.
    apply prod_local_update_1, prod_local_update_1. rewrite /=.
    by apply (res_tag_uniq_insert_local_update_inner _ _ k').
Qed.

(** updating locals *)
Lemma res_mapsto_1_insert_local_update (r: resUR) (l: loc) s1 s2 (t: ptr_id)
  (NONE: r.(rtm) !! t = None) :
  (r ⋅ res_mapsto l [s1] t, res_mapsto l [s1] t) ~l~>
  (r ⋅ res_mapsto l [s2] t, res_mapsto l [s2] t).
Proof.
  intros. rewrite /res_mapsto cmra_assoc. etrans.
  - eapply res_tag_1_insert_local_update_r.
    by rewrite lookup_op NONE /= lookup_empty right_id_L.
  - rewrite -(cmra_assoc r) 2!(cmra_comm (res_loc _ _ _)) 2!cmra_assoc
            /= insert_empty //.
Qed.

Lemma res_mapsto_tdom l v t:
  dom (gset nat) (res_mapsto l v t).(rtm) ≡ {[t]}.
Proof.
  intros t1.
  rewrite elem_of_dom /res_mapsto lookup_op /= left_id elem_of_singleton.
  case (decide (t1 = t)) => ?.
  - subst t1. rewrite lookup_insert. naive_solver.
  - rewrite lookup_insert_ne // lookup_empty. split; [by destruct 1|done].
Qed.

Lemma res_mapsto_ldom l v t:
  dom (gset nat) (res_mapsto l v t).(rlm) ≡ {[t]}.
Proof.
  intros t1.
  rewrite elem_of_dom /res_mapsto lookup_op /= right_id elem_of_singleton
          /to_lmUR lookup_fmap.
  case (decide (t1 = t)) => ?.
  - subst t1. rewrite lookup_insert. naive_solver.
  - rewrite lookup_insert_ne // lookup_empty. split; [by destruct 1|done].
Qed.
