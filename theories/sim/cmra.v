From iris.algebra Require Export local_updates.
From iris.algebra Require Export cmra gmap gset csum agree excl big_op.

From stbor.lang Require Export lang.

Set Default Proof Using "Type".

Inductive tag_kind := tkUnique | tkPub.
(* Ex() + Ag() *)
Definition tagKindR := csumR (exclR unitO) unitR.

Definition to_tagKindR (tk: tag_kind) : tagKindR :=
  match tk with tkUnique => Cinl (Excl ()) | tkPub => Cinr () end.

Inductive call_state := csOwned (T: gset ptr_id) | csPub.
(* Ex(ptr_id) + Ag() *)
Definition callStateR := csumR (exclR (gsetO ptr_id)) unitR.

Definition to_callStateR (cs: call_state) : callStateR :=
  match cs with csOwned T => Cinl (Excl T) | csPub => Cinr () end.

Definition cmap := gmap call_id call_state.
(* call_id ⇀ CallState *)
Definition cmapUR := gmapUR call_id callStateR.

Definition to_cmapUR (cm: cmap) : cmapUR := fmap to_callStateR cm.

Notation heaplet := mem.
Definition tmap := gmap ptr_id (tag_kind * heaplet).
Definition heapletR := gmapR loc (agreeR scalarC).
(* ptr_id ⇀ TagKid x (loc ⇀ Ag(Scalar)) *)
Definition tmapUR := gmapUR ptr_id (prodR tagKindR heapletR).

Definition to_heapR (h: heaplet) : heapletR := fmap to_agree h.
Definition to_tmapUR (pm: tmap) : tmapUR :=
  fmap (λ tm, (to_tagKindR tm.1, to_heapR tm.2)) pm.

Definition lmap := gmap loc ptr_id.
Definition tagR := exclR (leibnizO ptr_id).
Definition lmapUR := gmapUR loc tagR.
Definition to_tagR (t: ptr_id) := Excl t.

Definition res := (tmap * cmap * lmap)%type.
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
Lemma tag_kind_incl_eq (k1 k2: tagKindR):
  ✓ k2 → k1 ≼ k2 → k1 ≡ k2.
Proof.
  move => VAL /csum_included [? |[[? [? [? [? Eq]]]]|[[] [[] [? [? LE]]]]]];
    subst; [done|..|done].
  exfalso. eapply exclusive_included; [..|apply Eq|apply VAL]. apply _.
Qed.

Lemma tagKindR_exclusive (h0 h: heapletR) mb :
  mb ⋅ Some (to_tagKindR tkUnique, h0) ≡ Some (to_tagKindR tkPub, h) → False.
Proof.
  destruct mb as [[k ?]|]; [rewrite -Some_op pair_op|rewrite left_id];
    intros [Eq _]%Some_equiv_inj.
  - destruct k as [[]| |]; inversion Eq.
  - inversion Eq.
Qed.

Lemma tagKindR_exclusive_2 (h0 h: heapletR) mb :
  mb ⋅ Some (to_tagKindR tkPub, h0) ≡ Some (to_tagKindR tkUnique, h) → False.
Proof.
  destruct mb as [[k ?]|]; [rewrite -Some_op pair_op|rewrite left_id];
    intros [Eq _]%Some_equiv_inj.
  - destruct k as [[]| |]; inversion Eq.
  - inversion Eq.
Qed.

Lemma tagKindR_exclusive_heaplet' (h0 h: heapletR) mb k1 :
  mb ⋅ Some (to_tagKindR tkUnique, h0) ≡ Some (to_tagKindR k1, h) →
  h0 ≡ h ∧ k1 = tkUnique.
Proof.
  destruct mb as [[k ?]|]; [rewrite -Some_op pair_op|rewrite left_id];
    intros [Eq1 Eq2]%Some_equiv_inj.
  - destruct k as [[[]|]| |], k1 ; inversion Eq1; simplify_eq.
  - destruct k1; by inversion Eq1.
Qed.

Lemma tagKindR_exclusive_heaplet (h0 h: heapletR) mb :
  Some mb ⋅ Some (to_tagKindR tkUnique, h0) ≡ Some (to_tagKindR tkUnique, h) → False.
Proof.
  destruct mb as [c ]. rewrite -Some_op pair_op. intros [Eq _]%Some_equiv_inj.
  destruct c; inversion Eq; simpl in *; simplify_eq.
Qed.

Lemma tagKindR_valid (k: tagKindR) :
  valid k → ∃ k', k = to_tagKindR k'.
Proof.
  destruct k as [[[]|]|[]|]; [|done|..|done]; intros VAL.
  - by exists tkUnique.
  - by exists tkPub.
Qed.

(** cmap properties *)
Lemma cmap_lookup_op_r (cm1 cm2: cmapUR) c T (VALID: ✓ (cm1 ⋅ cm2)):
  cm2 !! c = Some (to_callStateR (csOwned T)) →
  (cm1 ⋅ cm2) !! c = Some (to_callStateR (csOwned T)).
Proof.
  intros HL. move : (VALID c). rewrite lookup_op HL.
  destruct (cm1 !! c) as [cs'|] eqn:Eqc; rewrite Eqc; [|done].
  rewrite -Some_op Some_valid.
  destruct cs' as [[]|c2|]; auto; try inversion 1.
Qed.

Lemma cmap_lookup_op_l (cm1 cm2: cmapUR) c T (VALID: ✓ (cm1 ⋅ cm2)):
  cm1 !! c = Some (to_callStateR (csOwned T)) →
  (cm1 ⋅ cm2) !! c = Some (to_callStateR (csOwned T)).
Proof.
  intros HL. move : (VALID c). rewrite lookup_op HL.
  destruct (cm2 !! c) as [cs'|] eqn:Eqc; rewrite Eqc; [|done].
  rewrite -Some_op Some_valid.
  destruct cs' as [[]|c2|]; auto; try inversion 1.
Qed.

Lemma cmap_lookup_op_l_equiv (cm1 cm2: cmapUR) c T (VALID: ✓ (cm1 ⋅ cm2)):
  cm1 !! c ≡ Some (to_callStateR (csOwned T)) →
  (cm1 ⋅ cm2) !! c ≡ Some (to_callStateR (csOwned T)).
Proof.
  intros HL. move : (VALID c). rewrite lookup_op HL.
  destruct (cm2 !! c) as [cs'|] eqn:Eqc; rewrite Eqc; [|done].
  rewrite -Some_op Some_valid.
  destruct cs' as [[]|c2|]; auto; try inversion 1.
Qed.

Lemma cmap_lookup_op_unique_included (cm1 cm2: cmapUR)
  c T (VALID: ✓ cm2) (INCL: cm1 ≼ cm2):
  cm1 !! c ≡ Some (to_callStateR (csOwned T)) →
  cm2 !! c ≡ Some (to_callStateR (csOwned T)).
Proof.
  destruct INCL as [cm' Eq]. rewrite Eq. apply cmap_lookup_op_l_equiv.
  by rewrite -Eq.
Qed.

Lemma cmap_lookup_op_l_equiv_pub (cm1 cm2: cmapUR) c (VALID: ✓ (cm1 ⋅ cm2)):
  cm1 !! c ≡ Some (to_callStateR csPub) →
  (cm1 ⋅ cm2) !! c ≡ Some (to_callStateR csPub).
Proof.
  intros HL. move : (VALID c). rewrite lookup_op HL.
  destruct (cm2 !! c) as [cs'|] eqn:Eqc; rewrite Eqc; [|done].
  rewrite -Some_op Some_valid.
  destruct cs' as [[]|c2|]; auto; inversion 1.
Qed.

Lemma cmap_insert_op_r (cm1 cm2: cmapUR) c T cs (VALID: ✓ (cm1 ⋅ cm2)):
  cm2 !! c = Some (to_callStateR (csOwned T)) →
  cm1 ⋅ <[c:=cs]> cm2 = <[c:=cs]> (cm1 ⋅ cm2).
Proof.
  intros HL. apply (map_eq (cm1 ⋅ <[c:=cs]> cm2)). intros c'.
  move : (VALID c). rewrite 2!lookup_op HL.
  destruct (cm1 !! c) as [[| |]|] eqn:Eqc; rewrite Eqc; [inversion 1..|].
  intros VL.
  case (decide (c' = c)) => [->|?].
  - by rewrite 2!lookup_insert Eqc.
  - do 2 (rewrite lookup_insert_ne //). by rewrite lookup_op.
Qed.

Lemma callStateR_exclusive_2 T mb :
  mb ⋅ Some (to_callStateR csPub) ≡ Some (to_callStateR (csOwned T)) → False.
Proof.
  destruct mb as [cs|]; [rewrite -Some_op|rewrite left_id];
    intros Eq%Some_equiv_inj.
  - destruct cs; inversion Eq.
  - inversion Eq.
Qed.

Lemma callStateR_exclusive_Some T1 T2 cs :
  Some cs ⋅ Some (to_callStateR (csOwned T1)) ≡ Some (to_callStateR (csOwned T2)) → False.
Proof.
  rewrite -Some_op. intros Eq%Some_equiv_inj.
  destruct cs as [[]| |]; inversion Eq; simplify_eq.
Qed.

Lemma callStateR_exclusive_eq T1 T2 mb :
  mb ⋅ Some (to_callStateR (csOwned T1)) ≡ Some (to_callStateR (csOwned T2)) → T1 = T2.
Proof.
  destruct mb. by intros ?%callStateR_exclusive_Some.
  rewrite left_id. intros Eq%Some_equiv_inj. by simplify_eq.
Qed.

(** tmap properties *)
Lemma tmap_insert_op_r (pm1 pm2: tmapUR) t h0 kh (VALID: ✓ (pm1 ⋅ pm2)):
  pm2 !! t = Some (to_tagKindR tkUnique, h0) →
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

Lemma tmap_lookup_op_r (pm1 pm2: tmapUR) t h0 (VALID: ✓ (pm1 ⋅ pm2)):
  pm2 !! t = Some (to_tagKindR tkUnique, h0) →
  (pm1 ⋅ pm2) !! t = Some (to_tagKindR tkUnique, h0).
Proof.
  intros HL. move : (VALID t). rewrite lookup_op HL.
  destruct (pm1 !! t) as [[k1 h1]|] eqn:Eqt; rewrite Eqt; [|done].
  rewrite -Some_op pair_op. intros [?%exclusive_r]; [done|apply _].
Qed.

Lemma tmap_lookup_op_r_unique_equiv (pm1 pm2: tmapUR) t h0 (VALID: ✓ (pm1 ⋅ pm2)):
  pm2 !! t ≡ Some (to_tagKindR tkUnique, h0) →
  (pm1 ⋅ pm2) !! t ≡ Some (to_tagKindR tkUnique, h0).
Proof.
  intros HL. move : (VALID t). rewrite lookup_op HL.
  destruct (pm1 !! t) as [[k1 h1]|] eqn:Eqt; rewrite Eqt; [|done].
  rewrite -Some_op pair_op. intros [?%exclusive_r]; [done|apply _].
Qed.

Lemma tmap_lookup_op_l_unique_equiv (pm1 pm2: tmapUR) t h0
  (VALID: ✓ (pm1 ⋅ pm2)):
  pm1 !! t ≡ Some (to_tagKindR tkUnique, h0) →
  (pm1 ⋅ pm2) !! t ≡ Some (to_tagKindR tkUnique, h0).
Proof.
  intros HL. move : (VALID t). rewrite lookup_op HL.
  destruct (pm2 !! t) as [[k2 h2]|] eqn:Eqt; rewrite Eqt; [|done].
  rewrite -Some_op pair_op. intros [?%exclusive_l]; [done|apply _].
Qed.

Lemma tmap_lookup_op_unique_included (pm1 pm2: tmapUR) t h0
  (VALID: ✓ pm2) (INCL: pm1 ≼ pm2):
  pm1 !! t ≡ Some (to_tagKindR tkUnique, h0) →
  pm2 !! t ≡ Some (to_tagKindR tkUnique, h0).
Proof.
  destruct INCL as [cm' Eq]. rewrite Eq. apply tmap_lookup_op_l_unique_equiv.
  by rewrite -Eq.
Qed.

Lemma tmap_lookup_op_r_equiv_pub (pm1 pm2: tmapUR) t h2 (VALID: ✓ (pm1 ⋅ pm2)):
  pm2 !! t ≡ Some (to_tagKindR tkPub, h2) →
  ∃ h1, (pm1 ⋅ pm2) !! t ≡ Some (to_tagKindR tkPub, h1 ⋅ h2).
Proof.
  intros HL. move : (VALID t). rewrite lookup_op.
  destruct (pm1 !! t) as [[k1 h1]|] eqn:Eqt; rewrite Eqt; rewrite -> HL.
  - rewrite -Some_op pair_op. move => [ VL1 ?]. exists h1. simpl in VL1.
    rewrite HL -Some_op pair_op.
    by rewrite -(tag_kind_incl_eq (to_tagKindR tkPub) _ VL1 (cmra_included_r _ _)).
  - intros _. exists (∅: gmap loc _). by rewrite 2!left_id HL.
Qed.

Lemma tmap_valid (r_f r: tmapUR) t h0 kh
  (Eqtg: r !! t = Some (to_tagKindR tkUnique, h0)) (VN: ✓ kh) :
  ✓ (r_f ⋅ r) → ✓ (r_f ⋅ (<[t:= kh]> r)).
Proof.
  intros VALID.
  apply (local_update_discrete_valid_frame _ _ _ VALID).
  have EQ := (tmap_insert_op_r _ _ _ _ kh VALID Eqtg). rewrite EQ.
  eapply (insert_local_update _ _ _
          (to_tagKindR tkUnique, h0) (to_tagKindR tkUnique, h0));
          [|exact Eqtg|by apply exclusive_local_update].
  by rewrite (tmap_lookup_op_r _ _ _ _ VALID Eqtg).
Qed.

(** heaplet *)
Lemma to_heapR_valid h : ✓ (to_heapR h).
Proof.
  intros l. rewrite /to_heapR lookup_fmap.
  destruct (h !! l) eqn:Eq; rewrite Eq //.
Qed.

Lemma to_heapR_lookup h l s :
  to_heapR h !! l ≡ Some (to_agree s) → h !! l = Some s.
Proof.
  rewrite /to_heapR lookup_fmap.
  destruct (h !! l) as [s'|] eqn:Eqs; rewrite Eqs /=; [|by inversion 1].
  intros Eq%Some_equiv_inj%to_agree_inj. by inversion Eq.
Qed.

Lemma heapletR_elem_of_dom (h: heapletR) l (VALID: valid h) :
  l ∈ dom (gset loc) h → ∃ s, h !! l ≡ Some (to_agree s).
Proof.
  rewrite elem_of_dom. intros [sa Eqs]. move : (VALID l). rewrite Eqs.
  intros [s Eq]%to_agree_uninj. exists s. by rewrite Eq.
Qed.

(** lmap *)
Lemma lmap_lookup_op_r (lm1 lm2 : lmapUR) (VALID: ✓ (lm1 ⋅ lm2)) l ls :
  lm2 !! l ≡ Some ls → ((lm1 ⋅ lm2) !! l : optionR tagR) ≡ Some ls.
Proof.
  intros Eq. move : (VALID l). rewrite lookup_op Eq.
  destruct (lm1 !! l) as [ls2|] eqn:Eql; rewrite Eql; [|by rewrite left_id].
  rewrite -Some_op.
  destruct ls, ls2; simpl; try inversion 1.
Qed.

Lemma lmap_lookup_op_l (lm1 lm2 : lmapUR) (VALID: ✓ (lm1 ⋅ lm2)) l ls :
  lm1 !! l ≡ Some ls → (lm1 ⋅ lm2) !! l ≡ Some ls.
Proof.
  intros Eq. move : (VALID l). rewrite lookup_op Eq.
  destruct (lm2 !! l) as [ls2|] eqn:Eql; rewrite Eql; [|by rewrite right_id].
  rewrite -Some_op.
  destruct ls, ls2; simpl; try inversion 1.
Qed.

Lemma lmap_lookup_op_included (lm1 lm2 : lmapUR) (l: loc) (t: ptr_id)
  (VALID: ✓ lm2) (INCL: (lm1 : lmapUR) ≼ (lm2 : lmapUR)):
  (lm1 !! l : optionR tagR) ≡ Some $ to_tagR t → (lm2 !! l : optionR tagR) ≡ Some $ to_tagR t.
Proof.
  destruct INCL as [cm' Eq]. rewrite Eq. apply lmap_lookup_op_l. by rewrite -Eq.
Qed.

Lemma lmap_exclusive_2 t1 t2 (c: tagR) :
  Some c ⋅ Some (to_tagR t1) ≡ Some (to_tagR t2) → False.
Proof.
  rewrite -Some_op. intros Eq%Some_equiv_inj.
  destruct c; inversion Eq.
Qed.

Lemma tagR_valid (ls: tagR) : valid ls → ∃ t, ls = to_tagR t.
Proof. destruct ls as [t|]; simpl; [|done]. naive_solver. Qed.

Lemma lmap_exclusive_eq_l t (c: tagR) (mb: optionR tagR) :
  Some c ⋅ mb ≡ Some (to_tagR t) → c ≡ to_tagR t.
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
  pm !! t ≡ Some (to_tagKindR tkPub, h) →
  core pm !! t ≡ Some (to_tagKindR tkPub, h).
Proof. intros Eq. rewrite lookup_core Eq /core /= core_id //. Qed.

(** Resources that we own. *)

Definition res_tag tg tk (h: heaplet) : resUR :=
  ({[tg := (to_tagKindR tk, to_agree <$> h)]}, ε, ε).

Definition res_callState (c: call_id) (cs: call_state) : resUR :=
  (ε, {[c := to_callStateR cs]}, ε).


Fixpoint write_local (l:loc) (n:nat) (t: ptr_id) (ls: lmap) : lmap :=
  match n with
  | O => ls
  | S n => <[l := t]>(write_local (l +ₗ 1) n t ls)
  end.

Definition res_loc l n t : resUR := (ε, to_tagR <$> (write_local l n t ∅)).

Definition res_mapsto (l:loc) (v: value) (t: ptr_id) : resUR :=
  res_loc l (length v) t ⋅ res_tag t tkUnique (write_mem l v ∅).

(** res_tag *)
Lemma res_tag_alloc_local_update lsf t k h (FRESH: lsf.(rtm) !! t = None) :
  (lsf, ε) ~l~> (lsf ⋅ res_tag t k h, res_tag t k h).
Proof.
  destruct lsf as [[tm cm] lm]. rewrite 2!pair_op right_id right_id.
  apply prod_local_update_1, prod_local_update_1.
  rewrite cmra_comm -insert_singleton_op //.
  apply alloc_singleton_local_update; [done|].
  split. by destruct k. apply to_heapR_valid.
Qed.


Lemma res_tag_unique_pub_local_update (r: resUR) t h
  (NONE: r.(rtm) !! t = None) :
  (r ⋅ res_tag t tkUnique h, res_tag t tkUnique h) ~l~>
  (r ⋅ res_tag t tkPub ∅, res_tag t tkPub ∅).
Proof.
  destruct r as [[tm cm] lm].
  apply prod_local_update_1, prod_local_update_1. rewrite /=.
  do 2 rewrite (cmra_comm tm) -insert_singleton_op //.
  rewrite -(insert_insert tm t (Cinr (), to_agree <$> ∅)
                               (Cinl (Excl ()), to_agree <$> h)).
  eapply (singleton_local_update (<[t := _]> tm : tmapUR)).
  by rewrite lookup_insert.
  apply exclusive_local_update. split; [done|apply to_heapR_valid].
Qed.

Lemma res_tag_insert_local_update (r: resUR) h1 h2 (t: ptr_id)
  (NONE: r.(rtm) !! t = None):
  (r ⋅ res_tag t tkUnique h1, res_tag t tkUnique h1) ~l~>
  (r ⋅ res_tag t tkUnique h2, res_tag t tkUnique h2).
Proof.
  destruct r as [[tm cm] lm].
  apply prod_local_update_1, prod_local_update_1. rewrite /=.
  do 2 rewrite (cmra_comm tm) -insert_singleton_op //.
  rewrite -(insert_insert tm t (_, to_agree <$> h2)
                               (Cinl (Excl ()), to_agree <$> h1)).
  eapply (singleton_local_update (<[t := _]> tm : tmapUR)).
  by rewrite lookup_insert.
  apply exclusive_local_update. split; [done|apply to_heapR_valid].
Qed.

Lemma res_tag_1_insert_local_update (r: resUR) (l: loc) s1 s2 (t: ptr_id)
  (NONE: r.(rtm) !! t = None):
  (r ⋅ res_tag t tkUnique {[l := s1]}, res_tag t tkUnique {[l := s1]}) ~l~>
  (r ⋅ res_tag t tkUnique {[l := s2]}, res_tag t tkUnique {[l := s2]}).
Proof. by apply res_tag_insert_local_update. Qed.

Lemma res_tag_1_insert_local_update_r (r: resUR) r' (l: loc) s1 s2 (t: ptr_id)
  (NONE: r.(rtm) !! t = None):
  (r ⋅ res_tag t tkUnique {[l := s1]}, (ε, r') ⋅ res_tag t tkUnique {[l := s1]}) ~l~>
  (r ⋅ res_tag t tkUnique {[l := s2]}, (ε, r') ⋅ res_tag t tkUnique {[l := s2]}).
Proof.
  destruct r as [[tm cm] lm].
  apply prod_local_update_1, prod_local_update_1. rewrite /= 2!left_id.
  do 2 rewrite (cmra_comm tm) -insert_singleton_op //.
  rewrite -(insert_insert tm t (_, to_agree <$> {[l := s2]})
                               (Cinl (Excl ()), to_agree <$> {[l := s1]})).
  eapply (singleton_local_update (<[t := _]> tm : tmapUR)).
  by rewrite lookup_insert.
  apply exclusive_local_update. split; [done|apply to_heapR_valid].
Qed.

Lemma res_tag_lookup (k: tag_kind) (h: heaplet) (t: ptr_id) :
  (res_tag t k h).(rtm) !! t ≡ Some (to_tagKindR k, to_agree <$> h).
Proof. by rewrite lookup_insert. Qed.

Lemma res_tag_lookup_ne (k: tag_kind) (h: heaplet) (t t': ptr_id) (NEQ: t' ≠ t) :
  (res_tag t k h).(rtm) !! t' ≡ None.
Proof. by rewrite lookup_insert_ne. Qed.

(** res_mapsto *)
Lemma write_local_lookup l n t ls :
  (∀ (i: nat), (i < n)%nat →
    write_local l n t ls !! (l +ₗ i) = Some t) ∧
  (∀ (l': loc), (∀ (i: nat), (i < n)%nat → l' ≠ l +ₗ i) →
    write_local l n t ls !! l' = ls !! l').
Proof.
  revert l ls. induction n as [|n IH]; intros l ls; simpl.
  { split; intros ??; [lia|done]. }
  destruct (IH (l +ₗ 1) ls) as [IH1 IH2].
  split.
  - intros i Lt. destruct i as [|i].
    + rewrite shift_loc_0_nat lookup_insert //.
    + have Eql: l +ₗ S i = (l +ₗ 1) +ₗ i.
      { rewrite shift_loc_assoc. f_equal. lia. }
      rewrite lookup_insert_ne.
      * rewrite Eql. destruct (IH (l +ₗ 1) ls) as [IH' _].
        apply IH'; lia.
      * rewrite -{1}(shift_loc_0_nat l). intros ?%shift_loc_inj. lia.
  - intros l' Lt. rewrite lookup_insert_ne.
    + apply IH2. intros i Lt'.
      rewrite (_: (l +ₗ 1) +ₗ i = l +ₗ S i); last first.
      { rewrite shift_loc_assoc. f_equal. lia. }
      apply Lt. lia.
    + specialize (Lt O ltac:(lia)). by rewrite shift_loc_0_nat in Lt.
Qed.

Lemma write_local_lookup_case l n t ls :
  ∀ l' t', write_local l n t ls !! l' = Some t' →
  ls !! l' = Some t' ∧ (∀ i : nat, (i < n)%nat → l' ≠ l +ₗ i) ∨
  ∃ i, (0 ≤ i < n) ∧ l' = l +ₗ i.
Proof.
  destruct (write_local_lookup l n t ls) as [EQ1 EQ2].
  intros l1 t1s1 Eq'.
  case (decide (l1.1 = l.1)) => [Eql|NEql];
    [case (decide (l.2 ≤ l1.2 < l.2 + n)) => [[Le Lt]|NIN]|].
  - have Eql2: l1 = l +ₗ Z.of_nat (Z.to_nat (l1.2 - l.2)). {
      destruct l, l1. move : Eql Le => /= -> ?.
      rewrite /shift_loc /= Z2Nat.id; [|lia]. f_equal. lia. }
    right. rewrite Eql2. eexists; split; [|done].
    rewrite Eql2 /= in Lt. lia.
  - left.
    have ?: ∀ i : nat, (i < n)%nat → l1 ≠ l +ₗ i.
    { intros i Lt Eq3. apply NIN. rewrite Eq3 /=. lia. }
     rewrite EQ2 // in Eq'.
  - left.
    have ?: ∀ i : nat, (i < n)%nat → l1 ≠ l +ₗ i.
    { intros i Lt Eq3. apply NEql. by rewrite Eq3. }
    rewrite EQ2 // in Eq'.
Qed.

Lemma res_mapsto_llookup l v t :
  (∀ (i: nat), (i < length v)%nat →
    (res_mapsto l v t).(rlm) !! (l +ₗ i) = Some $ to_tagR t) ∧
  (∀ (l': loc), (∀ (i: nat), (i < length v)%nat → l' ≠ l +ₗ i) →
    (res_mapsto l v t).(rlm) !! l' = None).
Proof.
  destruct (write_local_lookup l (length v) t ∅) as [EQ1 EQ2]. split.
  - intros i Lti. by rewrite /= right_id lookup_fmap (EQ1 _ Lti).
  - intros l' NEQ. by rewrite /= right_id lookup_fmap (EQ2 _ NEQ).
Qed.

Lemma res_mapsto_llookup_case l v t :
  ∀ l' t', ((res_mapsto l v t).(rlm) !! l' : optionR tagR) ≡ Some t' →
  t' = to_tagR t ∧ ∃ i, (0 ≤ i < length v) ∧ l' = l +ₗ i.
Proof.
  intros l' t' Eq'. apply leibniz_equiv_iff in Eq'.
  move : Eq'. rewrite /= right_id lookup_fmap.
  destruct (write_local l (length v) t ∅ !! l')
    as [t1|] eqn:Eql'; rewrite Eql'; [|done].
  simpl. intros. simplify_eq.
  destruct (write_local_lookup_case _ _ _ _ _ _ Eql') as [[]|Eq']; [done|].
  destruct Eq' as [i [[? Lti] Eqi]].
  have Lti': (Z.to_nat i < length v)%nat by rewrite Nat2Z.inj_lt Z2Nat.id.
  destruct (write_local_lookup l (length v) t ∅) as [EQ _].
  specialize (EQ _ Lti'). rewrite Z2Nat.id // -Eqi Eql' in EQ. simplify_eq.
  naive_solver.
Qed.

Lemma res_loc_lookup_1 l n t (LEN: (0 < n)%nat) :
  ((res_loc l n t).(rlm) !! l : optionR tagR) ≡ Some (to_tagR t).
Proof. rewrite /= lookup_fmap. destruct n; [lia|]. rewrite /= lookup_insert //. Qed.

Lemma res_mapsto_llookup_1 l v t (LEN: (0 < length v)%nat) :
  ((res_mapsto l v t).(rlm) !! l : optionR tagR) ≡ Some (to_tagR t).
Proof. rewrite lookup_op res_loc_lookup_1 //. Qed.

Lemma res_mapsto_tlookup l v (t: ptr_id) :
  (res_mapsto l v t).(rtm) !! t ≡
    Some (to_tagKindR tkUnique, to_agree <$> (write_mem l v ∅)).
Proof. by rewrite lookup_op /= lookup_empty left_id lookup_insert. Qed.

Lemma res_mapsto_tlookup_ne l v (t t': ptr_id) (NEQ: t' ≠ t) :
  (res_mapsto l v t).(rtm) !! t' ≡ None.
Proof. by rewrite lookup_op /= lookup_empty left_id lookup_insert_ne. Qed.

Lemma write_local_plus1 l n t :
  write_local (l +ₗ 1) n t ∅ !! l = None.
Proof.
  destruct (write_local_lookup (l +ₗ 1) n t ∅) as [_ EQ].
  rewrite EQ //. intros ??. rewrite shift_loc_assoc -{1}(shift_loc_0 l).
  intros ?%shift_loc_inj. lia.
Qed.

Lemma write_local_res_S l n t :
  (to_tagR <$> write_local l (S n) t ∅ : lmapUR) ≡
  ({[l := to_tagR t]} ⋅ (to_tagR <$> write_local (l +ₗ 1) n t ∅) : lmapUR).
Proof.
  rewrite /= fmap_insert /= insert_singleton_op //.
  rewrite lookup_fmap write_local_plus1 //.
Qed.

Lemma write_local_mem_dom l n t :
  dom (gset loc) (write_local l n t ∅) ≡ dom (gset loc) (init_mem l n ∅).
Proof.
  revert l. induction n as [|n IH]; simpl; intros l; [done|].
  rewrite /= 2!dom_insert IH //.
Qed.

(** allocating locals *)
Lemma write_local_res_alloc_local_update lsf l n t:
  (∀ i, (i < n)%nat → lsf !! (l +ₗ i) = None) →
  (lsf, ε) ~l~>
  (lsf ⋅ (to_tagR <$> write_local l n t ∅) : lmapUR, to_tagR <$> write_local l n t ∅ : lmapUR).
Proof.
  revert l lsf.
  induction n as [|n IH]; intros l lsf HL.
  - rewrite /= fmap_empty right_id //.
  - rewrite /= write_local_res_S.
    rewrite (cmra_comm ({[l := to_tagR t]} : lmapUR) (to_tagR <$> write_local _ _ _ _)).
    rewrite cmra_assoc.
    etrans.
    + apply (IH (l +ₗ 1)).
      intros i Lt. rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
      apply HL. lia.
    + have NEQ1: write_local (l +ₗ 1) n t ∅ !! l = None.
      { rewrite {1}/write_local write_local_plus1 //. }
      have ?: (lsf ⋅ (to_tagR <$> write_local (l +ₗ 1) n t ∅)) !! l = None.
      { rewrite lookup_op lookup_fmap NEQ1 right_id_L.
        specialize (HL O). rewrite shift_loc_0_nat in HL. apply HL. lia. }
      rewrite 2!(cmra_comm _  {[l := _]})
              -insert_singleton_op // -insert_singleton_op;
        [|by rewrite lookup_fmap NEQ1].
      by apply alloc_local_update.
Qed.

Lemma res_mapsto_local_alloc_local_update lsf l v t:
  lsf.(rtm) !! t = None →
  (∀ i, (i < length v)%nat → lsf.(rlm) !! (l +ₗ i) = None) →
  (lsf, ε) ~l~> (lsf ⋅ res_mapsto l v t, res_mapsto l v t).
Proof.
  intros FRESH1 FRESH2. destruct lsf as [[tm cm] lm].
  rewrite /res_mapsto (cmra_comm (res_loc _ _ _)).
  etrans. by apply (res_tag_alloc_local_update _ t tkUnique (write_mem l v ∅)).
  rewrite !pair_op !right_id left_id /=. apply prod_local_update_2.
  by apply write_local_res_alloc_local_update.
Qed.

(** deallocating locals *)
Lemma write_local_res_dealloc_local_update (lsf: lmapUR) l n t:
  (∀ i, (i < n)%nat → lsf !! (l +ₗ i) = None) →
  (lsf ⋅ (to_tagR <$> write_local l n t ∅) : lmapUR, (to_tagR <$> write_local l n t ∅) : lmapUR) ~l~>
  (lsf : lmapUR, ε : lmapUR).
Proof.
  revert l lsf.
  induction n as [|n IH]; intros l lsf HL.
  - rewrite /= fmap_empty right_id_L //.
  - rewrite /= write_local_res_S.
    rewrite (cmra_comm ({[l := to_tagR t]} : lmapUR) (to_tagR <$> write_local _ _ _ _)).
    rewrite cmra_assoc.
    have NEQ1: write_local (l +ₗ 1) n t ∅ !! l = None.
    { rewrite {1}/write_local write_local_plus1 //. }
    have ?: (lsf ⋅ (to_tagR <$> write_local (l +ₗ 1) n t ∅)) !! l = None.
    { rewrite lookup_op lookup_fmap NEQ1 right_id_L.
      specialize (HL O). rewrite shift_loc_0_nat in HL. apply HL. lia. }
    etrans.
    + rewrite 2!(cmra_comm _  {[l := _]}) -insert_singleton_op; [|done].
      rewrite -insert_singleton_op; [|by rewrite lookup_fmap NEQ1].
      eapply (delete_local_update_cancelable _ _ l); [|by rewrite lookup_insert..].
      apply _.
    + rewrite 2!delete_insert_delete delete_notin // delete_notin;
        [|by rewrite lookup_fmap NEQ1].
      apply (IH (l +ₗ 1)).
      intros i Lt. rewrite shift_loc_assoc -(Nat2Z.inj_add 1).
      apply HL. lia.
Qed.

Lemma res_mapsto_res_tag_public (r: resUR) l v t
  (NONE1: ∀ i, (i < length v)%nat → r.(rlm) !! (l +ₗ i) = None)
  (NONE2: r.(rtm) !! t = None):
  (r ⋅ res_mapsto l v t, res_mapsto l v t) ~l~>
  (r ⋅ res_tag t tkPub ∅, res_tag t tkPub ∅).
Proof.
  rewrite /res_mapsto. destruct r as [[tm cm] lm].
  rewrite (cmra_comm (res_loc _ _ _)) cmra_assoc. etrans.
  - apply prod_local_update_2. rewrite /= right_id left_id.
    by apply write_local_res_dealloc_local_update.
  - rewrite !pair_op /= !right_id.
    apply prod_local_update_1, prod_local_update_1. rewrite /=.
    do 2 rewrite (cmra_comm tm) -insert_singleton_op //.
    rewrite -(insert_insert tm t (Cinr (), to_agree <$> ∅)
                                 (Cinl (Excl ()), to_agree <$> (write_mem l v ∅))).
    eapply (singleton_local_update (<[t := _]> tm : tmapUR)).
    by rewrite lookup_insert.
    apply exclusive_local_update. split; [done|apply to_heapR_valid].
Qed.

(** updating locals *)
Lemma res_mapsto_1_insert_local_update (r: resUR) (l: loc) s1 s2 (t: ptr_id)
  (NONE1: r.(rlm) !! l = None) (NONE2: r.(rtm) !! t = None):
  (r ⋅ res_mapsto l [s1] t, res_mapsto l [s1] t) ~l~>
  (r ⋅ res_mapsto l [s2] t, res_mapsto l [s2] t).
Proof.
  intros. rewrite /res_mapsto cmra_assoc. etrans.
  - eapply res_tag_1_insert_local_update_r.
    by rewrite lookup_op NONE2 /= lookup_empty right_id_L.
  - rewrite -(cmra_assoc r) 2!(cmra_comm (res_loc _ _ _)) 2!cmra_assoc.
    rewrite /= insert_empty //.
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
