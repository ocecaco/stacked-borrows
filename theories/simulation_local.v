From Paco Require Import paco.

From stbor Require Import cmra simulation_local_base.

(** Public scalar relation *)
(* No case for poison *)
Definition arel (r: resUR) (s1 s2: scalar) : Prop :=
  match s1, s2 with
  | ScInt n1, ScInt n2 => n1 = n2
  | ScFnPtr n1, ScFnPtr n2 => n1 = n2
  | ScPtr l1 tg1, ScPtr l2 tg2 =>
      l1 = l2 ∧ tg1 = tg2 ∧
      match tg1 with
      | Untagged => True
      | Tagged t => ∃ h, r.1 !! t ≡ Some (to_tagKindR tkPub, h)
      end
  | _, _ => False
  end.

Fixpoint active_SRO (stk: stack) : gset ptr_id :=
  match stk with
  | [] => ∅
  | it :: stk =>
    match it.(perm) with
    | SharedReadOnly => match it.(tg) with
                        | Tagged t => {[t]} ∪ active_SRO stk
                        | Untagged => active_SRO stk
                        end
    | _ => ∅
    end
  end.

Definition ptrmap_inv (r: resUR) (σ: state) : Prop :=
  ∀ (t: ptr_id) (k: tag_kind) h, r.1 !! t ≡ Some (to_tagKindR k, h) →
  ∀ (l: loc) (s: scalar), h !! l ≡ Some (to_agree s) →
  ∀ (stk: stack), σ.(sst) !! l = Some stk →
  ∀ pm opro, mkItem pm (Tagged t) opro ∈ stk →
  (* as long as the tag [t] is in the stack [stk],
    then its heaplet [h] agree with the state [σ] *)
  σ.(shp) !! l = Some s ∧
  (* If [k] is Unique, then [t] must be Unique at the top of [stk]. Otherwise
    if [k] is Pub, then [t] can be among the top SRO items. *)
  match k with
  | tkUnique => ∃ stk' opro', stk = mkItem Unique (Tagged t) opro' :: stk'
  | tkPub => t ∈ active_SRO stk
  end.

Definition cmap_inv (r: resUR) (σ: state) : Prop :=
  ∀ (c: call_id) (cs: callStateR), r.2 !! c ≡ Some cs →
  match cs with
  (* if c is a private call id *)
  | Cinl (Excl T) =>
      c ∈ σ.(scs) ∧
      (* for any tag [t] owned by c *)
      ∀ (t: ptr_id), t ∈ T →
      (* that protects the heaplet [h] *)
      ∀ k h, r.1 !! t ≡ Some (k, h) →
      (* if [l] is in that heaplet [h] *)
      ∀ (l: loc), l ∈ dom (gset loc) h →
      (* then a c-protector must be in the stack of l *)
      ∃ stk pm, σ.(sst) !! l = Some stk ∧ mkItem pm (Tagged t) (Some c) ∈ stk
  (* if c is a public call id *)
  | Cinr _ => True
  | _ => False
  end.

(* [l] is private w.r.t to some tag [t] if [t] is uniquely owned and protected
  by some call id [c] and [l] is in [t]'s heaplet [h]. *)
Definition priv_loc (r: resUR) (l: loc) (t: ptr_id) :=
  ∃ (c: call_id) (T: gset ptr_id) h,
  r.2 !! c ≡ Some (Cinl (Excl T)) ∧ t ∈ T ∧
  r.1 !! t ≡ Some (to_tagKindR tkUnique, h) ∧ l ∈ dom (gset loc) h.

(** State relation *)
Definition srel (r: resUR) (σs σt: state) : Prop :=
  σs.(sst) = σt.(sst) ∧ σs.(snp) = σt.(snp) ∧
  σs.(scs) = σt.(scs) ∧ σs.(snc) = σt.(snc) ∧
  ∀ (l: loc) st, σt.(shp) !! l = Some st →
  (∃ ss, σs.(shp) !! l = Some ss ∧ arel r ss st) ∨ (∃ (t: ptr_id), priv_loc r l t).

Definition wsat (r: resUR) (σs σt: state) : Prop :=
  ptrmap_inv r σt ∧ cmap_inv r σt ∧ srel r σs σt.

(** Value relation for function arguments/return values *)
(* Values passed among functions are public *)
Definition vrel (r: resUR) (v1 v2: value) := Forall2 (arel r) v1 v2.
Definition vrel_expr (r: resUR) (e1 e2: expr) :=
  ∃ v1 v2, e1 = Val v1 ∧ e2 = Val v2 ∧ vrel r v1 v2.

(* TODO: I hate these cmra operations *)
Lemma ptrmap_inv_downward_mono (r1 r2 : resUR) σ (VAL: ✓ r2) :
  r1 ≼ r2 → ptrmap_inv r2 σ → ptrmap_inv r1 σ.
Proof.
  move => Le PI t k h Eqh l s Eqs stk Eqst pm opro IN.
  have HL1: Some (to_tagKindR k, h) ≼ r2.1 !! t.
  { rewrite -Eqh. by apply lookup_included, prod_included, Le. }
  apply option_included in HL1 as [?|[? [[k' h'] [? [Eq1 INCL]]]]]; [done|].
  simplify_eq.
  have VL2: ✓ (k', h').
  { apply (lookup_valid_Some _ t (k', h') (proj1 VAL)). by rewrite Eq1. }
  assert (r2.1 !! t ≡ Some (to_tagKindR k, h') ∧ h ≼ h') as [Eq2 LE2].
  { rewrite Eq1. move : INCL => [[/= EQ1 EQ2]|LE].
    - by rewrite EQ1 EQ2.
    - apply prod_included in LE as [Eq%tag_kind_incl_eq ?]; [|apply VL2].
      simpl in Eq. by rewrite Eq. }
  have EQL: h' !! l ≡ Some (to_agree s).
  { move : LE2 => /lookup_included /(_ l). rewrite Eqs.
    move => /option_included [//|[x [s' [? [EqL EqR]]]]]. simplify_eq.
    rewrite EqL. move : EqR => [<-//|].
    destruct (to_agree_uninj s') as [ss Eqss].
    - apply (lookup_valid_Some h' l). apply VL2. by rewrite EqL.
    - by rewrite -Eqss to_agree_included => ->. }
  specialize (PI _ _ _ Eq2 _ _ EQL _ Eqst _ _ IN). naive_solver.
Qed.

Lemma cmap_inv_downward_mono (r1 r2 : resUR) σ (VAL: ✓ r2) :
  r1 ≼ r2 → cmap_inv r2 σ → cmap_inv r1 σ.
Proof.
  move => Le CI c cs Eqcs.
  have HL1: Some cs ≼ r2.2 !! c.
  { rewrite -Eqcs. by apply lookup_included, prod_included, Le. }
  apply option_included in HL1 as [?|[cs1 [cs2 [? [Eq1 INCL]]]]]; [done|].
  simplify_eq.
  specialize (CI c cs2 (ltac: (by rewrite Eq1))).
  have VL2: ✓ cs2.
  { eapply (lookup_valid_Some r2.2 c). apply VAL. by rewrite Eq1. }
  have VL1: ✓ cs1. { move : INCL => [-> //|]. by apply cmra_valid_included. }
  destruct cs1 as [[T|]| |]; [|done..].
  destruct INCL as [INCL|INCL]; last first.
  { exfalso. apply (exclusive_included _ _ INCL VL2). }
  destruct cs2 as [[T2|]| |]; [|done|by inversion INCL|done].
  apply Cinl_inj, Excl_inj, leibniz_equiv_iff in INCL. subst T2.
  destruct CI as [IN EQM]. split; [done|].
  intros t INt k h Eqh l InD.
  have HL1: Some (k, h) ≼ r2.1 !! t.
  { rewrite -Eqh. by apply lookup_included, prod_included, Le. }
  apply option_included in HL1 as [?|[? [[k' h'] [? [Eq2 INCL]]]]]; [done|].
  simplify_eq.
  have VL3: ✓ (k', h').
  { apply (lookup_valid_Some _ t (k', h') (proj1 VAL)). by rewrite Eq2. }
  assert (r2.1 !! t ≡ Some (k, h') ∧ h ≼ h') as [Eq3 LE2].
  { rewrite Eq2. move : INCL => [[/= EQ1 EQ2]|LE].
    - by rewrite EQ1 EQ2.
    - apply prod_included in LE as [Eq%tag_kind_incl_eq ?]; [|apply VL3].
      simpl in Eq. by rewrite Eq. }
  apply (EQM _ INt k h' Eq3 l). eapply dom_included; eauto.
Qed.

Lemma priv_loc_downward_mono (r1 r2 : resUR) l t (VAL: ✓ r2) :
  r1 ≼ r2 → priv_loc r2 l t → priv_loc r1 l t.
Proof.
  intros Le (c & T & h & EqT & INt & Eqh & INl).
  have HL2: r1.2 !! c ≼ Some (Cinl (Excl T)).
  { rewrite -EqT. apply (lookup_included r1.2 r2.2), prod_included, Le. }

Abort.

Lemma srel_downward_mono (r1 r2 : resUR) σs σt (VAL: ✓ r2) :
  r1 ≼ r2 → srel r2 σs σt → srel r1 σs σt.
Proof.
  intros LE (? & ? & ? & ? & HL). repeat split; [done..|].
  intros l st Eqst.
  destruct (HL l st Eqst) as [[ss [Eqss AREL]]|[t PL]].
Abort.

Lemma wsat_downward_mono (r1 r2 : resUR) (VAL: ✓ r2) :
  r1 ≼ r2 → wsat r2 <2= wsat r1.
Proof.
  move => Le σs σt [PI [CI SREL]]. split; last split.
  - eapply ptrmap_inv_downward_mono; eauto.
  - eapply cmap_inv_downward_mono; eauto.
  -
Abort.
