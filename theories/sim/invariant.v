From stbor.lang Require Export defs.
From stbor.sim Require Export cmra.

Set Default Proof Using "Type".

(* TODO: define viewshift *)

(** Public scalar relation *)
(* No case for poison *)
Definition arel (r: resUR) (s1 s2: scalar) : Prop :=
  match s1, s2 with
  | ScPoison, ScPoison => True
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

Definition ptrmap_inv (r: resUR) (σ: state) : Prop :=
  ∀ (t: ptr_id) (k: tag_kind) h, r.1 !! t ≡ Some (to_tagKindR k, h) →
  (t < σ.(snp))%nat ∧
  (∀ (l: loc) (s: scalar), h !! l ≡ Some (to_agree s) →
  ∀ (stk: stack), σ.(sst) !! l = Some stk →
  ∀ pm opro, mkItem pm (Tagged t) opro ∈ stk → pm ≠ Disabled →
  (* as long as the tag [t] is in the stack [stk] (Disabled is considered not in),
    then its heaplet [h] agree with the state [σ] *)
  σ.(shp) !! l = Some s ∧
  (* If [k] is Unique, then [t] must be Unique at the top of [stk]. Otherwise
    if [k] is Pub, then [t] can be among the top SRO items. *)
  match k with
  | tkUnique => ∃ stk', stk = mkItem Unique (Tagged t) opro :: stk'
  | tkPub => t ∈ active_SRO stk
  end).

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
  | Cinr _ => (c < σ.(snc))%nat
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
  (* Wellformedness *)
  Wf σs ∧ Wf σt ∧ ✓ r ∧
  (* Invariants *)
  ptrmap_inv r σt ∧ cmap_inv r σt ∧ srel r σs σt.

(** Value relation for function arguments/return values *)
(* Values passed among functions are public *)
Definition vrel (r: resUR) (v1 v2: value) := Forall2 (arel r) v1 v2.
Definition vrel_expr (r: resUR) (e1 e2: expr) :=
  ∃ v1 v2, e1 = Val v1 ∧ e2 = Val v2 ∧ vrel r v1 v2.

Lemma arel_mono (r1 r2 : resUR) (VAL: ✓ r2) :
  r1 ≼ r2 → ∀ s1 s2, arel r1 s1 s2 → arel r2 s1 s2.
Proof.
  intros Le s1 s2. rewrite /arel.
  destruct s1 as [| |l1 t1|], s2 as [| |l2 t2|]; auto.
  intros [Eql [Eqt PV]]. subst. repeat split.
  destruct t2 as [t2|]; [|done].
  destruct PV as [h HL].
  have HL1: Some (to_tagKindR tkPub, h) ≼ r2.1 !! t2.
  { rewrite -HL. by apply lookup_included, prod_included, Le. }
  apply option_included in HL1 as [?|[th1 [[tk2 h2] [? [Eq1 INCL]]]]]; [done|].
  simplify_eq. exists h2. rewrite Eq1 (_: tk2 ≡ to_tagKindR tkPub) //.
  apply tag_kind_incl_eq; [done|].
  move : INCL => [[/=<- _//]|/prod_included [/= /csum_included Eq _]].
  - apply csum_included. naive_solver.
  - have VL2: ✓ tk2.
    { apply (pair_valid tk2 h2). rewrite -pair_valid.
      apply (lookup_valid_Some r2.1 t2); [apply VAL|]. by rewrite Eq1. }
    destruct Eq as [|[|Eq]]; [by subst|naive_solver|].
    destruct Eq as [?[ag[? [? ?]]]]. simplify_eq.
    apply to_agree_uninj in VL2 as [[] Eq]. rewrite -Eq.
    apply csum_included. naive_solver.
Qed.

Lemma vrel_mono (r1 r2 : resUR) (VAL: ✓ r2) :
  r1 ≼ r2 → ∀ v1 v2, vrel r1 v1 v2 → vrel r2 v1 v2.
Proof. intros Le v1 v2 VREL. by apply (Forall2_impl _ _ _ _ VREL), arel_mono. Qed.

Lemma vrel_expr_mono (r1 r2 : resUR) (VAL: ✓ r2) :
  r1 ≼ r2 → ∀ v1 v2, vrel_expr r1 v1 v2 → vrel_expr r2 v1 v2.
Proof.
  move => Le v1 v2 [? [? [? [? /(vrel_mono _ _ VAL Le) ?]]]]. do 2 eexists. eauto.
Qed.

Instance ptrmap_inv_proper : Proper ((≡) ==> (=) ==> iff) ptrmap_inv.
Proof.
  intros r1 r2 Eqr ? σ ?. subst. rewrite /ptrmap_inv. by setoid_rewrite Eqr.
Qed.

Instance cmap_inv_proper : Proper ((≡) ==> (=) ==> iff) cmap_inv.
Proof.
  intros r1 r2 Eqr ? σ ?. subst. rewrite /cmap_inv. setoid_rewrite Eqr.
  split; intros EQ ?? Eq; specialize (EQ _ _ Eq); destruct cs as [[]| |]; eauto;
    [by setoid_rewrite <- Eqr|by setoid_rewrite Eqr].
Qed.

Instance arel_proper : Proper ((≡) ==> (=) ==> (=) ==> iff) arel.
Proof. solve_proper. Qed.

Instance priv_loc_proper : Proper ((≡) ==> (=) ==> (=) ==> iff) priv_loc.
Proof. solve_proper. Qed.

Instance srel_proper : Proper ((≡) ==> (=) ==> (=) ==> iff) srel.
Proof.
  intros r1 r2 Eqr ??????. subst. rewrite /srel.
  split; move => [-> [-> [-> [-> PV]]]]; repeat split; intros l s Eqs;
    (destruct (PV _ _ Eqs) as [[ss ?]|[t ?]]; [left|right]; [exists ss|exists t]).
  - by rewrite -Eqr.
  - by rewrite -Eqr.
  - by rewrite Eqr.
  - by rewrite Eqr.
Qed.

Instance wsat_proper : Proper ((≡) ==> (=) ==> (=) ==> iff) wsat.
Proof. solve_proper. Qed.

Lemma cinv_lookup_in (r: resUR) (σ: state) c cs:
  Wf σ → cmap_inv r σ → r.2 !! c ≡ Some cs → (c < σ.(snc))%nat.
Proof.
  intros WF CINV EQ. specialize (CINV c cs EQ).
  destruct cs as [[]| |]; [|done..].
  destruct CINV. by apply WF.
Qed.

Lemma cinv_lookup_in_eq (r: resUR) (σ: state) c cs:
  Wf σ → cmap_inv r σ → r.2 !! c = Some cs → (c < σ.(snc))%nat.
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
Proof. intros (?&?&?&?&?&?). by eapply srel_heap_dom. Qed.
