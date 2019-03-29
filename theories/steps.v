From stbor Require Import lang notation.

Class Wellformed A := Wf : A → Prop.
Existing Class Wf.

Record state_wf' σ := {
  state_wf_dom : dom (gset loc) σ.(cheap) ≡ dom (gset loc) σ.(cstk);
  state_wf_mem_bor:
    ∀ l l' bor, σ.(cheap) !! l = Some (LitV (LitLoc l' bor)) →
      match bor with
      | UniqB t | AliasB (Some t) => (t < σ.(cclk))%nat
      | _ => True
      end;
  state_wf_stack_frozen:
    ∀ l stack, σ.(cstk) !! l = Some stack →
      match stack.(frozen_since) with Some t => (t < σ.(cclk))%nat | _ => True end;
  state_wf_stack_item:
    ∀ l stack si, σ.(cstk) !! l = Some stack → si ∈ stack.(borrows) →
      match si with
      | Uniq t => (t < σ.(cclk))%nat
      | FnBarrier c => is_Some (σ.(cbar) !! c)
      | _ => True
      end;
}.

Instance state_wf : Wellformed state :=  state_wf'.

(** Steps preserve wellformedness *)

Lemma init_mem_foldr' l n h (m: nat):
  init_mem (l +ₗ m) n h =
  fold_right (λ (i: nat) hi, <[(l +ₗ i):=LitV ☠%V]> hi) h (seq m n).
Proof.
  revert l h m. induction n as [|n IHn]; intros l h m; [done|]. simpl. f_equal.
  by rewrite shift_loc_assoc -(Nat2Z.inj_add m 1) Nat.add_1_r IHn.
Qed.
Lemma init_mem_foldr l n h:
  init_mem l n h =
  fold_right (λ (i: nat) hi, <[(l +ₗ i):=LitV ☠%V]> hi) h (seq 0 n).
Proof. by rewrite -init_mem_foldr' shift_loc_0. Qed.

Lemma free_mem_foldr' l n h (m: nat):
  free_mem (l +ₗ m) n h =
  fold_right (λ (i: nat) hi, delete (l +ₗ i) hi) h (seq m n).
Proof.
  revert l h m. induction n as [|n IHn]; intros l h m; [done|]. simpl. f_equal.
  by rewrite shift_loc_assoc -(Nat2Z.inj_add m 1) Nat.add_1_r IHn.
Qed.
Lemma free_mem_foldr l n h:
  free_mem l n h =
  fold_right (λ (i: nat) hi, delete (l +ₗ i) hi) h (seq 0 n).
Proof. by rewrite -free_mem_foldr' shift_loc_0. Qed.

Lemma init_stacks_foldr' l n h si (m: nat):
  init_stacks (l +ₗ m) n h si =
  fold_right (λ (i: nat) hi, <[(l +ₗ i):=mkBorStack [si] None]> hi) h (seq m n).
Proof.
  revert l h m. induction n as [|n IHn]; intros l h m; [done|]. simpl. f_equal.
  by rewrite shift_loc_assoc -(Nat2Z.inj_add m 1) Nat.add_1_r IHn.
Qed.
Lemma init_stacks_foldr l n h si:
  init_stacks l n h si =
  fold_right (λ (i: nat) hi, <[(l +ₗ i):=mkBorStack [si] None]> hi) h (seq 0 n).
Proof. by rewrite -init_stacks_foldr' shift_loc_0. Qed.

Lemma foldr_gmap_insert_dom `{Countable K} {A B C: Type}
  (ma: gmap K A) (mb: gmap K B) (a: A) (b: B) (cs: list C) (f: C → K):
  dom (gset K) ma ≡ dom (gset K) mb →
  dom (gset K) (foldr (λ (c: C) ma, <[f c := a]> ma) ma cs)
  ≡ dom (gset K) (foldr (λ (c: C) mb, <[f c := b]> mb) mb cs).
Proof.
  intros. induction cs; simpl; [done|].
  by rewrite 2!dom_insert IHcs.
Qed.

Lemma foldr_gmap_insert_lookup `{Countable K} {A C: Type}
  (ma: gmap K A) (a ka: A) (cs: list C) (f: C → K) (k: K):
  (foldr (λ (c: C) ma, <[f c := a]> ma) ma cs) !! k = Some ka →
  ka = a ∨ ma !! k = Some ka.
Proof.
  induction cs as [|a' ? IHm]; simpl; [naive_solver|].
  case (decide (f a' = k)) => [->|?].
  - rewrite lookup_insert. naive_solver.
  - by rewrite lookup_insert_ne.
Qed.

Lemma foldr_gmap_insert_lookup_neq `{Countable K} {A C: Type}
  (ma: gmap K A) (a ka: A) (cs: list C) (f: C → K) (k: K) (NEq: ka ≠ a):
  (foldr (λ (c: C) ma, <[f c := a]> ma) ma cs) !! k = Some ka →
  ma !! k = Some ka.
Proof.
  intros Eq. by destruct (foldr_gmap_insert_lookup _ _ _ _ _ _ Eq).
Qed.

(** Alloc *)
Lemma alloc_step_wf σ σ' e e' efs h0 l bor T:
  base_step e σ.(cheap) (Some $ AllocEvt l bor T) e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ AllocEvt l bor T)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h stk bar clk].
  destruct σ' as [h' stk' bar' clk']. simpl.
  intros BS IS WF. inversion BS. clear BS. simplify_eq.
  destruct (tsize T) eqn:Eqs.
  - inversion IS; clear IS; simplify_eq; constructor; simpl.
    + rewrite Eqs /=. apply WF.
    + move => ?? bor /(state_wf_mem_bor _ WF).
      destruct bor as [|[]]; simpl; lia.
    + rewrite Eqs /=.
      move => ? stack /(state_wf_stack_frozen _ WF).
      destruct (stack.(frozen_since)); simpl; lia.
    + rewrite Eqs /=.
      move => ?? si Eq In. move : (state_wf_stack_item _ WF _ _ _ Eq In).
      destruct si; [simpl; lia|done..].
  - inversion IS; clear IS; simplify_eq; constructor; cbn -[ init_mem].
    + rewrite Eqs init_stacks_foldr init_mem_foldr. apply foldr_gmap_insert_dom, WF.
    + intros l1 l2 bor. rewrite init_mem_foldr.
      intros [|Eq]%foldr_gmap_insert_lookup; [done|].
      move : (state_wf_mem_bor _ WF _ _ _ Eq).
      destruct bor as [|[]]; simpl; lia.
    + intros l1 stack. rewrite init_stacks_foldr.
      intros [->|Eq]%foldr_gmap_insert_lookup; [done|].
      move : (state_wf_stack_frozen _ WF _ _ Eq).
      destruct stack.(frozen_since); simpl; lia.
    + intros l1 stack si. rewrite init_stacks_foldr.
      intros [->|Eq]%foldr_gmap_insert_lookup.
      * intros ->%elem_of_list_singleton. lia.
      * move => /(state_wf_stack_item _ WF _ _ _ Eq).
        destruct si; [simpl; lia|done..].
Qed.

Lemma foldr_gmap_delete_lookup `{Countable K} {A C: Type}
  (ma: gmap K A) (ka: A) (cs: list C) (f: C → K) (k: K):
  (foldr (λ (c: C) ma, delete (f c) ma) ma cs) !! k = Some ka →
  ma !! k = Some ka.
Proof.
  induction cs as [|a' ? IHm]; simpl; [naive_solver|].
  case (decide (f a' = k)) => [->|?].
  - by rewrite lookup_delete.
  - by rewrite lookup_delete_ne.
Qed.

Lemma accessN_dealloc_delete' α β l bor n α' (m: nat):
  accessN α β (l +ₗ m) bor n AccessDealloc = Some α' →
  α' = fold_right (λ (i: nat) α, delete (l +ₗ i) α) α (seq m n).
Proof.
  revert α.
  induction n as [|n IHn]; intros α; [by move => [->]|]. simpl.
  case lookup => stack /= ; [|done]. case access1 => stack'; [|done].
  move => /IHn ->. clear. revert α m. induction n as [|n IH]; intros α m.
  - by rewrite /= shift_loc_0.
  - simpl. f_equal.
    by rewrite shift_loc_assoc -Nat2Z.inj_add -Nat.add_succ_comm Nat2Z.inj_add
               -shift_loc_assoc IH.
Qed.
Lemma accessN_dealloc_delete α β l bor n α':
  accessN α β l bor n AccessDealloc = Some α' →
  α' = fold_right (λ (i: nat) α, delete (l +ₗ i) α) α (seq O n).
Proof. intros. eapply accessN_dealloc_delete'. by rewrite shift_loc_0. Qed.

Lemma foldr_gmap_delete_dom `{Countable K} {A B C: Type}
  (ma: gmap K A) (mb: gmap K B) (cs: list C) (f: C → K):
  dom (gset K) ma ≡ dom (gset K) mb →
  dom (gset K) (foldr (λ (c: C) ma, delete (f c) ma) ma cs)
  ≡ dom (gset K) (foldr (λ (c: C) mb, delete (f c) mb) mb cs).
Proof.
  intros. induction cs; simpl; [done|].
  by rewrite 2!dom_delete IHcs.
Qed.

(** Dealloc *)
Lemma dealloc_step_wf σ σ' e e' efs h0 l bor T :
  base_step e σ.(cheap) (Some $ DeallocEvt l bor T) e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ DeallocEvt l bor T)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h stk bar clk]. destruct σ' as [h' stk' bar' clk']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  rewrite (accessN_dealloc_delete stk bar' l bor (tsize T) stk'); [|done].
  constructor; simpl.
  - rewrite free_mem_foldr. apply foldr_gmap_delete_dom, WF.
  - intros ???. rewrite free_mem_foldr.
    intros Eq%foldr_gmap_delete_lookup.
    apply (state_wf_mem_bor _ WF _ _ _ Eq).
  - intros ?? Eq%foldr_gmap_delete_lookup.
    apply (state_wf_stack_frozen _ WF _ _ Eq).
  - intros ??? Eq%foldr_gmap_delete_lookup.
    apply (state_wf_stack_item _ WF _ _ _ Eq).
Qed.

(** Copy *)

Lemma dom_map_insert_is_Some `{FinMapDom K M D} {A} (m : M A) i x :
  is_Some (m !! i) → dom D (<[i:=x]>m) ≡ dom D m.
Proof.
  intros IS. rewrite dom_insert. apply (anti_symm (⊆)).
  - apply union_least; [|done]. by apply elem_of_subseteq_singleton, elem_of_dom.
  - by apply union_subseteq_r.
Qed.

Lemma accessN_normal_dom α β l bor n kind α' (ND: kind ≠ AccessDealloc) :
  accessN α β l bor n kind = Some α' →
  dom (gset loc) α ≡ dom (gset loc) α'.
Proof.
  revert α α'. induction n as [|n IH]; intros α α'; [by move => /= [-> //]|].
  simpl. destruct (α !! (l +ₗ n)) eqn:Eq; [|done].
  simpl. case access1 => stack' /=; [|done]. intros Eq2.
  have Eq3: dom (gset loc) α' ≡ dom (gset loc) (<[l +ₗ n:=stack']> α).
  { destruct kind; [..|done]; move : Eq2 => /IH <- //. } clear Eq2.
  rewrite Eq3. symmetry. apply dom_map_insert_is_Some. by eexists.
Qed.

Lemma copy_step_wf σ σ' e e' efs h0 l bor T :
  base_step e σ.(cheap) (Some $ CopyEvt l bor T) e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ CopyEvt l bor T)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h stk bar clk]. destruct σ' as [h' stk' bar' clk']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl.
  - rewrite -(accessN_normal_dom stk bar' l bor (tsize T) AccessRead);
      [by apply WF|done..].
  - apply WF.
  - admit. (* stk' sub of stk *)
  - admit. (* stk' sub of stk *)
Abort.

(** Write *)

Lemma write_mem_dom l vl h
  (DEFINED: ∀ i : nat, (i < strings.length vl)%nat → is_Some (h !! (l +ₗ i))) :
  dom (gset loc) (write_mem l vl h) ≡ dom (gset loc) h.
Proof.
  revert l h DEFINED. induction vl as [|v vl IH]; intros l h DEFINED; [done|].
  rewrite /= IH.
  - apply dom_map_insert_is_Some. rewrite -(shift_loc_0_nat l).
    apply DEFINED. simpl. lia.
  - intros i Lt. rewrite lookup_insert_is_Some'. right.
    rewrite (shift_loc_assoc_nat l 1). apply DEFINED. simpl. lia.
Qed.

Lemma write_step_wf σ σ' e e' efs h0 l bor T :
  base_step e σ.(cheap) (Some $ WriteEvt l bor T) e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ WriteEvt l bor T)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h stk bar clk]. destruct σ' as [h' stk' bar' clk']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl.
  - rewrite -(accessN_normal_dom stk bar' l bor (tsize T) AccessWrite);
      [|done..].
    rewrite write_mem_dom; [by apply WF|done].
  - admit. (* only true if whatever in el is bound in the memory *)
  - admit. (* stk' sub of stk *)
  - admit. (* stk' sub of stk *)
Abort.

(** Deref *)
Lemma deref_step_wf σ σ' e e' efs h0 l bor T mut :
  base_step e σ.(cheap) (Some $ DerefEvt l bor T mut) e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ DerefEvt l bor T mut)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h stk bar clk]. destruct σ' as [h' stk' bar' clk']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl; apply WF.
Qed.

(** NewCall *)
Lemma newcall_step_wf σ σ' e e' efs h0 n :
  base_step e σ.(cheap) (Some $ NewCallEvt n) e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ NewCallEvt n)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h stk bar clk]. destruct σ' as [h' stk' bar' clk']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl; [apply WF..|].
  intros ??? Eq In. have SI := state_wf_stack_item _ WF _ _ _ Eq In.
  destruct si; [done..|]. rewrite lookup_insert_is_Some'. by right.
Qed.

(** EndCall *)
Lemma endcall_step_wf σ σ' e e' efs h0 n :
  base_step e σ.(cheap) (Some $ EndCallEvt n) e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ EndCallEvt n)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h stk bar clk]. destruct σ' as [h' stk' bar' clk']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl; [apply WF..|].
  intros ??? Eq In. have SI := state_wf_stack_item _ WF _ _ _ Eq In.
  destruct si; [done..|]. rewrite lookup_insert_is_Some'. by right.
Qed.


(** Retag *)
Lemma retag_step_wf σ σ' e e' efs h0 l T kind :
  base_step e σ.(cheap) (Some $ RetagEvt l T kind) e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ RetagEvt l T kind)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h stk bar clk]. destruct σ' as [h' stk' bar' clk']. simpl.
  intros BS IS WF.
  inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq.
  constructor; simpl.
  - admit. (* no change in dom of h' stk' *)
  - admit. (* new bor comes from increasing clk *)
  - admit. (* new bor comes from increasing clk *)
  - admit. (* barrier must be in memory *)
Abort.

(** None event step *)
Lemma None_step_wf σ σ' e e' efs h0 :
  base_step e σ.(cheap) None e' h0 efs →
  instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk)
                    None
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h stk bar clk]. destruct σ' as [h' stk' bar' clk']. simpl.
  intros BS IS WF.
  inversion BS; clear BS; simplify_eq;
  inversion IS; clear IS; simplify_eq; apply WF.
Qed.

Lemma head_step_wf σ σ' e e' efs :
  head_step e σ [] e' σ' efs → Wf σ → Wf σ'.
Proof.
  intros HS WF. inversion HS. simplify_eq. destruct oevent as [[]|].
  - eapply alloc_step_wf; eauto.
  - eapply dealloc_step_wf; eauto.
  - admit.
  - admit.
  - eapply deref_step_wf; eauto.
  - eapply newcall_step_wf; eauto.
  - eapply endcall_step_wf; eauto.
  - admit.
  - eapply None_step_wf; eauto.
Abort.
