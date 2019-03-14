From stbor Require Import lang notation.

Class Wellformed A := Wf : A →  Prop.
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

Lemma foldr_gmap_dom `{Countable K} {A B C: Type}
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

Lemma alloc_step_wf σ σ' e e' l bor T amod:
  base_step e σ.(cheap) (Some $ AllocEvt l bor T amod) e' σ'.(cheap) [] →
  instrumented_step σ.(cheap) σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ AllocEvt l bor T amod)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h stk bar clk].
  destruct σ' as [h' stk' bar' clk']. simpl.
  intros BS IS WF. inversion BS. clear BS. simplify_eq.
  destruct (tsize T) eqn:Eqs.
  - inversion IS; clear IS; simplify_eq; constructor; simpl.
    + rewrite Eqs /=. apply WF.
    + apply WF.
    + rewrite Eqs /=. apply WF.
    + rewrite Eqs /=. apply WF.
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
    + rewrite Eqs init_stacks_foldr init_mem_foldr. apply foldr_gmap_dom, WF.
    + intros l1 l2 bor. rewrite init_mem_foldr.
      intros [|Eq]%foldr_gmap_insert_lookup; [done|].
      by apply (state_wf_mem_bor _ WF _ _ _ Eq).
    + intros l1 stack. rewrite init_stacks_foldr.
      intros [->|Eq]%foldr_gmap_insert_lookup; [done|].
      by apply (state_wf_stack_frozen _ WF _ _ Eq).
    + intros l1 stack si. rewrite init_stacks_foldr.
      intros [->|Eq]%foldr_gmap_insert_lookup.
      * by intros ->%elem_of_list_singleton.
      * by apply (state_wf_stack_item _ WF _ _ _ Eq).
    + rewrite Eqs init_stacks_foldr init_mem_foldr. apply foldr_gmap_dom, WF.
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

Lemma dealloc_step_wf σ σ' e e' l bor T:
  base_step e σ.(cheap) (Some $ DeallocEvt l bor T) e' σ'.(cheap) [] →
  instrumented_step σ.(cheap) σ.(cstk) σ.(cbar) σ.(cclk)
                    (Some $ DeallocEvt l bor T)
                  σ'.(cheap) σ'.(cstk) σ'.(cbar) σ'.(cclk) →
  Wf σ → Wf σ'.
Proof.
  destruct σ as [h stk bar clk].
  destruct σ' as [h' stk' bar' clk']. simpl.
  intros BS IS WF. inversion BS. clear BS. simplify_eq.
  inversion IS. clear IS. simplify_eq. constructor; simpl.
  - admit. (* TODO: doesn't hold yet *)
  - intros l1 l2 bor1. rewrite free_mem_foldr.
    intros Eq%foldr_gmap_delete_lookup.
    apply (state_wf_mem_bor _ WF _ _ _ Eq).
  - admit. (* TODO: stk' is sub map of stk *)
  - admit.
Abort.
