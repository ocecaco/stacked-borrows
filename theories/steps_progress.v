From Equations Require Import Equations.
From stbor Require Export steps_wf.

Definition fresh_block (h : mem) : block :=
  let loclst : list loc := elements (dom (gset loc) h) in
  let blockset : gset block := foldr (λ l, ({[l.1]} ∪)) ∅ loclst in
  fresh blockset.

Lemma is_fresh_block h i : (fresh_block h,i) ∉ dom (gset loc) h.
Proof.
  assert (∀ l (ls: list loc) (X : gset block),
    l ∈ ls → l.1 ∈ foldr (λ l, ({[l.1]} ∪)) X ls) as help.
  { induction 1; set_solver. }
  rewrite /fresh_block /shift /= -elem_of_elements.
  move=> /(help _ _ ∅) /=. apply is_fresh.
Qed.

(* TODO: do we need non-empty condition? ie (tsize T) > 0? *)
Lemma alloc_head_step σ T :
  let l := (fresh_block σ.(cheap), 0) in
  let t := σ.(cclk) in
  ∃ σ',
  head_step (Alloc T) σ [AllocEvt l (UniqB t) T] (Place l (UniqB t) T) σ' [].
Proof.
  eexists. econstructor; econstructor.
  intros. by apply (not_elem_of_dom (D:=gset loc)), is_fresh_block.
Qed.

Definition borrow_write_match (bor: borrow) (stack: list stack_item) :=
  match bor with
  | UniqB t => Uniq t ∈ stack
  | AliasB _ => Raw ∈ stack
  end.

Lemma list_find_None_inv {A} (P : A → Prop) `{∀ x, Decision (P x)} l :
  Forall (λ x, ¬ P x) l → list_find P l = None.
Proof.
  induction l as [|x l IHl]; [eauto|]. simpl. intros FA.
  rewrite decide_False; [|apply (Forall_inv FA)]. rewrite IHl; [done|].
  by eapply Forall_cons_1.
Qed.

Lemma dealloc_no_active_barrier_true stack β kind
  (BAR: Forall (λ si, ¬ is_active_barrier β si) stack) :
  dealloc_no_active_barrier kind stack β = true.
Proof.
  rewrite /dealloc_no_active_barrier. destruct kind; [done..|].
  rewrite (_: find_top_active_call stack β = None); [done|].
  by rewrite /find_top_active_call list_find_None_inv.
Qed.

Lemma access1'_dealloc_progress bor stack β
  (BAR: Forall (λ si, ¬ is_active_barrier β si) stack)
  (BOR: borrow_write_match bor stack) :
  ∃ stack', access1' stack bor AccessDealloc β = Some stack'.
Proof.
  induction stack as [|si stack IH].
  { exfalso. move : BOR. rewrite /borrow_write_match.
    by destruct bor; apply not_elem_of_nil. }
  destruct (Forall_cons_1 _ _ _ BAR) as [NA BAR'].
  specialize (IH BAR').
  destruct si as [t1| |c]; [destruct bor as [t2|ot]|destruct bor|].
  - cbn -[dealloc_no_active_barrier]. case decide => ?.
    + subst. rewrite dealloc_no_active_barrier_true; [by eexists|done].
    + apply IH. by move : BOR => /elem_of_cons [[]|].
  - apply IH. by move : BOR => /elem_of_cons [|].
  - apply IH. by move : BOR => /elem_of_cons [|].
  - cbn -[dealloc_no_active_barrier].
    rewrite dealloc_no_active_barrier_true; [by eexists|done].
  - rewrite /= /is_active bool_decide_false; [|done]. apply IH.
    move : BOR; by destruct bor => /elem_of_cons [|].
Qed.

Lemma accessN_dealloc_progress α β l bor (n: nat) :
  (∀ m : Z, 0 ≤ m ∧ m < n → l +ₗ m ∈ dom (gset loc) α) →
  (∀ (m: nat) stack, (m < n)%nat →
    α !! (l +ₗ m) = Some stack → borrow_write_match bor stack.(borrows) ∧ ∀ c,
      FnBarrier c ∈ stack.(borrows) → β !! c = Some false) →
  ∃ α', accessN α β l bor n AccessDealloc = Some α'.
Proof.
  revert α. induction n as [|n IHn]; intros α IN BOR; simpl; [by eexists|].
  assert (is_Some (α !! (l +ₗ n))) as [stack Eq].
  { apply (elem_of_dom (D:=gset loc)), IN. by lia. }
  rewrite Eq /=.
  destruct (BOR n stack) as [BM FB]; [lia|done|..].
  assert (is_Some (access1' stack.(borrows) bor AccessDealloc β)) as [stk' Eq'].
  { apply access1'_dealloc_progress; [|done].
    apply Forall_forall. intros [t1| |c]; simpl; naive_solver. }
  assert (is_Some (access1 β stack bor AccessDealloc)) as [stack' Eq2].
  { rewrite /access1. case frozen_since as [tf|]; rewrite Eq'; by eexists. }
  rewrite Eq2 /=. apply IHn.
  - intros. apply elem_of_dom. rewrite lookup_delete_ne.
    + apply (elem_of_dom (D:=gset loc)), IN. lia.
    + move => /shift_loc_inj. lia.
  - intros ???. rewrite lookup_delete_ne.
    + apply BOR. lia.
    + move => /shift_loc_inj. lia.
Qed.

Lemma dealloc_head_step (σ: state) T l bor
  (WF: Wf σ)
  (BLK: ∀ m : Z, l +ₗ m ∈ dom (gset loc) σ.(cheap) ↔ 0 ≤ m ∧ m < tsize T)
  (BOR: ∀ (n: nat) stack, (n < tsize T)%nat →
    σ.(cstk) !! (l +ₗ n) = Some stack → borrow_write_match bor stack.(borrows) ∧
    ∀ c, FnBarrier c ∈ stack.(borrows) → σ.(cbar) !! c = Some false) :
  ∃ σ',
  head_step (Free (Place l bor T)) σ [DeallocEvt l bor T] #☠ σ' [].
Proof.
  destruct (accessN_dealloc_progress σ.(cstk) σ.(cbar) l bor (tsize T))
    as [α' Eq']; [|done|].
  - intros. rewrite -(state_wf_dom _ WF). by apply BLK.
  - eexists. econstructor; econstructor; [|done].
    intros. by rewrite -(elem_of_dom (D:= gset loc) σ.(cheap)).
Qed.

Lemma copy_head_step σ l bor T :
  ∃ σ' vl,
  head_step (Copy (Place l bor T)) σ
            [CopyEvt l bor T vl] (of_val (TValV vl)) σ' [].
Proof.
Abort.

Lemma write_head_step σ l bor T el vl
  (VALUES: to_val (TVal el) = Some (TValV vl)) :
  ∃ σ',
  head_step (Write (Place l bor T) (TVal el)) σ
            [WriteEvt l bor T vl] #☠ σ' [].
Proof.
Abort.

Lemma deref_head_step σ l bor T mut :
  ∃ σ',
  head_step (Deref (Lit (LitLoc l bor)) T mut) σ
            [DerefEvt l bor T mut] (Place l bor T) σ' [].
Proof.
Abort.

Lemma newcall_head_step σ :
  let c := fresh (dom (gset call_id) σ.(cbar)) in
  ∃ σ', head_step NewCall σ [NewCallEvt c] (Lit $ LitInt c) σ' [].
Proof. eexists. econstructor; econstructor. Qed.

Lemma endcall_head_step σ c (NZ: 0 ≤ c)
  (BAR: σ.(cbar) !! (Z.to_nat c) = Some true) :
  ∃ σ',
  head_step (EndCall #c) σ [EndCallEvt (Z.to_nat c)] #☠ σ' [].
Proof. eexists. econstructor; econstructor. lia. done. Qed.

Lemma retag_head_step σ x xbor T kind :
  ∃ σ',
  head_step (Retag (Place x xbor T) kind) σ [RetagEvt x T kind] #☠ σ' [].
Proof.
Abort.

Lemma syscall_head_step σ id :
  head_step (SysCall id) σ [SysCallEvt id] #☠ σ [].
Proof.
  have EE: ∃ σ', head_step (SysCall id) σ [SysCallEvt id] #☠ σ' [] ∧ σ' = σ.
  { eexists. split. econstructor; econstructor. by destruct σ. }
  destruct EE as [? [? ?]]. by subst.
Qed.
