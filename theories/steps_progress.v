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

Definition borrow_in (bor: borrow) (stack: list stack_item) :=
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
  (BOR: borrow_in bor stack) :
  ∃ stack', access1' stack bor AccessDealloc β = Some stack'.
Proof.
  induction stack as [|si stack IH].
  { exfalso. move : BOR. rewrite /borrow_in.
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
    α !! (l +ₗ m) = Some stack → borrow_in bor stack.(borrows) ∧ ∀ c,
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
    σ.(cstk) !! (l +ₗ n) = Some stack → borrow_in bor stack.(borrows) ∧
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

Lemma read_mem_is_Some l n h
  (BLK: ∀ m, (m < n)%nat → l +ₗ m ∈ dom (gset loc) h) :
  is_Some (read_mem l n h).
Proof.
  revert BLK.
  eapply (read_mem_elim
            (λ l n h ovl,
              (∀ m : nat, (m < n)%nat → l +ₗ m ∈ dom (gset loc) h) → is_Some ovl)
            (λ _ _ h l n oacc govl,
              (∀ m : nat, (m < n)%nat → l +ₗ m ∈ dom (gset loc) h) →
              is_Some oacc → is_Some govl)).
  - naive_solver.
  - naive_solver.
  - intros l1 n1 h2 l2 n2 oacc IH BLK [acc Eqacc].
    rewrite Eqacc /=.
    assert (is_Some (h2 !! l2)) as [v2 Eq2].
    { apply (elem_of_dom (D:=gset loc)). rewrite -(shift_loc_0_nat l2).
      apply BLK. lia. }
    rewrite Eq2 /=. apply IH; [|by eexists].
    intros m Lt. rewrite shift_loc_assoc -(Nat2Z.inj_add 1). apply BLK. lia.
Qed.

Lemma read_mem_values l n h vl :
  read_mem l n h = Some vl →
  length vl = n ∧
  (∀ i, (i < n)%nat → h !! (l +ₗ i) = vl !! i).
Proof.
  eapply (read_mem_elim
            (λ l n h ovl, ∀ vl, ovl = Some vl →
              length vl = n ∧
              (∀ i, (i < n)%nat → h !! (l +ₗ i) = vl !! i))
            (λ _ _ h l n oacc ovl, ∀ acc vl,
              oacc = Some acc → ovl = Some vl →
              (∀ i, (i < length acc)%nat → h !! (l +ₗ (i - length acc)) = acc !! i) →
              length vl = (length acc + n)%nat ∧
              (∀ i, (i < length acc)%nat → h !! (l +ₗ (i - length acc)) = vl !! i) ∧
              (∀ i, (i < n)%nat → h !! (l +ₗ i) = vl !! (length acc + i)%nat))).
  - intros ??? IH vl1 Eq.
    destruct (IH [] vl1) as [IH1 IH2]; [done..|simpl;intros;lia|].
    split; [done|]. intros i.
     rewrite -{2}(Nat.add_0_l i) -(nil_length (A:=immediate)). by apply IH2.
  - clear. intros _ _ ????????. simplify_eq.
    split; [lia|]. split; [done|intros; lia].
  - clear. move => l0 n0 h l n oacc IH acc vl -> /=.
    case lookup as [v|] eqn:Eq; [|done].
    move => /= Eqvl ACC.
    destruct (IH acc v (acc ++ [v]) vl eq_refl Eqvl) as [IH0 [IH1 IH2]];
      last split; last split.
    { intros i. rewrite app_length /=. intros Lt.
      rewrite (_: l +ₗ 1 +ₗ (i - (length acc + 1)%nat) = l +ₗ (i - length acc));
        last first. { rewrite shift_loc_assoc. f_equal. lia. }
      case (decide (i = length acc)) => ?; [subst i|].
      - by rewrite Z.sub_diag shift_loc_0 list_lookup_middle.
      - have ?: (i < length acc)%nat by lia.
        rewrite ACC; [|done]. by rewrite lookup_app_l. }
    { rewrite IH0 app_length /=. lia. }
    { intros i Lt. rewrite -IH1; [|rewrite app_length /=; lia].
      f_equal. rewrite shift_loc_assoc. f_equal. rewrite app_length /=. lia. }
    intros [|i] Lt.
    + rewrite Nat.add_0_r -IH1; [|rewrite app_length /=; lia].
      rewrite app_length /= shift_loc_assoc. do 2 f_equal. lia.
    + rewrite (_: (l +ₗ S i) =  (l +ₗ 1 +ₗ i));
        [|rewrite shift_loc_assoc; f_equal; lia].
      rewrite IH2; [|lia]. f_equal. rewrite app_length /=. lia.
Qed.

Fixpoint borrow_read_match (β: barriers) (bor: borrow) (stack: list stack_item)
  :=
  match stack with
  | [] => False
  | Raw :: stack => True
  | FnBarrier c :: stack => ¬ is_active β c ∧ borrow_read_match β bor stack
  | Uniq t :: stack =>
      bor = UniqB t ∨ bor ≠ UniqB t ∧ borrow_read_match β bor stack
  end.

Lemma access1'_read_progress bor stack β
  (BOR: borrow_read_match β bor stack) :
  ∃ stack', access1' stack bor AccessRead β = Some stack'.
Proof.
  induction stack as [|si stack IH]; [done|].
  destruct si as [t1| |c]; [destruct bor as [t2|ot]|destruct bor|]; simpl;
    [| |by eexists|by eexists|].
  - destruct BOR as [Eq|[NEq BOR]].
    + inversion Eq. rewrite decide_True; [by eexists|done].
    + rewrite decide_False; [|naive_solver]. by apply IH.
  - destruct BOR as [?|[? ?]]; [done|]. by apply IH.
  - destruct BOR as [NB BOR]. rewrite /is_active bool_decide_false.
    + by apply IH.
    + intros ?. apply NB. by rewrite /is_active bool_decide_true.
Qed.

Lemma accessN_read_progress α β l bor (n: nat) :
  (∀ m, (m < n)%nat → l +ₗ m ∈ dom (gset loc) α) →
  (∀ (m: nat) stack, (m < n)%nat →
    α !! (l +ₗ m) = Some stack →
    is_Some stack.(frozen_since) ∨ borrow_read_match β bor stack.(borrows)) →
  ∃ α', accessN α β l bor n AccessRead = Some α'.
Proof.
  revert α. induction n as [|n IHn]; intros α IN BOR; simpl; [by eexists|].
  assert (is_Some (α !! (l +ₗ n))) as [stack Eq].
  { apply (elem_of_dom (D:=gset loc)), IN. by lia. }
  rewrite Eq /=.
  have BM: is_Some stack.(frozen_since) ∨ borrow_read_match β bor stack.(borrows)
    by apply (BOR n); [lia|done].
  assert (is_Some (access1 β stack bor AccessRead)) as [stack' Eq2].
  { rewrite /access1. case frozen_since as [tf|]; [by eexists|].
    destruct BM as [?%is_Some_None|[? Eq']%access1'_read_progress]; [done|].
    rewrite Eq'; by eexists. }
  rewrite Eq2 /=. apply IHn.
  - intros. apply elem_of_dom. rewrite lookup_insert_ne.
    + apply (elem_of_dom (D:=gset loc)), IN. lia.
    + move => /shift_loc_inj. lia.
  - intros ???. rewrite lookup_insert_ne.
    + apply BOR. lia.
    + move => /shift_loc_inj. lia.
Qed.

Lemma copy_head_step (σ: state) l bor T
  (WF: Wf σ)
  (BLK: ∀ n, (n < tsize T)%nat → l +ₗ n ∈ dom (gset loc) σ.(cheap))
  (BOR: ∀ m stack, (m < tsize T)%nat → σ.(cstk) !! (l +ₗ m) = Some stack →
    is_Some stack.(frozen_since) ∨ borrow_read_match σ.(cbar) bor stack.(borrows)) :
  ∃ σ' vl,
  head_step (Copy (Place l bor T)) σ
            [CopyEvt l bor T vl] (of_val (TValV vl)) σ' [].
Proof.
  destruct (read_mem_is_Some _ _ _ BLK) as [vl RM].
  destruct (accessN_read_progress σ.(cstk) σ.(cbar) l bor (tsize T));[|done|].
  { move => ? /BLK. by rewrite (state_wf_dom _ WF). }
  do 2 eexists. econstructor; econstructor; [done..|].
  move => l1 bor1 /elem_of_list_lookup [i Eqi].
  apply (state_wf_mem_bor _ WF (l +ₗ i) l1).
  destruct (read_mem_values _ _ _ _ RM) as [Eq1 Eq2].
  rewrite Eq2; [done|]. rewrite -Eq1. by eapply lookup_lt_Some.
Qed.

Fixpoint borrow_write_match β (bor: borrow) (stack: list stack_item) :=
  match stack with
  | [] => False
  | Raw :: stack => ∃ ot, bor = AliasB ot
  | FnBarrier c :: stack => ¬ is_active β c ∧ borrow_write_match β bor stack
  | Uniq t :: stack =>
      bor = UniqB t ∨ bor ≠ UniqB t ∧ borrow_write_match β bor stack
  end.

Lemma access1'_write_progress bor stack β
  (BOR: borrow_write_match β bor stack) :
  ∃ stack', access1' stack bor AccessWrite β = Some stack'.
Proof.
  induction stack as [|si stack IH]; [done|].
  destruct si as [t1| |c]; [destruct bor as [t2|ot]|destruct bor|]; simpl;
    [| | |by eexists|].
  - destruct BOR as [Eq|[NEq BOR]].
    + inversion Eq. rewrite decide_True; [by eexists|done].
    + rewrite decide_False; [|naive_solver]. by apply IH.
  - destruct BOR as [?|[? ?]]; [done|]. by apply IH.
  - by destruct BOR as [??].
  - destruct BOR as [NB BOR]. rewrite /is_active bool_decide_false.
    + by apply IH.
    + intros ?. apply NB. by rewrite /is_active bool_decide_true.
Qed.

Lemma accessN_write_progress α β l bor (n: nat) :
  (∀ m, (m < n)%nat → l +ₗ m ∈ dom (gset loc) α) →
  (∀ (m: nat) stack, (m < n)%nat →
    α !! (l +ₗ m) = Some stack → borrow_write_match β bor stack.(borrows)) →
  ∃ α', accessN α β l bor n AccessWrite = Some α'.
Proof.
  revert α. induction n as [|n IHn]; intros α IN BOR; simpl; [by eexists|].
  assert (is_Some (α !! (l +ₗ n))) as [stack Eq].
  { apply (elem_of_dom (D:=gset loc)), IN. by lia. }
  rewrite Eq /=.
  have BM: borrow_write_match β bor stack.(borrows) by apply (BOR n); [lia|done].
  assert (is_Some (access1 β stack bor AccessWrite)) as [stack' Eq2].
  { rewrite /access1.
    destruct (access1'_write_progress _ _ _ BM) as [? Eq']. rewrite Eq'.
    case frozen_since as [tf|]; by eexists. }
  rewrite Eq2 /=. apply IHn.
  - intros. apply elem_of_dom. rewrite lookup_insert_ne.
    + apply (elem_of_dom (D:=gset loc)), IN. lia.
    + move => /shift_loc_inj. lia.
  - intros ???. rewrite lookup_insert_ne.
    + apply BOR. lia.
    + move => /shift_loc_inj. lia.
Qed.

Lemma write_head_step (σ: state) l bor T el vl
  (WF: Wf σ)
  (LEN: length vl = tsize T)
  (VALUES: to_val (TVal el) = Some (TValV vl))
  (BLK: ∀ n, (n < tsize T)%nat → l +ₗ n ∈ dom (gset loc) σ.(cheap))
  (LOCVAL: vl <<b σ.(cclk))
  (BOR: ∀ m stack, (m < tsize T)%nat → σ.(cstk) !! (l +ₗ m) = Some stack →
    borrow_write_match σ.(cbar) bor stack.(borrows)) :
  ∃ σ',
  head_step (Write (Place l bor T) (TVal el)) σ
            [WriteEvt l bor T vl] #☠ σ' [].
Proof.
  destruct (accessN_write_progress σ.(cstk) σ.(cbar) l bor (tsize T)); [|done|].
  { move => ? /BLK. by rewrite (state_wf_dom _ WF). }
  eexists. econstructor; econstructor; [done|by rewrite LEN|done..].
Qed.

Lemma match_deref_Some stack bor :
  borrow_in bor stack → is_Some (match_deref stack bor).
Proof.
  intros IN. induction stack as [|[t1| |ot] stack IH];
    [|destruct bor as [t2|ot2]..|]; simpl.
  - exfalso. revert IN. destruct bor; by apply not_elem_of_nil.
  - case decide => ?; [subst; by eexists|].
    apply IH. move : IN => /elem_of_cons [[]|] //.
  - apply IH. move : IN => /elem_of_cons [|] //.
  - apply IH. move : IN => /elem_of_cons [|] //.
  - by eexists.
  - apply IH. destruct bor; move : IN => /elem_of_cons [|] //.
Qed.

Lemma derefN_uniq_progress α l n t kind
  (BLK : ∀ i, (i < n)%nat → l +ₗ i ∈ dom (gset loc) α)
  (UNI : ∀ i stack, (i < n)%nat → α !! (l +ₗ i) = Some stack →
                    Uniq t ∈ stack.(borrows)) :
  is_Some (derefN α l (UniqB t) n kind).
Proof.
  induction n as [|n IH]; [by eexists|]. simpl.
  assert (is_Some (α !! (l +ₗ n))) as [stack Eq].
  { apply (elem_of_dom (D:=gset loc)), BLK. lia. }
  rewrite Eq /=.
  have IN : Uniq t ∈ borrows stack by (apply (UNI n); [lia|done]).
  destruct (match_deref_Some stack.(borrows) (UniqB t)) as [? Eq2]; [done|].
  rewrite Eq2 /=. apply IH.
  - intros. apply BLK. lia.
  - intros ???. apply UNI. lia.
Qed.

Lemma derefN_raw_progress α l n kind
  (BLK : ∀ i, (i < n)%nat → l +ₗ i ∈ dom (gset loc) α)
  (UNI : ∀ i stack, (i < n)%nat → α !! (l +ₗ i) = Some stack →
                    is_Some stack.(frozen_since) ∨ Raw ∈ stack.(borrows)) :
  is_Some (derefN α l (AliasB None) n kind).
Proof.
  induction n as [|n IH]; [by eexists|]; simpl.
  assert (is_Some (α !! (l +ₗ n))) as [stack Eq].
  { apply (elem_of_dom (D:=gset loc)), BLK. lia. }
  rewrite Eq /=.
  have IN : is_Some stack.(frozen_since) ∨ Raw ∈ stack.(borrows)
    by (apply (UNI n); [lia|done]).
  have IH': is_Some (derefN α l (AliasB None) n kind).
  { apply IH.
    - intros. apply BLK. lia.
    - intros ???. apply UNI. lia. }
  destruct stack.(frozen_since) eqn:Eqf; [done|].
  destruct IN as [[]|IN]; [done|].
  destruct (match_deref_Some stack.(borrows) (AliasB None)) as [? Eq2]; [done|].
  by rewrite Eq2.
Qed.

Lemma derefN_shared_progress α l n t kind
  (NU: kind ≠ UniqueRef)
  (BLK : ∀ i, (i < n)%nat → l +ₗ i ∈ dom (gset loc) α)
  (UNI : ∀ i stack, (i < n)%nat → α !! (l +ₗ i) = Some stack →
          (∃ tf, stack.(frozen_since) = Some tf ∧ (tf ≤ t)%nat) ∨
          (stack.(frozen_since) = None ∧ Raw ∈ stack.(borrows))) :
  is_Some (derefN α l (AliasB (Some t)) n kind).
Proof.
  induction n as [|n IH]; [by eexists|]; simpl.
  assert (is_Some (α !! (l +ₗ n))) as [stack Eq].
  { apply (elem_of_dom (D:=gset loc)), BLK. lia. }
  rewrite Eq /=.
  have IN : (∃ tf, stack.(frozen_since) = Some tf ∧ (tf ≤ t)%nat) ∨
            (stack.(frozen_since) = None ∧ Raw ∈ stack.(borrows))
            by (apply (UNI n); [lia|done]).
  have IH': is_Some (derefN α l (AliasB (Some t)) n kind).
  { apply IH.
    - intros. apply BLK. lia.
    - intros ???. apply UNI. lia. }
  destruct stack.(frozen_since) as [tf|] eqn:Eqf; simpl.
  - rewrite decide_True.
    + by destruct kind.
    + apply inj_le. destruct IN as [[? []]|[]]; [|done]. by simplify_eq.
  - destruct IN as [[? []]|[_ ?]]; [done|].
    destruct (match_deref_Some stack.(borrows) (AliasB (Some t)))
      as [? Eq2]; [done|].
    rewrite Eq2. by destruct kind.
Qed.

Fixpoint subtype' (Tc T : type) (cur: nat) : list nat :=
  if decide (Tc = T) then [cur] else
  match T with
  | Unsafe T => subtype' Tc T cur
  | Union Ts => foldl (λ ns T, ns ++ subtype' Tc T cur) [] Ts
  | Product Ts => foldl (λ ns T, ns ++ subtype' Tc T (cur + 1)) [] Ts
  | Sum Ts =>
      (foldl (λ sns T, ((sns.1 + tsize T)%nat, sns.2 ++ subtype' Tc T sns.1))
             (cur, []) Ts).2
  | _ => []
  end.
Definition subtype Tc T := subtype' Tc T O.

Lemma subtype_O T : O ∈ subtype T T.
Proof.
  rewrite /subtype. induction T; simpl;
    (rewrite decide_True; [by apply elem_of_list_singleton|done]).
Qed.

Lemma unsafe_action_is_Some_weak {A}
  (f: A → _ → nat → _ → _) a l last cur_dist n
  (HF: ∀ a i j b, (last ≤ i ≤ j ∧ j ≤ last + cur_dist + n)%nat →
          is_Some (f a (l +ₗ i) (Z.to_nat (j - i)) b)) :
  is_Some (unsafe_action f a l last cur_dist n).
Proof.
  rewrite /unsafe_action.
  destruct (HF a last (last + cur_dist)%nat true) as [a' Eq1]; [lia|].
  move : Eq1.
  rewrite (_: Z.to_nat (Z.of_nat (last + cur_dist) - Z.of_nat last) = cur_dist);
    last by rewrite Nat2Z.inj_add Z.add_simpl_l Nat2Z.id.
  move => -> /=.
  destruct (HF a' (last + cur_dist)%nat (last + cur_dist + n)%nat false)
    as [? Eq2]; [lia|].
  move : Eq2.
  rewrite (_: Z.to_nat (Z.of_nat (last + cur_dist + n) -
                Z.of_nat (last + cur_dist)) = n);
    last by rewrite Nat2Z.inj_add Z.add_simpl_l Nat2Z.id.
  move => -> /=. by eexists.
Qed.

Lemma visit_freeze_sensitive'_is_Some {A}
  h l (f: A → _ → nat → _ → _) a (last cur_dist: nat) T
  (HF: ∀ a i j b, (last ≤ i ≤ j ∧ j ≤ last + cur_dist + tsize T)%nat →
          is_Some (f a (l +ₗ i) (Z.to_nat (j - i)) b))
  (* (HFSTRONG: ∀ a (i: nat), (cur_dist ≤ i < cur_dist + tsize T) → ∃ a',
          f a (l +ₗ last) i true = Some a' ∧
          is_Some (f a' (l +ₗ last +ₗ i) (Z.to_nat (cur_dist + tsize T - i)) false)) *)
  (SUM: ∀ Ts (n: nat), n ∈ subtype (Sum Ts) T → ∃ i,
          h !! (l +ₗ (last + cur_dist) +ₗ n) = Some (LitV (LitInt i)) ∧
          0 ≤ i < length Ts) :
  is_Some (visit_freeze_sensitive' h l f a last cur_dist T).
Proof.
  revert HF SUM.
  eapply (visit_freeze_sensitive'_elim
    (* general goal P *)
    (λ h l f a last cur_dist T oalc,
      (∀ a i j b,(last ≤ i ≤ j ∧ j ≤ last + cur_dist + tsize T)%nat →
          is_Some (f a (l +ₗ i) (Z.to_nat (j - i)) b)) →
      (∀ Ts (n: nat), n ∈ subtype (Sum Ts) T → ∃ i,
          h !! (l +ₗ (last + cur_dist) +ₗ n) = Some (LitV (LitInt i)) ∧
          0 ≤ i < length Ts) →
      is_Some oalc)
    (λ h l f _ _ _ _ a last cur_dist Ts oalc,
      (∀ a i j b,(last ≤ i ≤ j ∧ j ≤ last + cur_dist + tsize (Product Ts))%nat →
          is_Some (f a (l +ₗ i) (Z.to_nat (j - i)) b)) →
      (∀ Ts' (n: nat), n ∈ subtype (Sum Ts') (Product Ts) → ∃ i,
          h !! (l +ₗ (last + cur_dist) +ₗ n) = Some (LitV (LitInt i)) ∧
          0 ≤ i < length Ts') →
      is_Some oalc)
    (λ h l last cur_dist i f a _ Ts n oalc,
      (∀ a i j b,(last ≤ i ≤ j ∧ j ≤ last + cur_dist + tsize (Sum Ts))%nat →
          is_Some (f a (l +ₗ i) (Z.to_nat (j - i)) b)) →
      (∀ Ts' (n: nat), n ∈ subtype (Sum Ts') (Sum Ts) → ∃ i,
          h !! (l +ₗ (last + cur_dist) +ₗ n) = Some (LitV (LitInt i)) ∧
          0 ≤ i < length Ts') →
          is_Some oalc)).
  - naive_solver.
  - naive_solver.
  - clear. intros ??????? HF _. by apply unsafe_action_is_Some_weak.
  - clear. intros h l f a last cur_dist T HF _.
    case is_freeze; [by eexists|]. by apply unsafe_action_is_Some_weak.
  - (* intros. naive_solver. *) (* product case *)
    admit.
  - naive_solver. (* product inner base case *)
  - clear.
    intros h l f a last cur_dist Ts a1 last1 cur_dist1 T1 Ts1 IH1 IH2 HF SUM.
    destruct IH2 as [[a2 [last2 cur_dist2]] Eq1].
    { admit. }
    { admit. }
    rewrite Eq1 /=. apply (IH1 (a2, (last2,cur_dist2))).
    { admit. (* need some relation between last2 vs. last1, cur_dist2 vs cur_dist1 *) }
    { admit. } (* product inner recursive case *)
  - clear.
    intros h l last cur_dist _ _ Ts EqPoison _ SUM.
    destruct (SUM Ts O) as [i [Eq ?]]; [by apply subtype_O|].
    move : Eq. by rewrite shift_loc_0_nat EqPoison.
  - clear. intros h l last cur_dist l1 tag1 _ _ Ts Eq0 _ SUM.
    destruct (SUM Ts O) as [i [Eq ?]]; [by apply subtype_O|].
    move : Eq. by rewrite shift_loc_0_nat Eq0.
  - admit. (* sum inner decide case *)
  - clear. intros h l last cur_dist f xl e ? _ _ Ts Eq0 _ SUM.
    destruct (SUM Ts O) as [i [Eq ?]]; [by apply subtype_O|].
    move : Eq. by rewrite shift_loc_0_nat Eq0.
  - clear. intros h l last cur_dist _ _ Ts Eq0 _ SUM.
    destruct (SUM Ts O) as [i [Eq ?]]; [by apply subtype_O|].
    move : Eq. by rewrite shift_loc_0_nat Eq0.
  - admit. (* sum inner lookup nil list case: needs extra condition --Sum not nil *)
  - admit. (* sum inner lookup list O case *)
  - admit. (* sum inner lookup list S case *)
Abort.

Lemma ptr_deref_progress h α l bor T mut
  (BLK: ∀ n, (n < tsize T)%nat → l +ₗ n ∈ dom (gset loc) α) :
  match mut with
  | None => True
  | Some mut =>
      match bor with
      | UniqB t => mut = Mutable ∧
          (∀ (m: nat) stack, (m < tsize T)%nat → α !! (l +ₗ m) = Some stack →
            Uniq t ∈ stack.(borrows))
      | AliasB None =>
          (∀ (m: nat) stack, (m < tsize T)%nat → α !! (l +ₗ m) = Some stack →
            is_Some stack.(frozen_since) ∨ Raw ∈ stack.(borrows))
      | AliasB (Some t) => mut = Immutable ∧
          (∀ (m: nat) stack, (m < tsize T)%nat → α !! (l +ₗ m) = Some stack →
            (∃ tf, stack.(frozen_since) = Some tf ∧ (tf ≤ t)%nat) ∨
            (stack.(frozen_since) = None ∧ Raw ∈ stack.(borrows)))
      end
  end →
  ptr_deref h α l bor T mut.
Proof.
  destruct mut as [mut|], bor as [|[t|]]; [| | |done..].
  - intros []. by apply derefN_uniq_progress.
  - intros [? H]. subst mut. simpl. split; [done|]. admit.
  - by apply derefN_raw_progress.
Abort.

Lemma deref_head_step (σ: state) l bor T mut
  (WF: Wf σ)
  (BLK: ∀ n, (n < tsize T)%nat → l +ₗ n ∈ dom (gset loc) σ.(cheap)) :
  ∃ σ',
  head_step (Deref (Lit (LitLoc l bor)) T mut) σ
            [DerefEvt l bor T mut] (Place l bor T) σ' [].
Proof.
  eexists. econstructor; econstructor; [done|].

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

Lemma retag_head_step σ x xbor T kind call :
  ∃ σ' kind',
  head_step (Retag (Place x xbor T) kind call) σ [RetagEvt x T kind'] #☠ σ' [].
Proof.
Abort.

Lemma syscall_head_step σ id :
  head_step (SysCall id) σ [SysCallEvt id] #☠ σ [].
Proof.
  have EE: ∃ σ', head_step (SysCall id) σ [SysCallEvt id] #☠ σ' [] ∧ σ' = σ.
  { eexists. split. econstructor; econstructor. by destruct σ. }
  destruct EE as [? [? ?]]. by subst.
Qed.
