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

Lemma access1'_read_is_Some bor stack β
  (BOR: borrow_read_match β bor stack) :
  is_Some (access1' stack bor AccessRead β).
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

Lemma access1_read_is_Some β stack bor
  (BOR: is_Some stack.(frozen_since) ∨ borrow_read_match β bor stack.(borrows)) :
  is_Some (access1 β stack bor AccessRead).
Proof.
  rewrite /access1. case frozen_since as [tf|]; [by eexists|].
  destruct BOR as [?%is_Some_None|[? Eq']%access1'_read_is_Some]; [done|].
  rewrite Eq'; by eexists.
Qed.

Lemma accessN_read_is_Some α β l bor (n: nat) :
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
  destruct (access1_read_is_Some β stack bor) as [stk' Eq2].
  { by apply (BOR n); [lia|done]. }
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
  destruct (accessN_read_is_Some σ.(cstk) σ.(cbar) l bor (tsize T));[|done|].
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

Lemma access1'_write_is_Some β stack bor
  (BOR: borrow_write_match β bor stack) :
  is_Some (access1' stack bor AccessWrite β).
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

Lemma access1_write_is_Some β stack bor
  (BOR: borrow_write_match β bor stack.(borrows)) :
  is_Some (access1 β stack bor AccessWrite).
Proof.
  rewrite /access1.
  destruct (access1'_write_is_Some _ _ _ BOR) as [? Eq']. rewrite Eq'.
  case frozen_since as [tf|]; by eexists.
Qed.

Lemma accessN_write_is_Some α β l bor (n: nat) :
  (∀ m, (m < n)%nat → l +ₗ m ∈ dom (gset loc) α) →
  (∀ (m: nat) stack, (m < n)%nat →
    α !! (l +ₗ m) = Some stack → borrow_write_match β bor stack.(borrows)) →
  is_Some (accessN α β l bor n AccessWrite).
Proof.
  revert α. induction n as [|n IHn]; intros α IN BOR; simpl; [by eexists|].
  assert (is_Some (α !! (l +ₗ n))) as [stack Eq].
  { apply (elem_of_dom (D:=gset loc)), IN. by lia. }
  rewrite Eq /=.
  destruct (access1_write_is_Some β stack bor) as [? Eq2].
  { by apply (BOR n); [lia|done]. }
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
  destruct (accessN_write_is_Some σ.(cstk) σ.(cbar) l bor (tsize T)); [|done|].
  { move => ? /BLK. by rewrite (state_wf_dom _ WF). }
  eexists. econstructor; econstructor; [done|by rewrite LEN|done..].
Qed.

Lemma match_deref_is_Some stack bor :
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

Lemma match_deref_is_Some_inv stack bor :
  is_Some (match_deref stack bor) → borrow_in bor stack.
Proof.
  intros IN. induction stack as [|[t1| |ot] stack IH];
    [|destruct bor as [t2|ot2]..|]; simpl.
  - exfalso. revert IN. by apply is_Some_None.
  - move : IN => /=. case decide => ?.
    + subst. by left.
    + right. by apply IH.
  - right. by apply IH.
  - right. by apply IH.
  - by left.
  - move : IN => /IH ?. destruct bor; by right.
Qed.

Definition deref1_pre stack bor kind :=
  match bor with
  | UniqB t => Uniq t ∈ stack.(borrows)
  | AliasB None =>
      (is_Some stack.(frozen_since) ∨ Raw ∈ stack.(borrows))
  | AliasB (Some t) =>
      kind ≠ UniqueRef ∧
      ((∃ tf, stack.(frozen_since) = Some tf ∧ (tf ≤ t)%nat) ∨
        (stack.(frozen_since) = None ∧ Raw ∈ stack.(borrows)))
  end.

Lemma deref1_is_Some stack bor kind
  (BOR: deref1_pre stack bor kind):
  is_Some (deref1 stack bor kind).
Proof.
  rewrite /deref1.
  destruct bor as [t|[t|]].
  - destruct (match_deref_is_Some stack.(borrows) (UniqB t)) as [? Eq2]; [done|].
    rewrite Eq2 /=. by eexists.
  - destruct BOR as [? BOR].
    destruct stack.(frozen_since) eqn:Eqf.
    + destruct BOR as [[? []]|[]]; [|done]. simplify_eq.
      destruct kind; [done|..]; (rewrite decide_True; [by eexists|lia]).
    + destruct BOR as [[? []]|[]]; [done|].
      destruct kind; [done|..];
      (destruct (match_deref_is_Some stack.(borrows) (AliasB (Some t)))
        as [? Eq2]; [done|]); rewrite Eq2; by eexists.
  - destruct stack.(frozen_since) eqn:Eqf; [by eexists|].
    destruct BOR as [[]|]; [by simplify_eq|].
    destruct (match_deref_is_Some stack.(borrows) (AliasB None)) as [? Eq2]; [done|].
    rewrite Eq2. by eexists.
Qed.

Lemma derefN_is_Some α l n bor kind
  (BLK : ∀ i, (i < n)%nat → l +ₗ i ∈ dom (gset loc) α)
  (UNI : ∀ i stack, (i < n)%nat → α !! (l +ₗ i) = Some stack →
            deref1_pre stack bor kind) :
  is_Some (derefN α l bor n kind).
Proof.
  induction n as [|n IH]; [by eexists|]. simpl.
  assert (is_Some (α !! (l +ₗ n))) as [stack Eq].
  { apply (elem_of_dom (D:=gset loc)), BLK. lia. }
  rewrite Eq /=.
  destruct (deref1_is_Some stack bor kind) as [? Eqs]. { eapply UNI; eauto. }
  rewrite Eqs /=. apply IH.
  - intros. apply BLK. lia.
  - intros ???. apply UNI. lia.
Qed.

Lemma unsafe_action_is_Some_weak {A} (GI: A → nat → Prop)
  (f: A → _ → nat → _ → _) a l last cur_dist n
  (HF: ∀ a i j b, (last ≤ i ≤ j ∧ j ≤ last + cur_dist + n)%nat → GI a i →
          ∃ a', f a (l +ₗ i) (Z.to_nat (j - i)) b = Some a' ∧ GI a' j) :
  GI a last → ∃ a' last' cur_dist',
  unsafe_action f a l last cur_dist n = Some (a', (last', cur_dist')) ∧ GI a' last'.
Proof.
  intros HI. rewrite /unsafe_action.
  destruct (HF a last (last + cur_dist)%nat true) as [a' Eq1]; [lia|done|].
  move : Eq1.
  rewrite (_: Z.to_nat (Z.of_nat (last + cur_dist) - Z.of_nat last) = cur_dist);
    last by rewrite Nat2Z.inj_add Z.add_simpl_l Nat2Z.id.
  move => [-> HI'] /=.
  destruct (HF a' (last + cur_dist)%nat (last + cur_dist + n)%nat false)
    as [? [Eq2 HI2]]; [lia|done|].
  move : Eq2.
  rewrite (_: Z.to_nat (Z.of_nat (last + cur_dist + n) -
                Z.of_nat (last + cur_dist)) = n);
    last by rewrite Nat2Z.inj_add Z.add_simpl_l Nat2Z.id.
  move => -> /=. by do 3 eexists.
Qed.

Lemma unsafe_action_offsets {A}
  (f: A → _ → nat → _ → _) a l (last fsz usz: nat) a' last' cur_dist' :
  unsafe_action f a l last fsz usz = Some (a', (last', cur_dist')) →
  (last' = last + fsz + usz ∧ cur_dist' = O)%nat.
Proof.
  rewrite /unsafe_action. do 2 (case f => ?; [simpl|done]).
  intros. by simplify_eq.
Qed.

Lemma visit_freeze_sensitive'_offsets {A}
  h l (f: A → _ → nat → _ → _) a (last cur_dist: nat) T a' last' cur_dist' :
  let HA (oalc: option (A * (nat * nat))) l1 c1 T1 a2 l2 c2 :=
    (oalc = Some (a2, (l2, c2)) →
      (l1 ≤ l2 ∧ l2 + c2 = l1 + c1 + tsize T1)%nat) in
  HA (visit_freeze_sensitive' h l f a last cur_dist T)
     last cur_dist T a' last' cur_dist'.
Proof.
  intros HA.
  apply (visit_freeze_sensitive'_elim
    (* general goal P *)
    (λ _ _ _ _ l1 c1 T1 oalc, ∀ a2 l2 c2, HA oalc l1 c1 T1 a2 l2 c2)
    (λ _ _ _ _ _ _ _ _ l1 c1 Ts oalc, ∀ a2 l2 c2,
      HA oalc l1 c1 (Product Ts) a2 l2 c2)
    (λ _ _ l1 c1 _ _ _ _ Ts i oalc, ∀ a2 l2 c2,
      oalc = Some (a2, (l2, c2)) → ∃ T1, Ts !! i = Some T1 ∧
      (l1 ≤ l2 ∧ l2 + c2 = l1 + S c1 + tsize T1)%nat)); rewrite /HA.
  - intros. simplify_eq. simpl. lia.
  - intros. simplify_eq. simpl. lia.
  - clear. intros _ ????????? [??]%unsafe_action_offsets. subst. simpl. lia.
  - clear. intros _ ?????????. case is_freeze.
    + intros. simplify_eq. lia.
    + intros [??]%unsafe_action_offsets. subst. lia.
  - naive_solver.
  - intros. simplify_eq. simpl. lia.
  - clear. intros h l f a1 l1 c1 Ts a2 l2 c2 T Ts' IH1 IH2 a4 l4 c4.
    case visit_freeze_sensitive' as [[a3 [l3 c3]]|] eqn:Eq3; [|done].
    cbn -[tsize].
    destruct (IH2 a3 l3 c3) as [Le3 EqO3]; [done|].
    intros Eq4. destruct (IH1 (a3, (l3, c3)) a4 l4 c4 Eq4) as [Le4 EqO4].
    clear -Le3 EqO3 Le4 EqO4. simpl in Le4. rewrite EqO4. cbn -[tsize].
    rewrite EqO3 tsize_product_cons. lia.
  - naive_solver.
  - naive_solver.
  - clear. intros h l l1 c1 ii f a1 Ts1 HL Eq a2 l2 c2.
    case decide => Ge0; [|done].
    case visit_freeze_sensitive'_clause_6_clause_1_visit_lookup
      as [[a3 [l3 c3]]|]; [|done]. cbn -[tsize].
    intros. simplify_eq.
    destruct (HL Ge0 a2 l2 c3) as [T1 [Eq1 [Le2 Eq2]]]; [done|].
    split; [done|]. rewrite le_plus_minus_r; [done|].
    etrans; [apply (le_plus_l _ c3)|]. rewrite Eq2. clear -Eq1.
    rewrite (_: l1 + S c1 + tsize T1 = l1 + c1 + S (tsize T1))%nat; [|lia].
    by eapply plus_le_compat_l, tsize_subtype_of_sum, elem_of_list_lookup_2.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
Qed.

Lemma visit_freeze_sensitive'_is_Some {A} (GI: A → nat → Prop)
  h l (f: A → _ → nat → _ → _) a (last cur_dist: nat) T
  (HF: ∀ a i j b, (last ≤ i ≤ j ∧ j ≤ last + cur_dist + tsize T)%nat → GI a i →
          ∃ a', f a (l +ₗ i) (Z.to_nat (j - i)) b = Some a' ∧ GI a' j)
  (* (HFSTRONG: ∀ a (i: nat), (cur_dist ≤ i < cur_dist + tsize T) → ∃ a',
          f a (l +ₗ last) i true = Some a' ∧
          is_Some (f a' (l +ₗ last +ₗ i) (Z.to_nat (cur_dist + tsize T - i)) false)) *)
  (SUM: ∀ Ts (n: nat), (n, (Sum Ts)) ∈ sub_sum_types T → ∃ i,
          h !! (l +ₗ (last + cur_dist) +ₗ n) = Some (LitV (LitInt i)) ∧
          0 ≤ i < length Ts) :
  GI a last → ∃ a' last' cur_dist',
  visit_freeze_sensitive' h l f a last cur_dist T = Some (a', (last', cur_dist')) ∧
  GI a' last'.
Proof.
  revert HF SUM.
  apply (visit_freeze_sensitive'_elim
    (* general goal P *)
    (λ h l f a last cur_dist T oalc,
      (∀ a i j b,(last ≤ i ≤ j ∧ j ≤ last + cur_dist + tsize T)%nat → GI a i →
          ∃ a', f a (l +ₗ i) (Z.to_nat (j - i)) b = Some a' ∧ GI a' j) →
      (∀ Ts (n: nat), (n, Sum Ts) ∈ sub_sum_types T → ∃ i,
          h !! (l +ₗ (last + cur_dist) +ₗ n) = Some (LitV (LitInt i)) ∧
          0 ≤ i < length Ts) →
      GI a last → ∃ a' last' cur', oalc = Some (a', (last', cur')) ∧ GI a' last')
    (λ h l f _ _ _ _ a last cur_dist Ts oalc,
      (∀ a i j b, (last ≤ i ≤ j ∧ j ≤ last + cur_dist + tsize (Product Ts))%nat →
          GI a i → ∃ a', f a (l +ₗ i) (Z.to_nat (j - i)) b = Some a' ∧ GI a' j) →
      (∀ Ts' (n: nat), (n, Sum Ts') ∈ sub_sum_types (Product Ts) → ∃ i,
          h !! (l +ₗ (last + cur_dist) +ₗ n) = Some (LitV (LitInt i)) ∧
          0 ≤ i < length Ts') →
      GI a last → ∃ a' last' cur', oalc = Some (a', (last', cur')) ∧ GI a' last')
    (λ h l last cur_dist i f a _ Ts n oalc,
      (∀ a i j b, (last ≤ i ≤ j ∧ j ≤ last + cur_dist + tsize (Sum Ts))%nat →
          GI a i → ∃ a', f a (l +ₗ i) (Z.to_nat (j - i)) b = Some a' ∧ GI a' j) →
      (∀ T' Ts' (n: nat), T' ∈ Ts → (n, Sum Ts') ∈ sub_sum_types T' → ∃ i,
          h !! (l +ₗ (last + cur_dist) +ₗ S n) = Some (LitV (LitInt i)) ∧
          0 ≤ i < length Ts') → (n < length Ts)%nat →
      GI a last → ∃ a' last' cur', oalc = Some (a', (last', cur')) ∧ GI a' last')).
  - naive_solver.
  - naive_solver.
  - clear. intros ??????? HF _. by apply unsafe_action_is_Some_weak.
  - clear. intros h l f a last cur_dist T HF _.
    case is_freeze; [by do 3 eexists|]. by apply unsafe_action_is_Some_weak.
  - naive_solver.
  - naive_solver.
  - clear.
    intros h l f a last cur_dist Ts a1 last1 cur_dist1 T1 Ts1 IH1 IH2 HF SUM HI.
    destruct IH2 as (a2 & last2 & cur_dist2 & Eq1 & HI2); [..|done|].
    { intros ???? [? Le]. apply HF. split; [done|]. clear -Le.
      rewrite tsize_product_cons. by lia. }
    { intros ???. by apply SUM, sub_sum_types_product_first. }
    destruct (visit_freeze_sensitive'_offsets _ _ _ _ _ _ _ _ _ _ Eq1)
      as [LeO EqO].
    rewrite Eq1 /=. apply (IH1 (a2, (last2,cur_dist2))); [..|done].
    { intros a' i j b. cbn -[tsize]. intros Lej. apply HF.
      clear -LeO EqO Lej. destruct Lej as [[Le2 Lei] Lej].
      split; [lia|]. move : Lej. rewrite EqO tsize_product_cons. lia. }
    { intros Ts' n IN.
      rewrite /= shift_loc_assoc -2!Nat2Z.inj_add EqO -(Nat.add_assoc _ _ n)
              2!Nat2Z.inj_add -shift_loc_assoc.
      by apply SUM, sub_sum_types_product_further. }
    (* product inner recursive case *)
  - clear.
    intros h l last cur_dist f a Ts EqPoison _ SUM.
    destruct (SUM Ts O) as [i [Eq ?]]; [by apply sub_sum_types_O_elem_of|].
    move : Eq. by rewrite shift_loc_0_nat EqPoison.
  - clear. intros h l last cur_dist l1 tag1 f a Ts Eq0 _ SUM.
    destruct (SUM Ts O) as [i [Eq ?]]; [by apply sub_sum_types_O_elem_of|].
    move : Eq. by rewrite shift_loc_0_nat Eq0.
  - clear. intros h l last cur_dist n f a Ts IH1 Eqn BLK SUM HI.
    destruct (SUM Ts O) as [i [Eq [Ge0 Lt]]]; [by apply sub_sum_types_O_elem_of|].
    move : Eq. rewrite shift_loc_0_nat Eqn. intros Eq. simplify_eq.
    rewrite decide_True; [|done].
    destruct (IH1 Ge0) as (a2 & l2 & c2 & Eq2 & HI2); [done|..|done|].
    + intros T' Ts' n IN1 IN2. apply SUM, sub_sum_types_elem_of_2.
      right. split; [lia|]. exists T'. split; [done|]. by rewrite /= Nat.sub_0_r.
    + rewrite -(Nat2Z.id (length Ts)) -Z2Nat.inj_lt; lia.
    + exists a2, l2. eexists. by rewrite Eq2 /=.
  - clear. intros h l last cur_dist fl xl e ? f a Ts Eq0 _ SUM.
    destruct (SUM Ts O) as [i [Eq ?]]; [by apply sub_sum_types_O_elem_of|].
    move : Eq. by rewrite shift_loc_0_nat Eq0.
  - clear. intros h l last cur_dist f a Ts Eq0 _ SUM.
    destruct (SUM Ts O) as [i [Eq ?]]; [by apply sub_sum_types_O_elem_of|].
    move : Eq. by rewrite shift_loc_0_nat Eq0.
  - clear. intros ???? _ ?? _ i _ _. simpl. lia.
  - clear. intros h l l1 c1 ii f a Ts1 T Ts IH BLK SUM _. apply IH.
    + intros ???? [? Le]. apply BLK. split; [done|].
      etrans; [apply Le|]. rewrite -Nat.add_assoc plus_Snm_nSm Nat.add_assoc.
      apply (plus_le_compat_l _ _ (l1 + c1)), tsize_subtype_of_sum. by left.
    + intros ?? IN.
      rewrite (_: l +ₗ (l1 + S c1) +ₗ n = l +ₗ (l1 + c1) +ₗ S n); last first.
      { rewrite 2!shift_loc_assoc. f_equal. lia. }
      apply (SUM T); [by left|done].
  - clear. intros h l l1 c1 ii fa a Ts0 T Ts i IH BLK SUM Lt.
    apply IH.
    + intros ???? [? Le]. apply BLK. split; [done|].
      etrans; [apply Le|].
      by apply (plus_le_compat_l _ _ (l1 + c1)), tsize_sum_cons_le.
    + intros ?? n IN. apply SUM. by right.
    + move : Lt => /=. lia.
Qed.

Lemma visit_freeze_sensitive_is_Some' {A} (GI: A → nat → Prop)
  h l (f: A → _ → nat → _ → _) a T
  (HF: ∀ a i j b, (i ≤ j ∧ j ≤ tsize T)%nat → GI a i →
          ∃ a', f a (l +ₗ i) (Z.to_nat (j - i)) b = Some a' ∧ GI a' j)
  (SUM: ∀ Ts (n: nat), (n, (Sum Ts)) ∈ sub_sum_types T → ∃ i,
          h !! (l +ₗ n) = Some (LitV (LitInt i)) ∧ 0 ≤ i < length Ts) :
  GI a O → ∃ a', visit_freeze_sensitive h l T f a = Some a' ∧ GI a' (tsize T).
Proof.
  intros HI. rewrite /visit_freeze_sensitive.
  destruct (visit_freeze_sensitive'_is_Some GI h l f a O O T)
    as (a1 & l1 & c1 & Eq1 & HI1); [..|done|].
  { rewrite 2!Nat.add_0_l. intros ???? [[??]?]. by apply HF. }
  { rewrite Z.add_0_l shift_loc_0. apply SUM. }
  rewrite Eq1 -(Nat.add_sub c1 l1) -(Nat2Z.id (c1 + l1 - l1))
          Nat2Z.inj_sub; [|lia].
  move : Eq1. intros [? Eq]%visit_freeze_sensitive'_offsets.
  destruct (HF a1 l1 (c1 + l1)%nat true) as (a2 & Eq2 & HI2); [|done|].
  { split; [lia|]. move : Eq. rewrite 2!Nat.add_0_l. lia. }
  exists a2. split; [done|].
  move : Eq. by rewrite 2!Nat.add_0_l Nat.add_comm => [<-].
Qed.

Lemma visit_freeze_sensitive_is_Some'_2 {A} (GI: A → nat → Prop)
  h l (f: A → _ → nat → _ → _) a T
  (HF: ∀ a i j b, (i ≤ j ∧ j ≤ tsize T)%nat → GI a i →
          ∃ a', f a (l +ₗ i) (Z.to_nat (j - i)) b = Some a' ∧ GI a' j)
  (SUM: ∀ Ts (n: nat), (n, (Sum Ts)) ∈ sub_sum_types T → ∃ i,
          h !! (l +ₗ n) = Some (LitV (LitInt i)) ∧ 0 ≤ i < length Ts) :
  GI a O → is_Some (visit_freeze_sensitive h l T f a).
Proof.
  intros HI. destruct (visit_freeze_sensitive_is_Some' GI h l f a T)
    as [a' [Eq _]]; [done..|by eexists].
Qed.

Lemma visit_freeze_sensitive_is_Some {A}
  h l (f: A → _ → nat → _ → _) a T
  (HF: ∀ a i j b, (i ≤ j ∧ j ≤ tsize T)%nat →
          is_Some (f a (l +ₗ i) (Z.to_nat (j - i)) b))
  (SUM: ∀ Ts (n: nat), (n, (Sum Ts)) ∈ sub_sum_types T → ∃ i,
          h !! (l +ₗ n) = Some (LitV (LitInt i)) ∧ 0 ≤ i < length Ts) :
  is_Some (visit_freeze_sensitive h l T f a).
Proof.
  destruct (visit_freeze_sensitive_is_Some' (λ _ _, True) h l f a T)
    as [a' [Eq _]]; [|done..|by eexists].
  intros a1 i j b Le _. destruct (HF a1 i j b Le). by eexists.
Qed.

Definition ptr_deref_pre (h: mem) (α: bstacks) l bor T mut : Prop :=
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
            (stack.(frozen_since) = None ∧ Raw ∈ stack.(borrows))) ∧
          (∀ Ts (n: nat), (n, (Sum Ts)) ∈ sub_sum_types T → ∃ i,
            h !! (l +ₗ n) = Some (LitV (LitInt i)) ∧ 0 ≤ i < length Ts)
      end
  end.

Lemma ptr_deref_progress h α l bor T mut
  (BLK: ∀ n, (n < tsize T)%nat → l +ₗ n ∈ dom (gset loc) α) :
  ptr_deref_pre h α l bor T mut →
  ptr_deref h α l bor T mut.
Proof.
  destruct mut as [mut|], bor as [|[t|]]; [| | |done..].
  - intros []. by apply derefN_is_Some.
  - intros [? [IN ?]]. subst mut. simpl. split; [done|].
    apply visit_freeze_sensitive_is_Some; [|done].
    intros _ i j b [Le1 Le2]. apply derefN_is_Some.
    + intros i' Lt. rewrite shift_loc_assoc -Nat2Z.inj_add. apply BLK.
      move : Lt. rewrite -Nat2Z.inj_sub // Nat2Z.id. lia.
    + intros i' stk Lt. rewrite shift_loc_assoc -Nat2Z.inj_add.
      intros Eq. split; [by destruct b|]. move : Eq. apply IN.
      move : Lt. rewrite -Nat2Z.inj_sub // Nat2Z.id. lia.
  - simpl. intros PRE. by apply derefN_is_Some.
Qed.

Lemma deref_head_step (σ: state) l bor T mut
  (WF: Wf σ)
  (BLK: ∀ n, (n < tsize T)%nat → l +ₗ n ∈ dom (gset loc) σ.(cheap))
  (MUT: ptr_deref_pre σ.(cheap) σ.(cstk) l bor T mut) :
  ∃ σ',
  head_step (Deref (Lit (LitLoc l bor)) T mut) σ
            [DerefEvt l bor T mut] (Place l bor T) σ' [].
Proof.
  eexists. econstructor; econstructor; [done|].
  apply ptr_deref_progress; [|done].
  move => ? /BLK. by rewrite (state_wf_dom _ WF).
Qed.

Lemma newcall_head_step σ :
  let c := fresh (dom (gset call_id) σ.(cbar)) in
  ∃ σ', head_step NewCall σ [NewCallEvt c] (Lit $ LitInt c) σ' [].
Proof. eexists. econstructor; econstructor. Qed.


Lemma endcall_head_step σ c (NZ: 0 ≤ c)
  (BAR: σ.(cbar) !! (Z.to_nat c) = Some true) :
  ∃ σ',
  head_step (EndCall #c) σ [EndCallEvt (Z.to_nat c)] #☠ σ' [].
Proof. eexists. econstructor; econstructor. lia. done. Qed.

Definition is_loc_val (v: immediate) :=
  match v with
  | LitV (LitLoc _ _) => True
  | _ => False
  end.

Lemma retag_lookup h α clk β l kind T h' α' clk' :
  let Hh h h' :=
    (∀ l v, h !! l = Some v → ¬ is_loc_val v → h' !! l = Some v) in
  retag h α clk β l kind T = Some (h', α', clk') →
  Hh h h'.
Proof.
  intros Hh.
  eapply (retag_elim
    (* general goal P *)
    (λ h _ _ _ _ _ _ ohac, ∀ h' α' clk',
        ohac = Some (h', α', clk') → Hh h h')
    (* invariant for Product's where P1 *)
    (λ _ _ _ _ _ _ _ h _ _ _ _ ohac, ∀ h' α' clk',
        ohac = Some (h', α', clk') → Hh h h')
    (* invariant for Sum's where P3 *)
    (λ h _ _ _ _ _ _ _ _ _ ohac, ∀ h' α' clk',
        ohac = Some (h', α', clk') → Hh h h')); rewrite /Hh.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - (* Reference cases *)
    clear. intros h ?? bor α clk β rt_kind p_kind T Eq h' α' clk'.
    destruct p_kind as [mut| |];
      [|destruct rt_kind; try by (intros; simplify_eq)|];
      (case retag_ref as [[[bor' α1] clk1]|] eqn:Eq1; [simpl|done]);
      intros ???; simplify_eq; intros Eq0 NL; (rewrite lookup_insert_ne; [done|]);
      intros ?; subst x; rewrite Eq0 in Eq; simplify_eq; by apply NL.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - (* Product inner recursive case *)
    intros ????????????? IH1 IH2 ???.
    case retag as [hac|]; [|done]. move => /= /IH1 IH.
    destruct hac as [[]]. intros. apply IH; [|done]. by eapply IH2.
  - naive_solver.
  - naive_solver.
  - (* Sum case *)
    intros ???????? IH Eq ???. case decide => Le; [|done]. by apply IH.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
Qed.

Lemma retag_lookup_ref h α clk β l kind T h' α' clk' :
  let Hh h h' :=
    (∀ l v, h !! l = Some v → is_loc_val v → ∃ v', h' !! l = Some v' ∧ is_loc_val v') in
  retag h α clk β l kind T = Some (h', α', clk') →
  Hh h h'.
Proof.
  intros Hh.
  eapply (retag_elim
    (* general goal P *)
    (λ h _ _ _ _ _ _ ohac, ∀ h' α' clk',
        ohac = Some (h', α', clk') → Hh h h')
    (* invariant for Product's where P1 *)
    (λ _ _ _ _ _ _ _ h _ _ _ _ ohac, ∀ h' α' clk',
        ohac = Some (h', α', clk') → Hh h h')
    (* invariant for Sum's where P3 *)
    (λ h _ _ _ _ _ _ _ _ _ ohac, ∀ h' α' clk',
        ohac = Some (h', α', clk') → Hh h h')); rewrite /Hh.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - (* Reference cases *)
    clear. intros h ?? bor α clk β rt_kind p_kind T Eq h' α' clk'.
    destruct p_kind as [mut| |];
      [|destruct rt_kind; try by (intros; simplify_eq; naive_solver)|];
      (case retag_ref as [[[bor' α1] clk1]|] eqn:Eq1; [simpl|done]);
      intros ? l0 ?; simplify_eq; intros Eq0 NL;
      (case (decide (l0 = x)) => [->|?];
        [rewrite lookup_insert; naive_solver
        |rewrite lookup_insert_ne; [naive_solver|done]]).
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - (* Product inner recursive case *)
    intros ????????????? IH1 IH2 ???.
    case retag as [hac|]; [|done]. move => /= /IH1 IH.
    destruct hac as [[h2 α2] clk2]. intros.
    destruct (IH2 h2 α2 clk2 eq_refl l1 v) as [v2 []]; [done..|].
    by apply (IH l1 v2).
  - naive_solver.
  - naive_solver.
  - (* Sum case *)
    intros ???????? IH Eq ???. case decide => Le; [|done]. by apply IH.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
Qed.

Lemma create_borrow_is_Some stk bor kind
  (BOR: match bor with
         | UniqB _ => kind = UniqueRef ∧ stk.(frozen_since) = None
         | AliasB None => kind = RawRef ∧ stk.(frozen_since) = None
         | AliasB (Some t) =>
            kind = RawRef ∧ stk.(frozen_since) = None ∨
            kind = FrozenRef ∧
              match stk.(frozen_since) with
              | Some t' => (t' ≤ t)%nat
              | _ => True
              end
         end) :
  is_Some (create_borrow stk bor kind).
Proof.
  destruct bor as [t|[t|]];
    [destruct BOR as [? EQN]
    |destruct BOR as [[? EQN]|[? EQN]]
    |destruct BOR as [? EQN]]; subst; simpl.
  - rewrite EQN. by eexists.
  - rewrite EQN. by eexists.
  - case_match; [|by eexists]. rewrite decide_True; [by eexists|done].
  - rewrite EQN. by eexists.
Qed.

Lemma add_barrier_frozen_eq stk bar :
  (add_barrier stk bar).(frozen_since) = stk.(frozen_since).
Proof.
  rewrite /add_barrier. case_match; [done|]. case_match; [done..|]. by case_decide.
Qed.

Lemma access1_is_Some β stk bor kind
  (ACC: match kind with
        | UniqueRef => stk.(frozen_since) = None ∧ borrow_write_match β bor stk.(borrows)
        | FrozenRef => is_Some stk.(frozen_since) ∨ borrow_read_match β bor stk.(borrows)
        | RawRef => stk.(frozen_since) = None ∧ borrow_read_match β bor stk.(borrows)
        end) :
  is_Some (access1 β stk bor (to_access_kind kind)).
Proof.
  destruct kind.
  - destruct (access1_write_is_Some β stk bor) as [stk' Eq1]; [by destruct ACC|].
    rewrite Eq1. by eexists.
  - destruct (access1_read_is_Some β stk bor) as [stk' Eq1]; [done|].
    rewrite Eq1. by eexists.
  - destruct (access1_read_is_Some β stk bor) as [? Eq1]; [naive_solver|].
    rewrite Eq1. by eexists.
Qed.

Lemma access1_read_frozen β stk bor stk':
  access1 β stk bor AccessRead = Some stk' →
  stk'.(frozen_since) = stk.(frozen_since).
Proof.
  rewrite /access1. case_match; [naive_solver|].
  case access1' => ? ; [|done]. simpl. naive_solver.
Qed.

Lemma access1_write_unfreeze β stk bor kind stk' (NR: kind ≠ AccessRead) :
  access1 β stk bor kind = Some stk' →
  stk'.(frozen_since) = None.
Proof.
  rewrite /access1. case_match.
  - destruct kind; [done|..]; (case access1' => ?; [|done]); simpl; naive_solver.
  - case access1' => ? ; [|done]. simpl. naive_solver.
Qed.

Lemma deref1_Some_None stk bor kind :
  deref1 stk bor kind = Some None →
  is_aliasing bor = true ∧ is_Some stk.(frozen_since).
Proof.
  rewrite /deref1.
  destruct bor as [t|[t|]]; simpl; [by case match_deref|..];
  case frozen_since.
  - naive_solver.
  - destruct kind; [done|..]; by case match_deref.
  - naive_solver.
  - by case match_deref.
Qed.

Lemma deref1_Some_Some stk bor kind i :
  deref1 stk bor kind = Some (Some i) → borrow_in bor stk.(borrows).
Proof.
  rewrite /deref1. destruct bor as [t|[t|]]; simpl.
  - case match_deref eqn:Eq => //= ?.
    apply (match_deref_is_Some_inv _ (UniqB t)). by eexists.
  - case_match; case_match; [done|by case_decide..|done| |];
      case match_deref eqn:Eq => //= ?;
      apply (match_deref_is_Some_inv _ (AliasB (Some t))); by eexists.
  - case_match; [done|]. case match_deref eqn:Eq => //= ?.
    apply (match_deref_is_Some_inv _ (AliasB None)); by eexists.
Qed.

Lemma create_borrow_is_Some_2 β stk bor kind stk' bor'
  (ACC: kind = RawRef → stk.(frozen_since) = None)
  (BOR': match bor' with
         | UniqB _ => kind = UniqueRef
         | AliasB None => kind = RawRef
         | AliasB (Some _) => kind = FrozenRef ∨ kind = RawRef
         end)
  (BORt: match bor' with
         | UniqB t | AliasB (Some t) =>
            match stk.(frozen_since) with | Some t' => (t' ≤ t)%nat | _ => True end
         | _ => True
         end)
  (EQ: access1 β stk bor (to_access_kind kind) = Some stk') :
  is_Some (create_borrow stk' bor' kind).
Proof.
  apply create_borrow_is_Some.
  destruct bor' as [t'|[t'|]]; [|destruct BOR'|].
  - split; [done|]. subst kind. move : EQ. by apply access1_write_unfreeze.
  - right. split; [done|]. destruct (to_access_kind kind).
    + by rewrite (access1_read_frozen _ _ _ _ EQ).
    + by rewrite (access1_write_unfreeze β stk bor AccessWrite stk').
    + by rewrite (access1_write_unfreeze β stk bor AccessDealloc stk').
  - left. split; [done|]. subst kind.
    by rewrite (access1_read_frozen _ _ _ _ EQ) ACC.
  - split; [done|]. subst kind.
    by rewrite (access1_read_frozen _ _ _ _ EQ) ACC.
Qed.

Lemma reborrow1_is_Some stk bor bor' kind β bar
  (BOR: deref1_pre stk bor kind)
  (ACC: match kind with
        | UniqueRef => stk.(frozen_since) = None ∧ borrow_write_match β bor stk.(borrows)
        | FrozenRef => is_Some stk.(frozen_since) ∨ borrow_read_match β bor stk.(borrows)
        | RawRef => stk.(frozen_since) = None ∧ borrow_read_match β bor stk.(borrows)
        end)
  (BOR': match bor' with
         | UniqB t => kind = UniqueRef
         | AliasB None => kind = RawRef
         | AliasB (Some _) => kind = FrozenRef ∨ kind = RawRef
         end)
  (BORt: match bor' with
         | UniqB t | AliasB (Some t) =>
            match stk.(frozen_since) with | Some t' => (t' ≤ t)%nat | _ => True end
         | _ => True
         end)
  (BORin: ∀ t, bor' = UniqB t → Uniq t ∉ stk.(borrows)) :
  is_Some (reborrow1 stk bor bor' kind β bar).
Proof.
  rewrite /reborrow1.
  destruct (deref1_is_Some stk bor kind BOR) as [oi Eqoi].
  rewrite Eqoi /=.
  destruct bar; [|destruct oi as [i|]].
  - destruct (access1_is_Some _ _ _ _ ACC) as [stk' Eq']. rewrite Eq'.
    apply create_borrow_is_Some. rewrite add_barrier_frozen_eq.
    destruct bor' as [t'|[t'|]]; [|destruct BOR'|].
    + split; [done|]. subst kind.
      move : Eq'. by apply access1_write_unfreeze.
    + right. split; [done|]. destruct (to_access_kind kind).
      * by rewrite (access1_read_frozen _ _ _ _ Eq').
      * by rewrite (access1_write_unfreeze β stk bor AccessWrite stk').
      * by rewrite (access1_write_unfreeze β stk bor AccessDealloc stk').
    + left. split; [done|]. subst kind.
      rewrite (access1_read_frozen _ _ _ _ Eq'). by destruct ACC.
    + split; [done|]. subst kind.
      rewrite (access1_read_frozen _ _ _ _ Eq'). by destruct ACC.
  - destruct (deref1 stk bor' kind) as [[i'|]|] eqn:Eqi'.
    + case decide => Le.
      * have IN:= deref1_Some_Some _ _ _ _ Eqi'. clear -IN BORin.
        destruct bor' as [t|]; [|by eexists]. exfalso. by apply (BORin t).
      * destruct (access1_is_Some _ _ _ _ ACC) as [stk' Eq']. rewrite Eq'.
        move : Eq'. apply create_borrow_is_Some_2; [naive_solver|done..].
    + move : Eqi' => /deref1_Some_None [-> _]. by eexists.
    + destruct (access1_is_Some _ _ _ _ ACC) as [stk' Eq']. rewrite Eq'.
      move : Eq'. apply create_borrow_is_Some_2; [naive_solver|done..].
  - destruct (deref1 stk bor' kind) as [[i'|]|] eqn:Eqi'.
    + destruct (access1_is_Some _ _ _ _ ACC) as [stk' Eq']. rewrite Eq'.
      move : Eq'. apply create_borrow_is_Some_2; [naive_solver|done..].
    + move : Eqi' => /deref1_Some_None [-> _]. by eexists.
    + destruct (access1_is_Some _ _ _ _ ACC) as [stk' Eq']. rewrite Eq'.
      move : Eq'. apply create_borrow_is_Some_2; [naive_solver|done..].
Qed.

Lemma reborrowN_is_Some α β l n bor bor' kind bar
  (BLK: ∀ m, (m < n)%nat → l +ₗ m ∈ dom (gset loc) α)
  (STK: ∀ m stk, (m < n)%nat → α !! (l +ₗ m) = Some stk →
          deref1_pre stk bor kind ∧
          match kind with
          | UniqueRef => stk.(frozen_since) = None ∧ borrow_write_match β bor stk.(borrows)
          | FrozenRef => is_Some stk.(frozen_since) ∨ borrow_read_match β bor stk.(borrows)
          | RawRef => stk.(frozen_since) = None ∧ borrow_read_match β bor stk.(borrows)
          end ∧
          match bor' with
          | UniqB t | AliasB (Some t) =>
            match stk.(frozen_since) with | Some t' => (t' ≤ t)%nat | _ => True end
          | _ => True
          end ∧ ∀ t, bor' = UniqB t → Uniq t ∉ stk.(borrows))
  (BOR': match bor' with
         | UniqB _ => kind = UniqueRef
         | AliasB None => kind = RawRef
         | AliasB (Some _) => kind = FrozenRef ∨ kind = RawRef
         end) :
  is_Some (reborrowN α β l n bor bor' kind bar).
Proof.
  revert α BLK STK.
  induction n as [|n IH]; intros α BLK STK; [by eexists|]; simpl.
  assert (is_Some (α !! (l +ₗ n))) as [stk Eq].
  { apply (elem_of_dom (D:=gset loc)), BLK. lia. }
  rewrite Eq /=. destruct (STK n stk) as (H1 & H2 & H3 & H4); [lia|done|].
  destruct (reborrow1_is_Some stk bor bor' kind β bar) as [stk2 Eq2];
    [done..|]. clear H1 H2 H3 H4.
  rewrite Eq2 /=. apply IH.
  { intros ??. rewrite dom_map_insert_is_Some; [|by eexists]. apply BLK. lia. }
  intros m stkm Lt. rewrite lookup_insert_ne; last by (intros ?%shift_loc_inj; lia).
  apply STK. by lia.
Qed.

Lemma borrow_write_match_uniq β t stk :
  borrow_write_match β (UniqB t) stk → Uniq t ∈ stk.
Proof.
  induction stk as [|[t'| |ci] stk IH]; [done|..].
  - move => /= [[->]|[? /IH]]; [by left|by right].
  - move => [? ?]//.
  - move => [? /IH]. by right.
Qed.

Lemma borrow_write_match_raw β stk :
  borrow_write_match β (AliasB None) stk → Raw ∈ stk.
Proof.
  induction stk as [|[t'| |ci] stk IH]; [done|..].
  - move => /= [//|[? /IH]]. by right.
  - by left.
  - move => [? /IH]. by right.
Qed.

Lemma borrow_read_match_raw β stk :
  borrow_read_match β (AliasB None) stk → Raw ∈ stk.
Proof.
  induction stk as [|[t'| |ci] stk IH]; [done|..].
  - move => /= [//|[? /IH]]. by right.
  - by left.
  - move => [? /IH]. by right.
Qed.

Lemma borrow_read_match_shared β stk t :
  borrow_read_match β (AliasB (Some t)) stk → Raw ∈ stk.
Proof.
  induction stk as [|[t'| |ci] stk IH]; [done|..].
  - move => /= [//|[? /IH]]. by right.
  - by left.
  - move => [? /IH]. by right.
Qed.

Lemma reborrowN_lookup (α1 α2 : bstacks) β l n bor bor' kind bar
  (EQB : reborrowN α1 β l n bor bor' kind bar = Some α2) :
  (∀ m, (n ≤ m)%nat → α2 !! (l +ₗ m) = α1 !! (l +ₗ m)) ∧
  (∀ m stk, (m < n)%nat → α1 !! (l +ₗ m) = Some stk →
    ∃ stk', α2 !! (l +ₗ m) = Some stk' ∧
    reborrow1 stk bor bor' kind β bar = Some stk') .
Proof.
  revert α1 EQB.
  induction n as [|n IH]; simpl; intros α1 EQB; [simplify_eq|].
  - split; [done|intros ??;lia].
  - move : EQB. case (α1 !! (l +ₗ n)) as [stk1|] eqn:Eq1; [|done]. simpl.
    case reborrow1 as [stk2|] eqn:Eq2; [|done].
    move => /= /IH [IH1 IH2]. split.
    + intros m Le. rewrite IH1; [|lia].
      rewrite lookup_insert_ne; [done|].
      intros ?%shift_loc_inj. lia.
    + intros m stk Lt Eq3.
      case (decide (m = n)) => [?|NEq].
      * subst m. rewrite Eq1 in Eq3. simplify_eq.
        exists stk2. rewrite (IH1 n) // lookup_insert //.
      * destruct (IH2 m stk) as [stk' Eq]; [lia|..| by exists stk'].
        rewrite lookup_insert_ne; [done|].
        intros ?%shift_loc_inj. by apply NEq, Nat2Z.inj.
Qed.

Lemma visit_freeze_sensitive'_is_freeze {A}
  h l (f: A → _ → nat → _ → _) a (last cur_dist: nat) T
  (SUM: ∀ Ts (n: nat), (n, (Sum Ts)) ∈ sub_sum_types T → ∃ i,
          h !! (l +ₗ (last + cur_dist) +ₗ n) = Some (LitV (LitInt i)) ∧
          0 ≤ i < length Ts) :
  is_freeze T →
  visit_freeze_sensitive' h l f a last cur_dist T
    = Some (a, (last, (cur_dist + tsize T)%nat)).
Proof.
  revert SUM.
  apply (visit_freeze_sensitive'_elim
    (* general goal P *)
    (λ h l f a last cur_dist T oalc,
      (∀ Ts (n: nat), (n, Sum Ts) ∈ sub_sum_types T → ∃ i,
          h !! (l +ₗ (last + cur_dist) +ₗ n) = Some (LitV (LitInt i)) ∧
          0 ≤ i < length Ts) →
      is_freeze T → oalc = Some (a, (last, (cur_dist + tsize T)%nat)))
    (λ h l f _ _ _ _ a last cur_dist Ts oalc,
      (∀ Ts' (n: nat), (n, Sum Ts') ∈ sub_sum_types (Product Ts) → ∃ i,
          h !! (l +ₗ (last + cur_dist) +ₗ n) = Some (LitV (LitInt i)) ∧
          0 ≤ i < length Ts') →
      is_freeze (Product Ts) →
      oalc = Some (a, (last, (cur_dist + tsize (Product Ts))%nat)))
    (λ h l last cur_dist i f a _ Ts n oalc,
      (∀ T' Ts' (n: nat), T' ∈ Ts → (n, Sum Ts') ∈ sub_sum_types T' → ∃ i,
          h !! (l +ₗ (last + cur_dist) +ₗ S n) = Some (LitV (LitInt i)) ∧
          0 ≤ i < length Ts') → (n < length Ts)%nat →
      is_freeze (Sum Ts) → ∃ T, Ts !! n = Some T ∧
      oalc = Some (a, (last, (cur_dist + S (tsize T))%nat)))).
  - done.
  - clear. intros ???????? _ _. by rewrite /= Nat.add_1_r.
  - done.
  - clear. intros ??????? _. by move => /Is_true_eq_true ->.
  - clear. naive_solver.
  - clear. intros ?? _ _ _ _ _ ??? _ _. by rewrite /= Nat.add_0_r.
  - clear. intros h l f a last cur_dist Ts a' l1 c1 T Ts' IH1 IH2 SUM FRZ.
    rewrite IH2; first rewrite /= (IH1 (a', (l1, c1 + tsize T)%nat)).
    + simpl. do 3 f_equal. change (tsize T) with (0 + tsize T)%nat.
      rewrite -(foldl_fmap_shift_init _ (λ n, n + tsize T)%nat);
        [by lia| intros ?? _; by lia].
    + intros Ts0 n IN.
      rewrite /= shift_loc_assoc -2!Nat2Z.inj_add
              (_: (l1 + (c1 + tsize T) + n) = (l1 + c1) + (tsize T + n))%nat; [|lia].
      rewrite 2!Nat2Z.inj_add -shift_loc_assoc.
      by apply SUM, sub_sum_types_product_further.
    + by eapply is_freeze_cons_product_inv.
    + intros ???. by apply SUM, sub_sum_types_product_first.
    + by eapply is_freeze_cons_product_inv.
  - clear. intros h l last cur_dist f a Ts EqPoison SUM _.
    destruct (SUM Ts O) as [i [Eq ?]]; [by apply sub_sum_types_O_elem_of|].
    move : Eq. by rewrite shift_loc_0_nat EqPoison.
  - clear. intros h l last cur_dist l1 tag1 f a Ts Eq0 SUM _.
    destruct (SUM Ts O) as [i [Eq ?]]; [by apply sub_sum_types_O_elem_of|].
    move : Eq. by rewrite shift_loc_0_nat Eq0.
  - clear. intros h l last cur_dist n f a Ts IH1 Eqn SUM HI.
    destruct (SUM Ts O) as [i [Eq [Ge0 Lt]]]; [by apply sub_sum_types_O_elem_of|].
    move : Eq. rewrite shift_loc_0_nat Eqn. intros Eq. simplify_eq.
    rewrite decide_True; [|done].
    destruct IH1 as [T' [EqT Eq]]; [done|..|done|].
    { intros T' Ts' n IN1 IN2. apply SUM, sub_sum_types_elem_of_2.
      right. split; [lia|]. exists T'. split; [done|]. by rewrite /= Nat.sub_0_r. }
    { rewrite -(Nat2Z.id (length Ts)) -Z2Nat.inj_lt; lia. }
    rewrite Eq /=. do 3 f_equal. lia.
  - clear. intros h l last cur_dist fl xl e ? f a Ts Eq0 SUM _.
    destruct (SUM Ts O) as [i [Eq ?]]; [by apply sub_sum_types_O_elem_of|].
    move : Eq. by rewrite shift_loc_0_nat Eq0.
  - clear. intros h l last cur_dist f a Ts Eq0 SUM _.
    destruct (SUM Ts O) as [i [Eq ?]]; [by apply sub_sum_types_O_elem_of|].
    move : Eq. by rewrite shift_loc_0_nat Eq0.
  - clear. intros ???? _ ?? _ i _. simpl. lia.
  - clear. intros h l l1 c1 ii f a Ts1 T Ts IH SUM _ FRZ. rewrite IH.
    + exists T. split; [done|]. do 3 f_equal. lia.
    + intros ?? IN.
      rewrite (_: l +ₗ (l1 + S c1) +ₗ n = l +ₗ (l1 + c1) +ₗ S n); last first.
      { rewrite 2!shift_loc_assoc. f_equal. lia. }
      apply (SUM T); [by left|done].
    + by eapply is_freeze_cons_sum_inv.
  - clear. intros h l l1 c1 ii fa a Ts0 T Ts i IH SUM Lt FRZ.
    apply IH.
    + intros ?? n IN. apply SUM. by right.
    + move : Lt => /=. lia.
    + by eapply is_freeze_cons_sum_inv.
Qed.

Lemma visit_freeze_sensitive_is_freeze {A}
  h l (f: A → _ → nat → _ → _) a T
  (SUM: ∀ Ts (n: nat), (n, (Sum Ts)) ∈ sub_sum_types T → ∃ i,
          h !! (l +ₗ n) = Some (LitV (LitInt i)) ∧ 0 ≤ i < length Ts) :
  is_freeze T → visit_freeze_sensitive h l T f a = f a l (tsize T) true.
Proof.
  intros FRZ. rewrite /visit_freeze_sensitive visit_freeze_sensitive'_is_freeze;
    [by rewrite shift_loc_0_nat Nat.add_0_l|by rewrite Z.add_0_l shift_loc_0|done].
Qed.

Lemma reborrow_is_freeze_is_Some h α β l bor T bar bor'
  (BLK: ∀ m, (m < tsize T)%nat → l +ₗ m ∈ dom (gset loc) α)
  (STK: ∀ m stk, (m < tsize T)%nat → α !! (l +ₗ m) = Some stk →
          match bor' with
          | UniqB t => stk.(frozen_since) = None ∧
              Uniq t ∉ stk.(borrows) ∧
              match bor with
              | UniqB _ | AliasB None => borrow_write_match β bor stk.(borrows)
              | _ => False
              end
          | AliasB (Some t) =>
              match stk.(frozen_since) with
              | Some t' => (t' ≤ t)%nat
              | _ => True
              end ∧
              match bor with
              | UniqB t => Uniq t ∈ stk.(borrows) ∧ borrow_read_match β bor stk.(borrows)
              | AliasB None =>
                  is_Some stk.(frozen_since) ∨ borrow_read_match β bor stk.(borrows)
              | AliasB (Some t) =>
                  match stk.(frozen_since) with
                  | Some t' => (t' ≤ t)%nat
                  | _ => borrow_read_match β bor stk.(borrows)
                  end
              end
          | AliasB None => stk.(frozen_since) = None ∧
              match bor with
              | UniqB t => Uniq t ∈ stk.(borrows) ∧ borrow_read_match β bor stk.(borrows)
              | AliasB None => borrow_read_match β bor stk.(borrows)
              | _ => False
              end
          end)
  (SUM: ∀ Ts (n: nat), (n, (Sum Ts)) ∈ sub_sum_types T → ∃ i,
          h !! (l +ₗ n) = Some (LitV (LitInt i)) ∧ 0 ≤ i < length Ts)
  (FRZ: is_freeze T):
  is_Some (reborrow h α β l bor T bar bor').
Proof.
  rewrite /reborrow. destruct bor' as [t|[t|]].
  - rewrite /reborrowBlock /=. apply reborrowN_is_Some; [done| |done].
    intros m stk Lt Eq. destruct (STK _ _ Lt Eq) as [EQN [NIN IN]].
    repeat split; [|done|..|by rewrite EQN|naive_solver].
    + destruct bor as [|[]]; [|done|].
      * move : IN => /borrow_write_match_uniq //.
      * move : IN => /borrow_write_match_raw. by right.
    + by destruct bor as [|[]].
  - rewrite visit_freeze_sensitive_is_freeze; [|done..].
    apply reborrowN_is_Some; [done| |by left].
    intros m stk Lt Eq. destruct (STK _ _ Lt Eq) as [FZ BOR].
    repeat split; [| |done|naive_solver].
    + destruct bor as [t1|[t1|]]; simpl; [apply BOR|..].
      * split; [done|]. destruct stk.(frozen_since); [left; by naive_solver|].
        right. split; [done|]. by eapply borrow_read_match_shared.
      * destruct BOR; [by left|right]. by eapply borrow_read_match_raw.
    + destruct bor as [t1|[t1|]]; simpl; [..|done].
      * right. apply BOR.
      * destruct stk.(frozen_since); [left; by eexists|by right].
    (* set GI: bstacks → nat → Prop :=
      λ α' i, ∀ m, (i ≤ m < tsize T)%nat → α' !! (l +ₗ m) = α !! (l +ₗ m).
    apply (visit_freeze_sensitive_is_Some'_2 GI); [|done|done].
    intros α1 i j b Le HI; rewrite /reborrowBlock /=.
    rewrite (_: (if if is_unique_ref (if b then FrozenRef else RawRef)
                    then true else false
                 then None else
                 reborrowN α1 β (l +ₗ i) (Z.to_nat (j - i)) bor (AliasB (Some t))
                    (if b then FrozenRef else RawRef) bar) =
                 reborrowN α1 β (l +ₗ i) (Z.to_nat (j - i)) bor (AliasB (Some t))
                 (if b then FrozenRef else RawRef) bar); last by destruct b.
    destruct (reborrowN_is_Some α1 β (l +ₗ i) (Z.to_nat (j - i)) bor
                  (AliasB (Some t)) (if b then FrozenRef else RawRef) bar)
                  as [α2 Eq2].
    + intros m. rewrite -Nat2Z.inj_sub; [|apply Le].
      rewrite Nat2Z.id shift_loc_assoc -Nat2Z.inj_add. intros Lt.
      have ?: (i + m < tsize T)%nat by lia.
      rewrite (elem_of_dom (D:=gset loc)) HI; [|lia].
      by apply (elem_of_dom (D:=gset loc)), BLK.
    + intros m stk. rewrite -Nat2Z.inj_sub; [|apply Le].
      rewrite Nat2Z.id shift_loc_assoc -Nat2Z.inj_add. intros Lt Eq.
      have Ltm: (i + m < tsize T)%nat by lia.
      have Eq': α !! (l +ₗ (i + m)%nat) = Some stk by rewrite -HI; [done|lia].
      destruct (STK _ _ Ltm Eq').
      repeat split; [..|done|naive_solver].
      * admit.
      * admit.
    + destruct b; [by left|by right].
    + exists α2. split; [done|]. move : Eq2 => /reborrowN_lookup Le2.
      intros m []. move : (Le2 (m - i)%nat).
      rewrite shift_loc_assoc -Nat2Z.inj_add -le_plus_minus; [|lia].
      rewrite -Nat2Z.inj_sub; [|apply Le].
      rewrite Nat2Z.id => ->; [|lia]. apply HI. lia. *)
  - rewrite /reborrowBlock /=. apply reborrowN_is_Some; [done| |done].
    intros m stk Lt Eq. destruct (STK _ _ Lt Eq) as [EQN IN].
    repeat split; [|done|..|naive_solver].
    + destruct bor as [|[]]; [by apply IN|done|].
      move : IN => /borrow_read_match_raw. by right.
    + destruct bor as [|[]]; [apply IN|done..].
Qed.

Lemma create_borrow_deref1_is_freeze stk stk' bor' kind :
  create_borrow stk bor' kind = Some stk' → deref1_pre stk' bor' FrozenRef.
Proof.
  rewrite /create_borrow. destruct kind; destruct bor' as [t|ot].
  - case frozen_since => ?; [done|simplify_eq]. simpl. by left.
  - case frozen_since => ?; [done|simplify_eq]. simpl.
    destruct ot; simpl; destruct stk.(borrows) as [|[] ?]; set_solver.
  - done.
  - destruct ot; [|done]. simpl. case frozen_since eqn:Eqs.
    + case decide => ?; [|done]. intros ?. simplify_eq. simpl. set_solver.
    + intros ?. simplify_eq. simpl. set_solver.
  - case frozen_since => ?; [done|simplify_eq]. simpl. by left.
  - case frozen_since => ?; [done|simplify_eq]. simpl.
    destruct ot; simpl; destruct stk.(borrows) as [|[] ?]; set_solver.
Qed.

Lemma deref1_pre_is_freeze stk bor kind :
  is_Some (deref1 stk bor kind) → deref1_pre stk bor FrozenRef.
Proof.
  rewrite /deref1_pre.
  destruct bor as [t|[t|]].
  - move => /= IS. apply (match_deref_is_Some_inv _ (UniqB t)).
    move : IS. case match_deref; [naive_solver|by intros []].
  - simpl.
    case stk.(frozen_since) as [ts|] eqn:Eqs;
      (destruct kind; [by intros []|..]).
    + case decide => ?; [|by intros []]; split; [done|left];
      exists ts; split; [done|lia].
    + case decide => ?; [|by intros []]; split; [done|left];
      exists ts; split; [done|lia].
    + move => IS. split; [done|]. right. split; [done|].
      apply (match_deref_is_Some_inv _ (AliasB (Some t))).
      move : IS. case match_deref; [naive_solver|by intros []].
    + move => IS. split; [done|]. right. split; [done|].
      apply (match_deref_is_Some_inv _ (AliasB (Some t))).
      move : IS. case match_deref; [naive_solver|by intros []].
  - simpl. case stk.(frozen_since) as [ts|] eqn:Eqs; [naive_solver|].
    move => IS. right. apply (match_deref_is_Some_inv _ (AliasB None)).
    move : IS. case match_deref; [naive_solver|by intros []].
Qed.

Lemma reborrow1_deref1_is_freeze stk stk' bor bor' kind β bar :
  reborrow1 stk bor bor' kind β bar = Some stk' →
  deref1_pre stk' bor' FrozenRef.
Proof.
  rewrite /reborrow1.
  case (deref1 stk bor kind) as [[i|]|] eqn:Eq1; simpl; [..|done];
    destruct bar as [c|]; simpl.
  - case access1 as [stk1|] eqn: Eq2; [|done].
    by apply create_borrow_deref1_is_freeze.
  - case (deref1 stk bor' kind) as [[i'|]|] eqn:Eq2.
    + case decide => ?.
      * case is_aliasing eqn:Eqa; [|done]. intros ?. simplify_eq.
        eapply deref1_pre_is_freeze. by eexists.
      * case access1 as [stk1|] eqn: Eq3; [|done].
        by apply create_borrow_deref1_is_freeze.
    + case is_aliasing eqn:Eqa; [|done]. intros ?. simplify_eq.
      eapply deref1_pre_is_freeze. by eexists.
    + case access1 as [stk1|] eqn: Eq3; [|done].
      by apply create_borrow_deref1_is_freeze.
  - case access1 as [stk1|] eqn: Eq2; [|done].
    by apply create_borrow_deref1_is_freeze.
  - case (deref1 stk bor' kind) as [[i'|]|] eqn:Eq2.
    + case access1 as [stk1|] eqn: Eq3; [|done].
      by apply create_borrow_deref1_is_freeze.
    + case is_aliasing eqn:Eqa; [|done]. intros ?. simplify_eq.
      eapply deref1_pre_is_freeze. by eexists.
    + case access1 as [stk1|] eqn: Eq3; [|done].
      by apply create_borrow_deref1_is_freeze.
Qed.

Lemma reborrowBlock_deref1_is_freeze α β l n bor bor' kind bar α' :
  reborrowBlock α β l n bor bor' kind bar = Some α' →
  ∀ m stk, (m < n)%nat → α' !! (l +ₗ m) = Some stk →
  deref1_pre stk bor' FrozenRef.
Proof.
  rewrite /reborrowBlock. case xorb; [done|].
  revert α.
  induction n as [|n IH]; intros α; simpl; [intros _ ??; lia|].
  case lookup as [stk|] eqn:Eqs; [simpl|done].
  case reborrow1 as [stk'|] eqn:Eq1; [simpl|done].
  intros Eq2 m stk1 Lt EqL.
  case (decide (m = n)) => [?|NEq].
  - subst. destruct (reborrowN_lookup _ _ _ _ _ _ _ _ _ Eq2) as [HL _].
    move : EqL. rewrite HL // lookup_insert. intros ?. simplify_eq.
    by eapply reborrow1_deref1_is_freeze.
  - apply (IH (<[l +ₗ n:=stk']> α) Eq2 m stk1); [lia|done].
Qed.

Lemma reborrow_deref1_is_freeze h α β l bor T bar bor' α'
  (FRZ: is_freeze T)
  (SUM: ∀ Ts (n: nat), (n, (Sum Ts)) ∈ sub_sum_types T → ∃ i,
          h !! (l +ₗ n) = Some (LitV (LitInt i)) ∧ 0 ≤ i < length Ts) :
  reborrow h α β l bor T bar bor' = Some α' →
  ∀ m stk, (m < tsize T)%nat → α' !! (l +ₗ m) = Some stk →
  deref1_pre stk bor' FrozenRef.
Proof.
  rewrite /reborrow. destruct bor' as [|[]].
  - by apply reborrowBlock_deref1_is_freeze.
  - rewrite visit_freeze_sensitive_is_freeze; [|done..].
    by apply reborrowBlock_deref1_is_freeze.
  - by apply reborrowBlock_deref1_is_freeze.
Qed.

Lemma create_borrow_read_access_is_freeze β stk stk' bor' kind :
  create_borrow stk bor' kind = Some stk' →
  is_Some stk'.(frozen_since) ∨ borrow_read_match β bor' stk'.(borrows).
Proof.
  rewrite /create_borrow.
  destruct kind; destruct bor' as [t|ot]; [| |done| | |].
  - case frozen_since => ?; [done|simplify_eq]. naive_solver.
  - case frozen_since => ?; [done|simplify_eq].
    destruct ot; simpl; destruct stk.(borrows) as [|[]]; naive_solver.
  - destruct ot; [|done]. case frozen_since eqn:Eqs.
    + case decide => ?; [|done]. intros. simplify_eq. rewrite Eqs. naive_solver.
    + intros ?. simplify_eq. naive_solver.
  - case frozen_since => ?; [done|simplify_eq]. naive_solver.
  - case frozen_since => ?; [done|simplify_eq].
    destruct ot; simpl; destruct stk.(borrows) as [|[] ?]; naive_solver.
Qed.

(*
Lemma access1'_is_Some_read β stk bor kind stk' :
  access1' stk bor kind β = Some stk' → borrow_read_match β bor stk'.
Proof.
  induction stk as [|si stack IH]; [done|].
  destruct si as [t1| |c]; [destruct bor as [t2|ot]|destruct bor|]; simpl;
    [|by apply IH|..].
  - case decide => ?; [|by apply IH]. subst. case_match; [|done].
    intros. simplify_eq. by left.
  - destruct kind; [|apply IH..]. intros. by simplify_eq.
  - destruct kind; [intros; by simplify_eq|..]; (case_match; [|done]);
      intros; by simplify_eq.
  - case_match; [done|apply IH].
Qed.

Lemma access1_read_access β stk bor kind stk' :
  access1 β stk bor kind = Some stk' →
  is_Some stk'.(frozen_since) ∨ borrow_read_match β bor stk'.(borrows).
Proof.
  rewrite /access1. case stk.(frozen_since) eqn:Eqf; [destruct kind|..];
    [intros; simplify_eq; rewrite Eqf; left; by eexists|..];
    (case access1' as [stk1|] eqn:Eqa; [|done]); simpl; intros; simplify_eq; right;
    move : Eqa; apply access1'_is_Some_read.
Qed. *)

Lemma match_deref_lookup stk bor i :
  match_deref stk bor = Some i →
  i < length stk ∧
  stk !! (length stk - S i)%nat =
    Some (match bor with | UniqB t => Uniq t | _ => Raw end).
Proof.
  revert i. induction stk as [|[t| |c] stk IH]; intros i; [done|..]; simpl.
  - destruct bor; [case decide => ?; [subst|]|].
    + intros ?. simplify_eq. split; [lia|]. by rewrite Nat.sub_diag.
    + move => /IH [Lt Eq]. split; [lia|].
      rewrite -Eq (lookup_app_r [Uniq t]); [|simpl; lia].
      f_equal. simpl. lia.
    + move => /IH [Lt Eq]. split; [lia|].
      rewrite -Eq (lookup_app_r [Uniq _]); [|simpl; lia].
      f_equal. simpl. lia.
  - destruct bor; [|intros ?; simplify_eq].
    + move => /IH [Lt Eq]. split; [lia|].
      rewrite -Eq (lookup_app_r [Raw]); [|simpl; lia].
      f_equal. simpl. lia.
    + split; [lia|by rewrite Nat.sub_diag].
  - move => /IH [Lt Eq]. split; [lia|].
    rewrite -Eq (lookup_app_r [FnBarrier _]); [|simpl; lia].
    f_equal. simpl. lia.
Qed.

Lemma match_deref_borrow_read_match β stk bor bor' oi oi' 
  (BOR : borrow_read_match β bor stk)
  (IS1 : match_deref stk bor ≫= Some ∘ Some = Some oi)
  (IS2 : match_deref stk bor' ≫= Some ∘ Some = Some oi')
  (Le : oi ⊑ oi') (AL: is_aliasing bor') :
  borrow_read_match β bor' stk.
Proof.
  induction stk as [|[t| |c] stk' IH]; [done| |done|].
  - simpl. right. split; [by destruct bor'|].
    have IS2':  match_deref stk' bor' ≫= Some ∘ Some = Some oi'
      by destruct bor'. clear IS2.
    move : BOR IS1 => /= [?|[NE BOR]].
    + subst bor. rewrite decide_True; [|done]. simpl. intros. simplify_eq.
      destruct oi' as [i'|]; [|done].
      destruct (match_deref_lookup stk' bor' i') as [Lt _].
      * move : IS2'. case match_deref; [naive_solver|done].
      * exfalso. apply Nat2Z.inj_lt in Lt. move : Le Lt. cbn.
        rewrite /sqsubseteq /nat_sqsubseteq /=. lia.
    + destruct bor.
      * rewrite decide_False; [|by intros ?; subst].
        intros ?. by apply IH.
      * intros ?. by apply IH.
  - move : BOR => /= [INA BOR]. split; [done|].
    by apply IH.
Qed.

Lemma deref1_read_access β stk bor bor' kind
  (BOR: match bor' with
        | UniqB _ =>
            match bor with
            | UniqB _ | AliasB None => borrow_write_match β bor stk.(borrows)
            | _ => False
            end
        | AliasB (Some _) =>
            match bor with
            | UniqB _ => borrow_read_match β bor stk.(borrows)
            | AliasB None =>
                is_Some stk.(frozen_since) ∨ borrow_read_match β bor stk.(borrows)
            | AliasB (Some _) =>
                if stk.(frozen_since) then True else
                  borrow_read_match β bor stk.(borrows)
            end
        | AliasB None =>
            match bor with
            | UniqB _ | AliasB None => borrow_read_match β bor stk.(borrows)
            | _ => False
            end
        end)
  (AL: is_aliasing bor') oi oi':
  deref1 stk bor kind = Some oi →
  deref1 stk bor' kind = Some oi' →
  oi ⊑ oi' →
  is_Some stk.(frozen_since) ∨ borrow_read_match β bor' stk.(borrows).
Proof.
  rewrite /deref1.
  destruct bor' as [|[t'|]]; [done|..];
    (case stk.(frozen_since) eqn:Eqf; [left; by eexists|intros IS1 IS2 Le; right]);
    destruct bor as [t|[t|]].
  - have IS2':
      match_deref (borrows stk) (AliasB (Some t')) ≫= Some ∘ Some = Some oi'.
    { by destruct kind. } clear Eqf AL IS2.
    eapply match_deref_borrow_read_match; eauto.
  - have IS1':
      match_deref (borrows stk) (AliasB (Some t)) ≫= Some ∘ Some = Some oi.
    { by destruct kind. }
    have IS2':
      match_deref (borrows stk) (AliasB (Some t')) ≫= Some ∘ Some = Some oi'.
    { by destruct kind. } clear Eqf AL IS1 IS2.
    eapply match_deref_borrow_read_match; eauto.
  - destruct BOR as [[]|BOR]; [done|].
    have IS2':
      match_deref (borrows stk) (AliasB (Some t')) ≫= Some ∘ Some = Some oi'.
    { by destruct kind. } clear Eqf AL IS2.
    eapply match_deref_borrow_read_match; eauto.
  - clear Eqf AL. eapply match_deref_borrow_read_match; eauto.
  - done.
  - clear Eqf AL. eapply match_deref_borrow_read_match; eauto.
Qed.

Lemma reborrow1_read_access_is_freeze stk stk' bor bor' kind β bar
  (BOR: match bor' with
        | UniqB _ =>
            match bor with
            | UniqB _ | AliasB None => borrow_write_match β bor stk.(borrows)
            | _ => False
            end
        | AliasB (Some _) =>
            match bor with
            | UniqB _ => borrow_read_match β bor stk.(borrows)
            | AliasB None =>
                is_Some stk.(frozen_since) ∨ borrow_read_match β bor stk.(borrows)
            | AliasB (Some _) =>
                if stk.(frozen_since) then True else
                  borrow_read_match β bor stk.(borrows)
            end
        | AliasB None =>
            match bor with
            | UniqB _ | AliasB None => borrow_read_match β bor stk.(borrows)
            | _ => False
            end
        end) :
  reborrow1 stk bor bor' kind β bar = Some stk' →
  is_Some stk'.(frozen_since) ∨ borrow_read_match β bor' stk'.(borrows).
Proof.
  rewrite /reborrow1.
  case (deref1 stk bor kind) as [[i|]|] eqn:Eq1; simpl; [..|done];
    destruct bar as [c|]; simpl.
  - case access1 as [stk1|] eqn: Eq2; [|done]. simpl.
    by apply create_borrow_read_access_is_freeze.
  - case (deref1 stk bor' kind) as [[i'|]|] eqn:Eq2.
    + case decide => ?.
      * case is_aliasing eqn:Eqa; [|done]. intros ?. simplify_eq.
        eapply deref1_read_access; eauto.
      * case access1 as [stk1|] eqn: Eq3; [|done].
        by apply create_borrow_read_access_is_freeze.
    + case is_aliasing eqn:Eqa; [|done]. intros ?. simplify_eq.
      left. by eapply deref1_Some_None.
    + case access1 as [stk1|] eqn: Eq3; [|done].
      by apply create_borrow_read_access_is_freeze.
  - case access1 as [stk1|] eqn: Eq2; [|done].
    by apply create_borrow_read_access_is_freeze.
  - case (deref1 stk bor' kind) as [[i'|]|] eqn:Eq2.
    + case access1 as [stk1|] eqn: Eq3; [|done].
      by apply create_borrow_read_access_is_freeze.
    + case is_aliasing eqn:Eqa; [|done]. intros ?. simplify_eq.
      eapply deref1_read_access; eauto.
    + case access1 as [stk1|] eqn: Eq3; [|done].
      by apply create_borrow_read_access_is_freeze.
Qed.

Lemma reborrowBlock_read_access_is_freeze α β l n bor bor' kind bar α'
  (STK: ∀ m stk, (m < n)%nat → α !! (l +ₗ m) = Some stk →
          match bor' with
          | UniqB _ =>
              match bor with
              | UniqB _ | AliasB None => borrow_write_match β bor stk.(borrows)
              | _ => False
              end
          | AliasB (Some _) =>
              match bor with
              | UniqB _ => borrow_read_match β bor stk.(borrows)
              | AliasB None =>
                  is_Some stk.(frozen_since) ∨ borrow_read_match β bor stk.(borrows)
              | AliasB (Some _) =>
                  if stk.(frozen_since) then True else
                    borrow_read_match β bor stk.(borrows)
              end
          | AliasB None =>
              match bor with
              | UniqB _ | AliasB None => borrow_read_match β bor stk.(borrows)
              | _ => False
              end
          end) :
  reborrowBlock α β l n bor bor' kind bar = Some α' →
  ∀ m stk, (m < n)%nat → α' !! (l +ₗ m) = Some stk →
  is_Some stk.(frozen_since) ∨ borrow_read_match β bor' stk.(borrows).
Proof.
  rewrite /reborrowBlock. case xorb; [done|].
  revert α STK.
  induction n as [|n IH]; intros α STK; simpl; [intros _ ??; lia|].
  case lookup as [stk|] eqn:Eqs; [simpl|done].
  case reborrow1 as [stk'|] eqn:Eq1; [simpl|done].
  intros Eq2 m stk1 Lt EqL.
  case (decide (m = n)) => [?|NEq].
  - subst. destruct (reborrowN_lookup _ _ _ _ _ _ _ _ _ Eq2) as [HL _].
    move : EqL. rewrite HL // lookup_insert. intros ?. simplify_eq.
    specialize (STK _ _ Lt Eqs). clear IH Eq2 HL Lt Eqs.
    eapply reborrow1_read_access_is_freeze; eauto.
  - eapply (IH (<[l +ₗ n:=stk']> α)); [|done| |done]; [|lia].
    intros m2 stk2 Lt2.
    rewrite lookup_insert_ne; [apply STK|intros ?%shift_loc_inj]; lia.
Qed.

Lemma reborrow_read_access_is_freeze h α β l bor T bar bor' α'
  (FRZ: is_freeze T)
  (SUM: ∀ Ts (n: nat), (n, (Sum Ts)) ∈ sub_sum_types T → ∃ i,
          h !! (l +ₗ n) = Some (LitV (LitInt i)) ∧ 0 ≤ i < length Ts)
  (STK: ∀ m stk, (m < tsize T)%nat → α !! (l +ₗ m) = Some stk →
          match bor' with
          | UniqB _ =>
              match bor with
              | UniqB _ | AliasB None => borrow_write_match β bor stk.(borrows)
              | _ => False
              end
          | AliasB (Some _) =>
              match bor with
              | UniqB _ => borrow_read_match β bor stk.(borrows)
              | AliasB None =>
                  is_Some stk.(frozen_since) ∨ borrow_read_match β bor stk.(borrows)
              | AliasB (Some _) =>
                  if stk.(frozen_since) then True else
                    borrow_read_match β bor stk.(borrows)
              end
          | AliasB None =>
              match bor with
              | UniqB _ | AliasB None => borrow_read_match β bor stk.(borrows)
              | _ => False
              end
          end) :
  reborrow h α β l bor T bar bor' = Some α' →
  ∀ m stk, (m < tsize T)%nat → α' !! (l +ₗ m) = Some stk →
  is_Some stk.(frozen_since) ∨ borrow_read_match β bor' stk.(borrows).
Proof.
  rewrite /reborrow. destruct bor' as [|[]].
  - by apply reborrowBlock_read_access_is_freeze.
  - rewrite visit_freeze_sensitive_is_freeze; [|done..].
    by apply reborrowBlock_read_access_is_freeze.
  - by apply reborrowBlock_read_access_is_freeze.
Qed.

Lemma retag_ref_is_freeze_is_Some h α β clk l bor T mut bar (tp: bool)
  (BLK: ∀ n, (n < tsize T)%nat → l +ₗ n ∈ dom (gset loc) h)
  (SUM: ∀ Ts (n: nat), (n, (Sum Ts)) ∈ sub_sum_types T → ∃ i,
          h !! (l +ₗ n) = Some (LitV (LitInt i)) ∧ 0 ≤ i < length Ts)
  (FRZ: is_freeze T)
  (WF: Wf (mkState h α β clk))
  (TP: tp → mut = Some Mutable)
  (BAR : match bar with Some c => is_Some (β !! c) | _ => True end)
  (STK: ∀ m stk, (m < tsize T)%nat → α !! (l +ₗ m) = Some stk →
          match mut with
          | Some Mutable => stk.(frozen_since) = None ∧
              match bor with
              | UniqB _ | AliasB None => borrow_write_match β bor stk.(borrows)
              | _ => False
              end
          | Some Immutable =>
              match bor with
              | UniqB t => Uniq t ∈ stk.(borrows) ∧ borrow_read_match β bor stk.(borrows)
              | AliasB None =>
                  is_Some stk.(frozen_since) ∨ borrow_read_match β bor stk.(borrows)
              | AliasB (Some t) =>
                  match stk.(frozen_since) with
                  | Some t' => (t' ≤ t)%nat
                  | _ => borrow_read_match β bor stk.(borrows)
                  end
              end
          | None => stk.(frozen_since) = None ∧
              match bor with
              | UniqB t => Uniq t ∈ stk.(borrows) ∧ borrow_read_match β bor stk.(borrows)
              | AliasB None => borrow_read_match β bor stk.(borrows)
              | _ => False
              end
          end) :
  is_Some (retag_ref h α β clk l bor T mut bar tp).
Proof.
  rewrite /retag_ref. destruct (tsize T) as [|sT] eqn:Eqs; [by eexists|].
  set bor' := match mut with
              | Some Mutable => UniqB clk
              | Some Immutable => AliasB (Some clk)
              | None => AliasB None
              end.
  destruct (reborrow_is_freeze_is_Some h α β l bor T bar bor')
    as [α1 Eq1]; [..|done|done|].
  { intros ?. rewrite Eqs -(state_wf_dom _ WF). by apply BLK. }
  { intros m stk. rewrite Eqs. intros Lt Eq.
    specialize (STK _ _ Lt Eq). rewrite /bor'. destruct mut as [[]|]; simpl.
    - destruct STK. repeat split; [done| |done].
      intros IN. move : (state_wf_stack_item _ WF _ _ Eq _ IN) => /=. lia.
    - split; [|done].
      move : (state_wf_stack_frozen _ WF _ _ Eq) => /=. rewrite /frozen_lt.
      case frozen_since; [|done]. intros ?. lia.
    - done. }
  rewrite Eq1 /=. destruct tp; [|by eexists]. rewrite TP; [|done].
  rewrite visit_freeze_sensitive_is_freeze; [|done..].
  rewrite /reborrowBlock /=.
  destruct (reborrow_wf_stack h α β (S clk) l bor T bar bor' α1) as [WF1 WF2];
    [|done|done|..].
  { rewrite /bor'. destruct mut as [[]|]; simpl; [lia..|done]. }
  { repeat split; [..|apply WF].
    - eapply wf_stack_frozen_mono; [|apply WF]. simpl. lia.
    - eapply wf_stack_item_mono; [|apply WF]. simpl. lia. }
  destruct (reborrowN_is_Some α1 β l (tsize T) bor' (AliasB (Some (S clk)))
              FrozenRef None) as [α2 Eq2]; [..|by left|].
  { intros ?. rewrite Eqs -WF1 -(state_wf_dom _ WF). apply BLK. }
  { intros m stk Lt Eq. destruct WF2 as (WF2 & WF3 & WF4).
    repeat split; [..|naive_solver].
    - move : Eq1 m stk Lt Eq. by apply reborrow_deref1_is_freeze.
    - move : Eq1 m stk Lt Eq. apply reborrow_read_access_is_freeze; [done..|].
      rewrite Eqs. intros m stk Lt Eq. move : (STK _ _ Lt Eq). rewrite /bor'.
      destruct mut as [[]|]; naive_solver.
    - move : (WF2 _ _ Eq). rewrite /frozen_lt.
      case frozen_since; [intros ?; lia|done]. }
  rewrite Eq2 /=. by eexists.
Qed.

Lemma retag_is_freeze_is_Some h α clk β x kind T
  (REF: ∀ (n: nat) pk Tr, (n, Reference pk Tr) ∈ sub_ref_types T → ∃ l tag,
          h !! (x +ₗ n) = Some (LitV (LitLoc l tag)) ∧ is_freeze Tr)
  (SUM: ∀ Ts (n: nat), (n, (Sum Ts)) ∈ sub_sum_types T → ∃ i,
          h !! (x +ₗ n) = Some (LitV (LitInt i)) ∧ 0 ≤ i < length Ts)
  (WF: Wf (mkState h α β clk))
  (FNBAR : match kind with | FnEntry c => β !! c = Some true | _ => True end) :
  is_Some (retag h α clk β x kind T).
Proof.
  revert REF SUM WF FNBAR.
  apply (retag_elim
    (* general goal P *)
    (λ h α clk β l kind T ohac,
      (∀ (n: nat) pk Tr, (n, Reference pk Tr) ∈ sub_ref_types T → ∃ l0 tag0,
          h !! (l +ₗ n) = Some (LitV (LitLoc l0 tag0)) ∧ is_freeze Tr) →
      (∀ Ts (n: nat), (n, Sum Ts) ∈ sub_sum_types T → ∃ i,
          h !! (l +ₗ n) = Some (LitV (LitInt i)) ∧
          0 ≤ i < length Ts) →
      Wf (mkState h α β clk) →
      (match kind with | FnEntry c => β !! c = Some true | _ => True end) →
      is_Some ohac)
    (λ _ _ _ β _ kind _ h α clk l Ts ohac,
      (∀ (n: nat) pk Tr, (n, Reference pk Tr) ∈ sub_ref_types (Product Ts) → ∃ l0 tag0,
          h !! (l +ₗ n) = Some (LitV (LitLoc l0 tag0)) ∧ is_freeze Tr) →
      (∀ Ts' (n: nat), (n, Sum Ts') ∈ sub_sum_types (Product Ts) → ∃ i,
          h !! (l +ₗ n) = Some (LitV (LitInt i)) ∧
          0 ≤ i < length Ts') →
      Wf (mkState h α β clk) →
      (match kind with | FnEntry c => β !! c = Some true | _ => True end) →
      is_Some ohac)
    (λ h l _ α clk β kind _ Ts n ohac,
      (∀ (n: nat) pk Tr, (n, Reference pk Tr) ∈ sub_ref_types (Sum Ts) → ∃ l0 tag0,
          h !! (l +ₗ n) = Some (LitV (LitLoc l0 tag0)) ∧ is_freeze Tr) →
      (∀ T' Ts' (n: nat), T' ∈ Ts → (n, Sum Ts') ∈ sub_sum_types T' → ∃ i,
          h !! (l +ₗ S n) = Some (LitV (LitInt i)) ∧
          0 ≤ i < length Ts') → (n < length Ts)%nat →
      Wf (mkState h α β clk) →
      (match kind with | FnEntry c => β !! c = Some true | _ => True end) →
      is_Some ohac)).
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - clear. intros h x _ _ _ _ pk T Eq0 REF _ _ _.
    destruct (REF _ _ _ (sub_ref_types_O_elem_of pk T)) as (? & ? & Eq & ?).
    move : Eq. by rewrite shift_loc_0 Eq0.
  - clear. intros h x l tag α clk β rkind pkind T Eq0 REF SUM WF FNBAR.
    have FRZ: is_freeze T. { destruct (REF O pkind T) as (? & ? & ? &?);
                              [apply sub_ref_types_O_elem_of|done]. }
    destruct pkind; simpl.
    + destruct (retag_ref_is_freeze_is_Some h α β clk l tag T
                  (Some mut) (adding_barrier rkind) (is_two_phase rkind))
        as [bac Eq]; [| |done|done|..|rewrite Eq; by eexists].
      * admit.
      * admit.
      * admit.
      * destruct rkind; [by eexists|done..].
      * admit.
    + destruct rkind; [by eexists..| |by eexists].
      destruct (retag_ref_is_freeze_is_Some h α β clk l tag T None None false)
        as [bac Eq]; [| |done..| |rewrite Eq; by eexists].
      * admit.
      * admit.
      * admit.
    + destruct (retag_ref_is_freeze_is_Some h α β clk l tag T
                  (Some Mutable) None (is_two_phase rkind))
        as [bac Eq]; [| |done|done|..|done|done| |rewrite Eq; by eexists].
      * admit.
      * admit.
      * admit.
  - clear. intros h x n _ _ _ _ pk T Eq0 REF _ _ _.
    destruct (REF _ _ _ (sub_ref_types_O_elem_of pk T)) as (? & ? & Eq & ?).
    move : Eq. by rewrite shift_loc_0 Eq0.
  - clear. intros h x ???? _ _ _ _ pk T Eq0 REF _ _ _.
    destruct (REF _ _ _ (sub_ref_types_O_elem_of pk T)) as (? & ? & Eq & ?).
    move : Eq. by rewrite shift_loc_0 Eq0.
  - clear. intros h x _ _ _ _ pk T Eq0 REF _ _ _.
    destruct (REF _ _ _ (sub_ref_types_O_elem_of pk T)) as (? & ? & Eq & ?).
    move : Eq. by rewrite shift_loc_0 Eq0.
  - naive_solver.
  - clear.
    intros h α clk β x kind Ts h1 α1 clk1 x1 T Ts1 IH1 IH2 REF SUM WF FNBAR.
    destruct IH2 as [[[h2 α2] clk2] Eq1]; [..|done|done|].
    { intros ????. by eapply REF, sub_ref_types_product_first. }
    { intros ???. by apply SUM, sub_sum_types_product_first. }
    rewrite Eq1 /=. apply (IH1 ((h2, α2), clk2)); [..|done].
    { intros n pk Tr IN. rewrite /= shift_loc_assoc -Nat2Z.inj_add.
      destruct (REF (tsize T + n)%nat pk Tr) as [l0 [tag0 [Eq0 ?]]].
      - by apply sub_ref_types_product_further.
      - move : Eq1 => /retag_lookup_ref Eq1.
        destruct (Eq1 _ _ Eq0) as [v' []]; [done|].
        destruct v' as [[|l tag|]|]; [done| |done..]. by exists l, tag. }
    { intros Ts' n IN. rewrite /= shift_loc_assoc.
      destruct (SUM Ts' (tsize T + n)%nat) as [i [Eqi Lti]].
      - by apply sub_sum_types_product_further.
      - exists i. split; [|done]. move : Eq1 => /retag_lookup EqL.
        apply EqL; [by rewrite -Nat2Z.inj_add|by intros []]. }
    { eapply retag_wf; eauto. }
  - clear. intros h x _ _ _ _ Ts Eq0 _ SUM _ _.
    destruct (SUM Ts O) as [i [Eq ?]]; [by apply sub_sum_types_O_elem_of|].
    move : Eq. by rewrite shift_loc_0_nat Eq0.
  - clear. intros h x l tag _ _ _ _ Ts Eq0 _ SUM _ _.
    destruct (SUM Ts O) as [i [Eq ?]]; [by apply sub_sum_types_O_elem_of|].
    move : Eq. by rewrite shift_loc_0_nat Eq0.
  - clear. intros h x n α clk β kind Ts IH Eq0 REF SUM WF FNBAR.
    destruct (SUM Ts O) as [i [Eq [Ge0 Lt]]]; [by apply sub_sum_types_O_elem_of|].
    move : Eq. rewrite shift_loc_0_nat Eq0. intros Eq. simplify_eq.
    rewrite decide_True; [|done].
    apply IH; [done|done|..|rewrite -(Nat2Z.id (length Ts)) -Z2Nat.inj_lt; lia
              |done|done].
    intros T' Ts' n IN1 IN2. apply SUM, sub_sum_types_elem_of_2.
    right. split; [lia|]. exists T'. split; [done|]. by rewrite /= Nat.sub_0_r.
  - clear. intros h x f xl e ? _ _ _ _ Ts Eq0 _ SUM _ _.
    destruct (SUM Ts O) as [i [Eq ?]]; [by apply sub_sum_types_O_elem_of|].
    move : Eq. by rewrite shift_loc_0_nat Eq0.
  - clear. intros h x _ _ _ _ Ts Eq0 _ SUM _ _.
    destruct (SUM Ts O) as [i [Eq ?]]; [by apply sub_sum_types_O_elem_of|].
    move : Eq. by rewrite shift_loc_0_nat Eq0.
  - clear. intros h x _ _ _ _ _ _ i _ _ Lt _ _. simpl in Lt. lia.
  - clear. intros h x _ α clk β kind _ T Ts IH REF SUM Lt WF FNBAR.
    apply IH; [..|done|done].
    + intros n pk Tr IN. rewrite shift_loc_assoc -(Nat2Z.inj_add 1 n) Nat.add_1_l.
      by eapply REF, sub_ref_types_sum_first.
    + intros Ts' n IN. rewrite shift_loc_assoc -(Nat2Z.inj_add 1 n) Nat.add_1_l.
      apply (SUM T); [by left|done].
  - clear. intros h x ii α clk β kind Ts0 T Ts i IH REF SUM Lt WF FNBAR.
    apply IH; [..|done|done].
    + intros ????. by eapply REF, sub_ref_types_sum_further.
    + intros ?? n IN. apply SUM. by right.
    + move : Lt => /=. lia.
Abort.

Lemma retag_head_step σ x xbor T kind (call: Z) (Gt0: 0 ≤ call)
  (BAR: match kind with
        | FnEntry _ => σ.(cbar) !! (Z.to_nat call) = Some true
        | _ => True
        end) :
  ∃ σ' kind',
  head_step (Retag (Place x xbor T) kind #call) σ [RetagEvt x T kind'] #☠ σ' [].
Proof.
  eexists.
  exists (match kind with FnEntry _ => FnEntry (Z.to_nat call) | _ => kind end).
  econstructor. { econstructor; eauto. destruct kind; auto. naive_solver. }
  econstructor. { by destruct kind. }
Abort.

Lemma syscall_head_step σ id :
  head_step (SysCall id) σ [SysCallEvt id] #☠ σ [].
Proof.
  have EE: ∃ σ', head_step (SysCall id) σ [SysCallEvt id] #☠ σ' [] ∧ σ' = σ.
  { eexists. split. econstructor; econstructor. by destruct σ. }
  destruct EE as [? [? ?]]. by subst.
Qed.
