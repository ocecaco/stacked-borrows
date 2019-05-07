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
  head_step (Alloc T) σ [AllocEvt l (Tagged t) T] (Place l (Tagged t) T) σ' [].
Proof.
  eexists. econstructor; econstructor.
  intros. by apply (not_elem_of_dom (D:=gset loc)), is_fresh_block.
Qed.

Lemma find_granting_is_Some stk kind bor
  (BOR: ∃ it, it ∈ stk ∧ it.(tg) = bor ∧
              (kind = AccessWrite → it.(perm) ≠ SharedReadOnly)) :
  is_Some (find_granting stk kind bor).
Proof.
  destruct BOR as [it [IN [Eq KD]]].
  destruct (list_find_elem_of (matched_grant kind bor) stk it IN)
    as [it1 Eq1].
  - split; [|done]. destruct it.(perm), kind; try done. naive_solver.
  - rewrite /find_granting Eq1. by eexists.
Qed.

Lemma dealloc1_progress stk bor β
  (PR: Forall (λ it, ¬ is_active_protector β it) stk)
  (BOR: ∃ it, it ∈ stk ∧ it.(tg) = bor ∧ it.(perm) ≠ SharedReadOnly) :
  is_Some (dealloc1 stk bor β).
Proof.
  rewrite /dealloc1.
  destruct (find_granting_is_Some stk AccessWrite bor) as [? Eq]; [naive_solver|].
  rewrite Eq /find_top_active_protector list_find_None_inv;
    [by eexists|done].
Qed.

Lemma for_each_is_Some α l (n: nat) b f :
  (∀ m : Z, 0 ≤ m ∧ m < n → l +ₗ m ∈ dom (gset loc) α) →
  (∀ (m: nat) stk, (m < n)%nat → α !! (l +ₗ m) = Some stk → is_Some (f stk)) →
  is_Some (for_each α l n b f).
Proof.
  revert α. induction n as [|n IHn]; intros α IN Hf; [by eexists|]. simpl.
  assert (is_Some (α !! (l +ₗ n))) as [stk Eq].
  { apply (elem_of_dom (D:=gset loc)), IN. by lia. }
  rewrite Eq /=. destruct (Hf n stk) as [stk' Eq']; [lia|done|].
  rewrite Eq' /=. destruct b; apply IHn.
  - intros. apply elem_of_dom. rewrite lookup_delete_ne.
    + apply (elem_of_dom (D:=gset loc)), IN. lia.
    + move => /shift_loc_inj. lia.
  - intros ???. rewrite lookup_delete_ne.
    + apply Hf. lia.
    + move => /shift_loc_inj. lia.
  - intros. apply elem_of_dom. rewrite lookup_insert_ne.
    + apply (elem_of_dom (D:=gset loc)), IN. lia.
    + move => /shift_loc_inj. lia.
  - intros ???. rewrite lookup_insert_ne.
    + apply Hf. lia.
    + move => /shift_loc_inj. lia.
Qed.

Lemma memory_deallocated_progress α β l bor (n: nat) :
  (∀ m : Z, 0 ≤ m ∧ m < n → l +ₗ m ∈ dom (gset loc) α) →
  (∀ (m: nat) stk, (m < n)%nat → α !! (l +ₗ m) = Some stk →
      (∃ it, it ∈ stk ∧ it.(tg) = bor ∧ it.(perm) ≠ SharedReadOnly) ∧
      ∀ it, it ∈ stk →
      match it.(protector) with Some c => β !! c = Some false | _ => True end) →
  is_Some (memory_deallocated α β l bor n).
Proof.
  intros IN IT. apply for_each_is_Some; [done|].
  intros m stk Lt Eq. destruct (IT _ _ Lt Eq) as [In PR].
  destruct (dealloc1_progress stk bor β) as [? Eq1];
    [|done|rewrite Eq1; by eexists].
  apply Forall_forall. move => it /PR. rewrite /is_active_protector.
  case protector; naive_solver.
Qed.

Lemma dealloc_head_step (σ: state) T l bor
  (WF: Wf σ)
  (BLK: ∀ m : Z, l +ₗ m ∈ dom (gset loc) σ.(cheap) ↔ 0 ≤ m ∧ m < tsize T)
  (BOR: ∀ (n: nat) stk, (n < tsize T)%nat →
    σ.(cstk) !! (l +ₗ n) = Some stk →
    (∃ it, it ∈ stk ∧ it.(tg) = bor ∧ it.(perm) ≠ SharedReadOnly) ∧
      ∀ it, it ∈ stk →
      match it.(protector) with Some c => σ.(cpro) !! c = Some false | _ => True end) :
  ∃ σ',
  head_step (Free (Place l bor T)) σ [DeallocEvt l bor T] #☠ σ' [].
Proof.
  destruct (memory_deallocated_progress σ.(cstk) σ.(cpro) l bor (tsize T))
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

Lemma rm_incompat_is_Some β stk pm kind :
  (∀ it, it ∈ stk → ∃ b, compatible_with pm kind it.(perm) = Some b ∧
      if b then True
      else match it.(protector) with | Some c => ¬ is_active β c | _ => True end) →
  is_Some (rm_incompat β stk pm kind).
Proof.
  induction stk as [|it stk IH]; [by eexists|]. intros IT. simpl.
  destruct IH as [stk2 Eq2]. { intros ? IN. apply IT. by right. }
  rewrite Eq2 /=.
  destruct (IT it) as [b [Eqb PR]]; [by left|].
  rewrite Eqb /=. destruct b; [by eexists|]. move : PR.
  case protector => ?; [|by eexists].
  move => /negb_prop_intro /Is_true_eq_true /negb_true_iff ->. by eexists.
Qed.

Lemma grants_read_all pm: grants pm AccessRead.
Proof. by case pm. Qed.
Lemma grants_write_all pm: pm ≠ SharedReadOnly → grants pm AccessWrite.
Proof. by case pm. Qed.

Definition item_inactive_protector β (it: item) :=
  match it.(protector) with Some c => ¬ is_active β c | _ => True end.

Definition is_write (access: access_kind) :=
  match access with AccessWrite => true | _ => false end.

Definition access1_pre
  (β: protectors) (stk: stack) (kind: access_kind) (bor: tag) :=
  ∃ (i: nat) it, stk !! i = Some it ∧ it.(tg) = bor ∧
    (is_write kind → it.(perm) ≠ SharedReadOnly) ∧
  ∀ (j: nat) jt, (j < i)%nat → stk !! j = Some jt →
    (if is_write kind then jt.(perm) = SharedReadOnly ∨ jt.(tg) ≠ bor
     else jt.(tg) ≠ bor) ∧
    match it.(perm) with
    | SharedReadOnly => jt.(perm) = SharedReadOnly ∧
        (is_write kind → item_inactive_protector β jt)
    | Unique =>
        (is_write kind ∨ jt.(perm) = Unique) → item_inactive_protector β jt
    | SharedReadWrite =>
        (is_write kind ∧ jt.(perm) ≠ SharedReadWrite ∨ jt.(perm) = Unique) →
        item_inactive_protector β jt
    end.

Definition access1_read_pre (β: protectors) (stk: stack) (bor: tag) :=
  ∃ (i: nat) it, stk !! i = Some it ∧ it.(tg) = bor ∧
  ∀ (j: nat) jt, (j < i)%nat → stk !! j = Some jt →
    jt.(tg) ≠ bor ∧
    match it.(perm) with
    | SharedReadOnly => jt.(perm) = SharedReadOnly
    | _ => match jt.(perm), jt.(protector) with
           | Unique, Some c => ¬ is_active β c
           | _, _ => True
           end
    end.

Definition access1_write_pre (β: protectors) (stk: stack) (bor: tag) :=
  ∃ (i: nat) it, stk !! i = Some it ∧ it.(perm) ≠ SharedReadOnly ∧ it.(tg) = bor ∧
  ∀ (j: nat) jt, (j < i)%nat → stk !! j = Some jt →
    (jt.(perm) = SharedReadOnly ∨ jt.(tg) ≠ bor) ∧
    match it.(perm) with
    | Unique => match jt.(protector) with Some c => ¬ is_active β c | _ => True end
    | SharedReadWrite =>
        jt.(perm) ≠ SharedReadWrite →
        match jt.(protector) with Some c => ¬ is_active β c | _ => True end
    | SharedReadOnly => jt.(perm) = SharedReadOnly ∧
        match jt.(protector) with Some c => ¬ is_active β c | _ => True end
    end.

Lemma access1_is_Some β stk kind bor
  (BOR: access1_pre β stk kind bor) :
  is_Some (access1 stk kind bor β).
Proof.
  destruct BOR as (i & it & Eqi & Eqit & IW & Lti).
  rewrite /access1 /find_granting.
  rewrite (_: list_find (matched_grant kind bor) stk = Some (i, it)); last first.
  { apply list_find_Some_not_earlier. split; last split; [done|..].
    - split; [|done].
      destruct kind; [apply grants_read_all|by apply grants_write_all, IW].
    - intros ?? Lt Eq GR. destruct (Lti _ _ Lt Eq) as [NEq1 NEq2].
      destruct kind; [by apply NEq1, GR|]. destruct NEq1 as [OR|OR].
      + move : GR. rewrite /matched_grant OR /=. naive_solver.
      + by apply OR, GR. } simpl.
  destruct (rm_incompat_is_Some β (take i stk) it.(perm) kind) as [? Eq2];
    [|rewrite Eq2 /=; by eexists].
  intros jt [j Eqj]%elem_of_list_lookup_1.
  have ?: (i ≤ length stk)%nat. { by eapply Nat.lt_le_incl, lookup_lt_Some. }
  have ?: (j < i)%nat.
  { rewrite -(take_length_le stk i); [|done]. by eapply lookup_lt_Some. }
  destruct (Lti j jt) as [Eq1 PR]; [done|..].
  - symmetry. by rewrite -Eqj lookup_take.
  - move : PR. rewrite /compatible_with.
    case it.(perm); case jt.(perm); destruct kind; naive_solver.
Qed.

Lemma access1_read_is_Some β stk bor
  (BOR: access1_read_pre β stk bor) :
  is_Some (access1 stk AccessRead bor β).
Proof.
  destruct BOR as (i & it & Eqi & Eqit & Lti).
  apply access1_is_Some. exists i, it. do 3 (split; [done|]).
  intros j jt Lt Eq. destruct (Lti _ _ Lt Eq) as [? PR]. split; [done|].
  move : PR. case perm; [..|naive_solver]; case perm; naive_solver.
Qed.

Lemma memory_read_is_Some α β l bor (n: nat) :
  (∀ m, (m < n)%nat → l +ₗ m ∈ dom (gset loc) α) →
  (∀ (m: nat) stk, (m < n)%nat →
    α !! (l +ₗ m) = Some stk → access1_read_pre β stk bor) →
  is_Some (memory_read α β l bor n).
Proof.
  intros IN STK. apply for_each_is_Some.
  - intros m []. rewrite -(Z2Nat.id m); [|done]. apply IN.
    rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; [done..|lia].
  - intros m stk Lt Eq.
    specialize (STK _ _ Lt Eq).
    destruct (access1_read_is_Some _ _ _ STK) as [? Eq2]. rewrite Eq2. by eexists.
Qed.

Lemma copy_head_step (σ: state) l bor T
  (WF: Wf σ)
  (BLK: ∀ n, (n < tsize T)%nat → l +ₗ n ∈ dom (gset loc) σ.(cheap))
  (BOR: ∀ m stk, (m < tsize T)%nat → σ.(cstk) !! (l +ₗ m) = Some stk →
        access1_read_pre σ.(cpro) stk bor) :
  ∃ σ' vl,
  head_step (Copy (Place l bor T)) σ
            [CopyEvt l bor T vl] (of_val (TValV vl)) σ' [].
Proof.
  destruct (read_mem_is_Some _ _ _ BLK) as [vl RM].
  destruct (memory_read_is_Some σ.(cstk) σ.(cpro) l bor (tsize T));[|done|].
  { move => ? /BLK. by rewrite (state_wf_dom _ WF). }
  do 2 eexists. econstructor; econstructor; [done..|].
  move => l1 bor1 /elem_of_list_lookup [i Eqi].
  apply (state_wf_mem_tag _ WF (l +ₗ i) l1).
  destruct (read_mem_values _ _ _ _ RM) as [Eq1 Eq2].
  rewrite Eq2; [done|]. rewrite -Eq1. by eapply lookup_lt_Some.
Qed.

Lemma access1_write_is_Some β stk bor
  (BOR: access1_write_pre β stk bor) :
  is_Some (access1 stk AccessWrite bor β).
Proof.
  destruct BOR as (i & it & Eqi & Neqi & Eqit & Lti).
  apply access1_is_Some. exists i, it. do 3 (split; [done|]).
  intros j jt Lt Eq. destruct (Lti _ _ Lt Eq) as [? PR]. split; [done|].
  move : PR. case perm; [..|naive_solver]; case perm; naive_solver.
Qed.

Lemma memory_written_is_Some α β l bor (n: nat) :
  (∀ m, (m < n)%nat → l +ₗ m ∈ dom (gset loc) α) →
  (∀ (m: nat) stk, (m < n)%nat →
    α !! (l +ₗ m) = Some stk → access1_write_pre β stk bor) →
  is_Some (memory_written α β l bor n).
Proof.
  intros IN STK. apply for_each_is_Some.
  - intros m []. rewrite -(Z2Nat.id m); [|done]. apply IN.
    rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; [done..|lia].
  - intros m stk Lt Eq.
    specialize (STK _ _ Lt Eq).
    destruct (access1_write_is_Some _ _ _ STK) as [? Eq2]. rewrite Eq2. by eexists.
Qed.

Lemma write_head_step (σ: state) l bor T el vl
  (WF: Wf σ)
  (LEN: length vl = tsize T)
  (VALUES: to_val (TVal el) = Some (TValV vl))
  (LOCVAL: vl <<b σ.(cclk))
  (BLK: ∀ n, (n < tsize T)%nat → l +ₗ n ∈ dom (gset loc) σ.(cheap))
  (STK: ∀ m stk, (m < tsize T)%nat → σ.(cstk) !! (l +ₗ m) = Some stk →
        access1_write_pre σ.(cpro) stk bor) :
  ∃ σ',
  head_step (Write (Place l bor T) (TVal el)) σ
            [WriteEvt l bor T vl] #☠ σ' [].
Proof.
  destruct (memory_written_is_Some σ.(cstk) σ.(cpro) l bor (tsize T)); [|done|].
  { move => ? /BLK. by rewrite (state_wf_dom _ WF). }
  eexists. econstructor; econstructor; [done|by rewrite LEN|done..].
Qed.


Lemma newcall_head_step σ :
  let c := fresh (dom (gset call_id) σ.(cpro)) in
  ∃ σ', head_step NewCall σ [NewCallEvt c] (Lit $ LitInt c) σ' [].
Proof. eexists. econstructor; econstructor. Qed.


Lemma endcall_head_step σ c (NZ: 0 ≤ c)
  (BAR: σ.(cpro) !! (Z.to_nat c) = Some true) :
  ∃ σ',
  head_step (EndCall #c) σ [EndCallEvt (Z.to_nat c)] #☠ σ' [].
Proof. eexists. econstructor; econstructor. lia. done. Qed.


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
    (λ _ _ _ _ l1 c1 _ Ts i oalc, ∀ a2 l2 c2,
      oalc = Some (a2, (l2, c2)) → ∃ T1, Ts !! i = Some T1 ∧
      (l1 ≤ l2 ∧ l2 + c2 = l1 + S c1 + tsize T1)%nat)); rewrite /HA.
  - intros. simplify_eq. simpl. lia.
  - intros. simplify_eq. simpl. lia.
  - clear. intros _ ????????? [??]%unsafe_action_offsets. subst. simpl. lia.
  - clear. intros _ ?????????. case is_freeze.
    + intros. simplify_eq. lia.
    + intros [??]%unsafe_action_offsets. subst. lia.
  - clear. intros ??????? IH ???.
    case is_freeze; [intros; simplify_eq; lia|by move => /IH].
  - clear. intros ???? l1 c1 ? IH ???.
    case is_freeze; [intros; simplify_eq; lia|].
    case lookup => [[[//|//|i]|//]|//].
    case decide => [Ge0|//].
    case visit_freeze_sensitive'_clause_6_visit_lookup
      as [[? [l3 c3]]|] eqn:Eq1; [simpl|done].
    intros. simplify_eq.
    destruct (IH (LitV LitPoison) LitPoison _ Ge0 _ _ _ Eq1) as (T1&HL&Le&Eq).
    split; [done|]. rewrite le_plus_minus_r; [done|].
    etrans; [apply (le_plus_l _ c3)|]. rewrite Eq.
    rewrite (_: l1 + S c1 + tsize T1 = l1 + c1 + S (tsize T1))%nat; [|lia].
    by eapply plus_le_compat_l, tsize_subtype_of_sum, elem_of_list_lookup_2.
  - naive_solver.
  - clear. intros h l f a1 l1 c1 Ts a2 l2 c2 T Ts' IH1 IH2 a4 l4 c4.
    case visit_freeze_sensitive' as [[a3 [l3 c3]]|] eqn:Eq3; [|done].
    cbn -[tsize].
    destruct (IH2 a3 l3 c3) as [Le3 EqO3]; [done|].
    intros Eq4. destruct (IH1 (a3, (l3, c3)) a4 l4 c4 Eq4) as [Le4 EqO4].
    clear -Le3 EqO3 Le4 EqO4. simpl in Le4. rewrite EqO4. cbn -[tsize].
    rewrite EqO3 tsize_product_cons. lia.
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
    (λ h l f a last cur_dist _ Ts n oalc,
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
  - clear. intros h l f a last cur_dist Ts IH Hf SUM HI.
    case is_freeze; [intros; simplify_eq; exists a, last; by eexists|by apply IH].
  - clear. intros ??? a l1 c1 Ts IH Hf SUM HI.
    case is_freeze; [intros; simplify_eq; exists a, l1; by eexists|].
    destruct (SUM Ts O) as [i [Eq [Ge0 Lti]]]; [by apply sub_sum_types_O_elem_of|].
    move : Eq. rewrite shift_loc_0_nat => Eq. rewrite Eq decide_True; [|done].
    destruct (IH (LitV LitPoison) LitPoison _ Ge0) as (a2&l2&c2&Eq1&HI2);
      [done|..|done|].
    { intros T' Ts' n IN SUB. apply SUM, sub_sum_types_elem_of_2. right.
      split; [lia|]. exists T'. split; [done|]. by rewrite Nat.sub_1_r. }
    { rewrite -(Nat2Z.id (length Ts)) -Z2Nat.inj_lt; [done..|lia]. }
    rewrite Eq1 /=. exists a2, l2. by eexists.
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
  - clear. intros ?????? _ i _ _. simpl. lia.
  - clear. intros h l f a l1 c1 _ T Ts IH Hf SUM _. apply IH.
    + intros ???? [? Le]. apply Hf. split; [done|].
      etrans; [apply Le|]. rewrite -Nat.add_assoc plus_Snm_nSm Nat.add_assoc.
      apply (plus_le_compat_l _ _ (l1 + c1)), tsize_subtype_of_sum. by left.
    + intros ?? IN.
      rewrite (_: l +ₗ (l1 + S c1) +ₗ n = l +ₗ (l1 + c1) +ₗ S n); last first.
      { rewrite 2!shift_loc_assoc. f_equal. lia. }
      apply (SUM T); [by left|done].
  - clear. intros h l f a l1 c1 Ts0 T Ts i IH Hf SUM Lt. apply IH.
    + intros ???? [? Le]. apply Hf. split; [done|]. etrans; [apply Le|].
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
    clear. intros h  x l bor α clk β rt_kind p_kind T Eq h' α' clk'.
    destruct p_kind as [[]|[]|];
      [| |destruct rt_kind; try by (intros; simplify_eq)..|];
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
    (∀ l v, h !! l = Some v →
      is_loc_val v → ∃ v', h' !! l = Some v' ∧ is_loc_val v') in
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
    clear. intros h x ? bor α clk β rt_kind p_kind T Eq h' α' clk'.
    destruct p_kind as [[]|[]|];
      [| |destruct rt_kind; try by (intros; simplify_eq; naive_solver)..|];
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

Lemma access1_find_granting_agree stk kind bor β i1 i2 pm1 stk2:
  find_granting stk kind bor = Some (i1, pm1) →
  access1 stk kind bor β = Some (i2, stk2) →
  i1 = i2.
Proof.
  intros FI. rewrite /access1 FI /=.
  case rm_incompat => [? /= ?|//]. by simplify_eq.
Qed.

Lemma reborrow1_is_Some stk old weak new β
  (WEAK: if weak : bool then new.(perm) ≠ SharedReadOnly else True) :
  let access :=
    if grants new.(perm) AccessWrite then AccessWrite else AccessRead in
  access1_pre β stk access old →
  is_Some (reborrow1 stk old weak new β).
Proof.
  intros access ACC. rewrite /reborrow1.
  destruct (find_granting_is_Some stk access old) as [[i pi] Eqi].
  { destruct ACC as (i & it & Eqi & Eqt & NEq & Lt).
    exists it. split; [by eapply elem_of_list_lookup_2|].
    split; [done|]. intros Eqa. apply NEq. by rewrite Eqa. }
  rewrite Eqi. cbn -[item_insert_dedup].
  destruct weak; [rewrite decide_False //; by eexists|].
  destruct (access1_is_Some _ _ _ _ ACC) as [[i' stk'] Eq].
  rewrite Eq. cbn -[item_insert_dedup]. rewrite decide_True; [by eexists|].
  symmetry. by eapply access1_find_granting_agree.
Qed.

Lemma reborrowN_is_Some α β l n old new pm fweak protector
  (BLK: ∀ m, (m < n)%nat → l +ₗ m ∈ dom (gset loc) α)
  (FW: if fweak : bool then pm ≠ SharedReadOnly else True) :
  let access := if grants pm AccessWrite then AccessWrite else AccessRead in
  (∀ (m: nat) stk, (m < n)%nat → α !! (l +ₗ m) = Some stk →
    access1_pre β stk access old) →
  is_Some (reborrowN α β l n old new pm fweak protector).
Proof.
  intros access STK.
  rewrite /reborrowN. apply for_each_is_Some.
  - intros m []. rewrite -(Z2Nat.id m); [|done]. apply BLK.
    rewrite -(Nat2Z.id n) -Z2Nat.inj_lt; [done..|lia].
  - intros m stk Lt Eq. apply reborrow1_is_Some; [|by apply (STK _ _ Lt Eq)].
    simpl. case (decide (pm = SharedReadWrite)) => [Eqp|NEqp].
    + by rewrite bool_decide_true // orb_true_r Eqp.
    + by rewrite bool_decide_false // orb_false_r.
Qed.

Lemma reborrowN_lookup (α1 α2 : stacks) β l n old new pm fweak protector
  (EQB : reborrowN α1 β l n old new pm fweak protector = Some α2) :
  (∀ m, (n ≤ m)%nat → α2 !! (l +ₗ m) = α1 !! (l +ₗ m)) ∧
  (∀ m stk, (m < n)%nat → α1 !! (l +ₗ m) = Some stk →
    ∃ stk', α2 !! (l +ₗ m) = Some stk' ∧
    let weak := bool_decide (pm = SharedReadWrite) in
    let item := mkItem pm new protector in
    reborrow1 stk old (fweak || weak) item β = Some stk') ∧
  (∀ m stk', (m < n)%nat → α2 !! (l +ₗ m) = Some stk' →
    ∃ stk, α1 !! (l +ₗ m) = Some stk ∧
    let weak := bool_decide (pm = SharedReadWrite) in
    let item := mkItem pm new protector in
    reborrow1 stk old (fweak || weak) item β = Some stk').
Proof.
  destruct (for_each_lookup _ _ _ _ _ EQB) as [HL1 [HL2 HL3]]. split; last split.
  - intros m Ge. apply HL3. intros i Lt Eq%shift_loc_inj. subst. lia.
  - by apply HL1.
  - by apply HL2.
Qed.

Lemma visit_freeze_sensitive'_is_freeze {A}
  h l (f: A → _ → nat → _ → _) a (last cur_dist: nat) T :
  is_freeze T →
  visit_freeze_sensitive' h l f a last cur_dist T
    = Some (a, (last, (cur_dist + tsize T)%nat)).
Proof.
  apply (visit_freeze_sensitive'_elim
    (* general goal P *)
    (λ h l f a last cur_dist T oalc,
      is_freeze T → oalc = Some (a, (last, (cur_dist + tsize T)%nat)))
    (λ h l f _ _ _ _ a last cur_dist Ts oalc,
      is_freeze (Product Ts) →
      oalc = Some (a, (last, (cur_dist + tsize (Product Ts))%nat)))
    (λ h l f a last cur_dist _ Ts n oalc,
      (n < length Ts)%nat →
      is_freeze (Sum Ts) → ∃ T, Ts !! n = Some T ∧
      oalc = Some (a, (last, (cur_dist + S (tsize T))%nat)))).
  - done.
  - clear. intros ???????? _. by rewrite /= Nat.add_1_r.
  - done.
  - clear. intros ???????. by move => /Is_true_eq_true ->.
  - clear. intros ??????? _. by move => /Is_true_eq_true ->.
  - clear. intros ??????? _. by move => /Is_true_eq_true ->.
  - clear. intros ?? _ _ _ _ _ ??? _. by rewrite /= Nat.add_0_r.
  - clear. intros h l f a last cur_dist Ts a' l1 c1 T Ts' IH1 IH2 FRZ.
    rewrite IH2; first rewrite /= (IH1 (a', (l1, c1 + tsize T)%nat)).
    + simpl. do 3 f_equal. change (tsize T) with (0 + tsize T)%nat.
      rewrite -(foldl_fmap_shift_init _ (λ n, n + tsize T)%nat);
        [by lia|intros ?? _; by lia].
    + by eapply is_freeze_cons_product_inv.
    + by eapply is_freeze_cons_product_inv.
  - clear. intros ?????? _ i. simpl. lia.
  - clear. intros h l f a l1 c1 _ T Ts IH _ FRZ. rewrite IH.
    + exists T. split; [done|]. do 3 f_equal. lia.
    + by eapply is_freeze_cons_sum_inv.
  - clear. intros h l f a l1 c1 Ts0 T Ts i IH Lt FRZ. apply IH.
    + move : Lt => /=. lia.
    + by eapply is_freeze_cons_sum_inv.
Qed.

Lemma visit_freeze_sensitive_is_freeze {A}
  h l (f: A → _ → nat → _ → _) a T :
  is_freeze T → visit_freeze_sensitive h l T f a = f a l (tsize T) true.
Proof.
  intros FRZ. rewrite /visit_freeze_sensitive visit_freeze_sensitive'_is_freeze;
    [by rewrite shift_loc_0_nat Nat.add_0_l|done].
Qed.

Lemma reborrow_is_freeze_is_Some h α β l old T kind new fweak prot
  (BLK: ∀ m, (m < tsize T)%nat → l +ₗ m ∈ dom (gset loc) α)
  (ACC: match kind with
        | SharedRef | RawRef false => fweak = false
        | _ => True
        end)
  (FRZ: is_freeze T)
  (STK: ∀ m stk, (m < tsize T)%nat → α !! (l +ₗ m) = Some stk →
    let access := match kind with
                  | SharedRef | RawRef false => AccessRead
                  | _ => AccessWrite
                  end in access1_pre β stk access old) :
  is_Some (reborrow h α β l old T kind new fweak prot).
Proof.
  rewrite /reborrow. destruct kind as [| |[]].
  - apply reborrowN_is_Some; [done|by destruct fweak|done].
  - rewrite visit_freeze_sensitive_is_freeze //. subst.
    by apply reborrowN_is_Some.
  - apply reborrowN_is_Some; [done|by destruct fweak|done].
  - rewrite visit_freeze_sensitive_is_freeze //. subst.
    by apply reborrowN_is_Some.
Qed.

Lemma reborrow_is_freeze_lookup h α β l old T kind new fweak prot α'
  (FRZ: is_freeze T) :
  reborrow h α β l old T kind new fweak prot = Some α' →
  ∀ m stk', (m < tsize T)%nat → α' !! (l +ₗ m) = Some stk' →
  ∃ stk, α !! (l +ₗ m) = Some stk ∧
  let pm := match kind with
                        | SharedRef | RawRef false => SharedReadOnly
                        | UniqueRef => Unique
                        | RawRef true => SharedReadWrite
                        end in
  let weak := bool_decide (pm = SharedReadWrite) in
  let item := mkItem pm new prot in
  reborrow1 stk old (fweak || weak) item β = Some stk'.
Proof.
  rewrite /reborrow. destruct kind as [| |[]]; intros EQB m stk' Lt Eq'.
  - apply reborrowN_lookup in EQB as [_ [_ HL]]. by apply HL.
  - move : EQB. rewrite visit_freeze_sensitive_is_freeze; [|done].
    move => /reborrowN_lookup [_ [_ HL]]. by apply HL.
  - apply reborrowN_lookup in EQB as [_ [_ HL]]. by apply HL.
  - move : EQB. rewrite visit_freeze_sensitive_is_freeze; [|done].
    move => /reborrowN_lookup [_ [_ HL]]. by apply HL.
Qed.

Lemma item_insert_dedup_lookup stk it i (IS: is_Some (stk !! i)):
  ∃ j, (item_insert_dedup stk it i) !! j = Some it ∧
    (j = i ∨ (1 ≤ i ∧ j = i - 1)%nat) ∧
    (∀ j', (j' < j)%nat → (item_insert_dedup stk it i) !! j' = stk !! j').
Proof.
  destruct i as [|i]; simpl.
  - destruct stk as [|it' stk']; [by destruct IS|]. case decide => [->|?].
    + exists O. naive_solver.
    + exists O. split; [done|]. split;[by left| intros; lia].
  - destruct IS as [it1 Eq1]. rewrite Eq1.
    destruct (stk !! i) as [it2|] eqn:Eq2; last first.
    { apply lookup_ge_None_1 in Eq2. apply lookup_lt_Some in Eq1. lia. }
    case decide => [->|?]; [|case decide => [->|?]].
    + exists i. split; [done|]. rewrite Nat.sub_0_r. split; [right; lia|done].
    + exists (S i). split; [done|]. split; [by left|done].
    + exists i. rewrite Nat.sub_0_r. split; last split; [|right; lia|].
      * rewrite list_lookup_middle // take_length_le //.
        by eapply Nat.lt_le_incl, lookup_lt_Some.
      * intros j' Lt'. rewrite lookup_app_l; [apply lookup_take; lia|].
        rewrite take_length_le //. by eapply Nat.lt_le_incl, lookup_lt_Some.
Qed.

Lemma find_granting_Some stk kind bor i pi :
  find_granting stk kind bor = Some (i, pi) →
  is_Some (stk !! i) ∧
  ∀ j jt, (j < i)%nat → stk !! j = Some jt →
  ¬ (grants jt.(perm) kind ∧ jt.(tg) = bor).
Proof.
  move => /fmap_Some [[i' pi'] [/list_find_Some_not_earlier [Eq1 [MG LT]] Eq2]].
  simplify_eq. simpl. split; [by eexists|by apply LT].
Qed.

Lemma item_insert_dedup_elem_of stk it i (IS: is_Some (stk !! i)):
  it ∈ item_insert_dedup stk it i.
Proof.
  destruct IS as [? Eq1]. destruct i as [|i]; simpl.
  - destruct stk; [|case decide]; set_solver.
  - destruct (stk !! i) as [it2|] eqn:Eq2; last first.
    { apply lookup_ge_None_1 in Eq2. apply lookup_lt_Some in Eq1. lia. }
    rewrite Eq1. case decide => [->|_]; [|case decide => [->|_]].
    + by eapply elem_of_list_lookup_2.
    + by eapply elem_of_list_lookup_2. 
    + set_solver.
Qed.

Lemma reborrow1_new_lookup stk old weak new β stk1 :
  reborrow1 stk old weak new β = Some stk1 →
  ∀ i pi,
  let access := if grants new.(perm) AccessWrite then AccessWrite else AccessRead in
  list_find (matched_grant access old) stk = Some (i, pi) →
  ∃ j, stk1 !! j = Some new ∧ (j ≤ i)%nat ∧
    (∀ j', (j' < j)%nat → stk1 !! j' = stk !! j').
Proof.
  intros RB i pi access HF. move : RB.
  rewrite /reborrow1 /find_granting HF. cbn -[item_insert_dedup].
  apply list_find_Some in HF as [HF1 MG1].
  destruct weak.
  - case decide => ? ; [done|]. intros. simplify_eq.
    destruct (item_insert_dedup_lookup stk new i)
      as (j & ? & Eqj & ?); [by eexists|].
    exists j. split; [done|]. split; [destruct Eqj as [|[]]; subst j; lia|done].
  - case access1 as [[i' stk']|] eqn:Eq1; [|done]. cbn -[item_insert_dedup].
    case decide => ?; [|done]. intros Eq0. subst i'.
    rewrite (_: stk1 = item_insert_dedup stk' new 0); [|by inversion Eq0].
    exists O. split; last split; [|lia|intros;lia].
    destruct (item_insert_dedup_lookup stk' new O)
      as (j & ? & Eqj & ?).
    + apply lookup_lt_is_Some_2. destruct stk'; [|simpl; lia].
      by apply access1_non_empty in Eq1.
    + destruct Eqj as [|[]]; subst j; [done|lia].
Qed.

Lemma reborrow1_new_elem_of stk old weak it β stk1 :
  reborrow1 stk old weak it β = Some stk1 → it ∈ stk1.
Proof.
  intros RB. have RB' := reborrow1_new_lookup _ _ _ _ _ _ RB.
  move : RB.
  rewrite /reborrow1. case find_granting as [[i pi]|] eqn:Eq1; [|done].
  intros _. apply fmap_Some in Eq1 as [[i' pi'] [Eq1 Eq2]]. simplify_eq.
  destruct (RB' _ _ Eq1) as [j [Eqj ?]]. by eapply elem_of_list_lookup_2. 
Qed.

Lemma access1_write_Some β stk old i pi stk' :
  find_granting stk AccessWrite old = Some (i, pi) →
  access1 stk AccessWrite old β = Some (i, stk') →
  ∃ j jt, stk' !! j = Some jt ∧ matched_grant AccessWrite old jt ∧
  (∀ j1 jt1, (j1 < j)%nat → stk' !! j1 = Some jt1 →
    ¬ matched_grant AccessWrite old jt ∧
    compatible_with jt.(perm) AccessWrite jt1.(perm) = Some true ∧
    ∃ j1', stk !! j1' = Some jt1 ∧ (j1' < i)%nat).
Proof.
  intros FG. rewrite /access1 FG /=.
  case rm_incompat as [stk1|] eqn:Eq1; [|done]. simpl. intros. simplify_eq.
  apply fmap_Some in FG as [[i' pi'] [Eq%list_find_Some_not_earlier Eqi']].
  simpl in Eqi'. simplify_eq. destruct Eq as [Eq [MG LT]].
  exists (length stk1), pi'. split; last split; [|done|].
  { by rewrite lookup_app_r // Nat.sub_diag lookup_drop Nat.add_0_r. }
  intros j1 jt1 Lt1. rewrite lookup_app_l // => Eqj1.
Abort.

(* Lemma reborrow1_read_access_is_freeze stk pm old new prot β stk1:
  let it := mkItem pm new prot in
  reborrow1 stk old (bool_decide (pm = SharedReadWrite)) it β = Some stk1 →
  access1_pre β stk1 AccessRead new.
Proof.
  intros it.
  rewrite /reborrow1.
  case find_granting as [[i pi]|] eqn:Eqf; [|done]. cbn -[item_insert_dedup].
  case (decide (pm = SharedReadWrite)) => [Eqp|NEq].
  - subst pm. move => /= [<-]. move : Eqf => /= Eqf.
    destruct (item_insert_dedup_lookup stk it i) as (j & Eqlj & Eqj & HLj).
    { apply fmap_Some in Eqf as [[i' pi'] [[Eq' ?]%list_find_Some ?]].
      simplify_eq. by eexists. }
    exists j, it. do 3 (split; [done|]). simpl.
    intros j' jt' Lt'. rewrite (HLj _ Lt') => Eq'.
    have Ltj': (j' < i)%nat. { destruct Eqj as [|[]]; subst; [done|lia]. }
    have UM := find_granting_Some _ _ _ _ _ Eqf j' jt' Ltj' Eq'.
    admit.
  - rewrite bool_decide_false //.
    case access1 as [[i' stk']|] eqn:Eq'; [|done]. cbn -[item_insert_dedup].
    have ? : i = i' by eapply access1_find_granting_agree. subst i'.
    rewrite decide_True //. intros Eq0.
    rewrite (_: stk1 = item_insert_dedup stk it 0); [|by inversion Eq0]. clear Eq0.
    exists O, it.
    destruct (item_insert_dedup_lookup stk it O) as [j [Eqlj Eqj]].
    { apply fmap_Some_1 in Eqf as [[i2 pi2] [[Eq2 ?]%list_find_Some ?]].
      apply lookup_lt_is_Some_2. apply lookup_lt_Some in Eq2. lia. }
    destruct Eqj as [?|[]]; [subst j|lia]. do 3 (split; [done|]).
    intros ???. lia.
Abort.
*)

Lemma retag_ref_is_freeze_is_Some h α β clk l old T kind prot (tp: bool)
  (BLK: ∀ n, (n < tsize T)%nat → l +ₗ n ∈ dom (gset loc) h)
  (TP: tp → kind = UniqueRef)
  (FRZ: is_freeze T) (WF: Wf (mkState h α β clk))
  (PR : match prot with Some c => is_Some (β !! c) | _ => True end)
  (STK: ∀ m stk, (m < tsize T)%nat → α !! (l +ₗ m) = Some stk →
    let access := match kind with
                  | SharedRef | RawRef false => AccessRead
                  | _ => AccessWrite
                  end in access1_pre β stk access old) :
  is_Some (retag_ref h α β clk l old T kind prot tp).
Proof.
  rewrite /retag_ref. destruct (tsize T) as [|sT] eqn:Eqs; [by eexists|].
  set new := match kind with
             | RawRef _ => Untagged
             | _ => Tagged clk
             end.
  destruct (reborrow_is_freeze_is_Some h α β l old T kind new tp prot)
    as [α1 Eq1]; [..|done| |].
  { intros ?. rewrite Eqs -(state_wf_dom _ WF). by apply BLK. }
  { destruct tp; [by rewrite TP|]. by destruct kind as [| |[]]. }
  { intros m stk Lt. apply STK. by rewrite -Eqs. }
  rewrite Eq1 /=. destruct tp; [|by eexists].
  have ? : kind = UniqueRef by apply TP. clear TP. subst kind.
  rewrite visit_freeze_sensitive_is_freeze; [|done..].
  destruct (reborrow_wf_stack h α β (S clk) l old T UniqueRef new true prot α1)
    as [EqD [WFI NE]]; [|done|done|..].
  { rewrite /new. simpl; lia. }
  { split; [|apply WF]. eapply wf_stack_item_mono; [|apply WF]. simpl. lia. }
  destruct (reborrowN_is_Some α1 β l (tsize T) new old SharedReadOnly false None)
    as [α2 Eq2]; [|done|..].
  { intros ?. rewrite Eqs -EqD -(state_wf_dom _ WF). apply BLK. }
  { intros m stk1 Lt Eq. simpl.
    destruct (reborrow_is_freeze_lookup _ _ _ _ _ _ _ _ _ _ _ FRZ Eq1 _ _ Lt Eq)
      as [stk [Eq' RB']].
    move : RB'. simpl.
    set it := mkItem Unique new prot. move => RB'.
    rewrite -Eqs in STK.
    destruct (STK _ _ Lt Eq') as (io & ito & Eqo & Eqto & PMO & LtO).
    simpl in PMO, LtO. admit. }
  rewrite Eq2. by eexists.
Abort.


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
        | FnEntry _ => σ.(cpro) !! (Z.to_nat call) = Some true
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
