From Equations Require Import Equations.
From stdpp Require Export gmap.

From stbor Require Export lang_base notation.

Set Default Proof Using "Type".

(*** STACKED BORROWS SEMANTICS ---------------------------------------------***)

Implicit Type (α: stacks) (β: protectors) (t: ptr_id) (c: call_id) (T: type).

(** CORE SEMANTICS *)

Inductive access_kind := AccessRead | AccessWrite.

Definition grants (perm: permission) (access: access_kind) : bool :=
  match perm, access with
  | Disabled, _ => false
  (* All items grant read access.
    All items except SharedReadOnly grant write access. *)
  | SharedReadOnly, AccessWrite => false
  | _, _ => true
  end.

Definition matched_grant (access: access_kind) (bor: tag) (it: item) :=
  grants it.(perm) access ∧ it.(tg) = bor.
Instance matched_grant_dec (access: access_kind) (bor: tag) :
  Decision (matched_grant access bor it) := _.

(* This is different from Miri's implementation: left-to-right is top-to-bottom
  of the stack. So 0 is top of the stack. The index returned by this function
  also follows this scheme (smaller means higher in the stack). *)
Definition find_granting (stk: stack) (access: access_kind) (bor: tag) :
  option (nat * permission) :=
  (λ nit, (nit.1, nit.2.(perm))) <$> (list_find (matched_grant access bor) stk).

Definition is_active β (c: call_id) : bool :=
  bool_decide (β !! c = Some true).
Definition is_active_protector β (it: item) :=
  match it.(protector) with
  | Some c => β !! c = Some true
  | _ => False
  end.
Instance is_active_protector_dec β : Decision (is_active_protector β it).
Proof. intros it. rewrite /is_active_protector. case_match; solve_decision. Qed.

(* Find the top active protector *)
Definition find_top_active_protector β (stk: stack) :=
  list_find (is_active_protector β) stk.

(* Checks to deallocate a location: Like a write access, but also there must be
  no active protectors at all. *)
Definition dealloc1 (stk: stack) (bor: tag) β : option unit :=
  (* Step 1: Find granting item. *)
  found ← find_granting stk AccessWrite bor;
  (* Step 2: Check that there are no active protectors left. *)
  if find_top_active_protector β stk then None else Some ().

(* Find the index RIGHT BEFORE the first incompatiable item *)
Definition find_first_write_incompatible
  (stk: stack) (pm: permission) : option nat :=
  match pm with
  | Unique => Some (length stk)
  | SharedReadWrite =>
      match (list_find (λ it, it.(perm) ≠ SharedReadWrite) (reverse stk)) with
      | Some (idx, _) => Some ((length stk) - idx)%nat
      | _ => Some O
      end
  | SharedReadOnly | Disabled => None
  end.

Definition check_protector β (it: item) : bool :=
  match it.(protector) with
  | None => true
  | Some c => if is_active β c then false else true
  end.

(* Remove from `stk` the items before `idx`.
  Check that removed items do not have active protectors.
  The check is run from the top to before the `idx`. *)
Fixpoint remove_check β (stk: stack) (idx: nat) : option stack :=
  match idx, stk with
  (* Assumption: idx ≤ length stk *)
  | S _, [] => None
  | O, stk => Some stk
  | S idx, it :: stk =>
      if check_protector β it then remove_check β stk idx else None
  end.

(* Replace any Unique permission with Disabled, starting from the top of the
  stack. Check that replaced item do not have active protectors *)
Fixpoint replace_check' β (acc stk : stack) : option stack :=
  match stk with
  | [] => Some acc
  | it :: stk =>
      if decide (it.(perm) = Unique) then
        if check_protector β it
        then let new := mkItem Disabled it.(tg) it.(protector) in
             replace_check' β (acc ++ [new]) stk
        else None
      else replace_check' β (acc ++ [it]) stk
  end.
Definition replace_check β (stk: stack) : option stack :=
  replace_check' β [] stk.

(* Test if a memory `access` using pointer tagged `tg` is granted.
   If yes, return the index (in the old stack) of the item that granted it,
   as well as the new stack. *)
Definition access1 (stk: stack) (access: access_kind) (tg: tag) β
  : option (nat * stack) :=
  (* Step 1: Find granting item. *)
  idx_p ← find_granting stk access tg;
  (* Step 2: Remove incompatiable items. *)
  match access with
  | AccessWrite =>
      (* Remove everything above the write-compatible items, like a proper stack. *)
      incompat_idx ← find_first_write_incompatible (take idx_p.1 stk) idx_p.2;
      stk' ← remove_check β (take idx_p.1 stk) incompat_idx;
      Some (idx_p.1, stk' ++ drop idx_p.1 stk)
  | AccessRead =>
      (* On a read, *disable* all `Unique` above the granting item. *)
      stk' ← replace_check β (take idx_p.1 stk);
      Some (idx_p.1, stk' ++ drop idx_p.1 stk)
  end.

(* Initialize [l, l + n) with singleton stacks of `tg` *)
Fixpoint init_stacks α (l:loc) (n:nat) (tg: tag) : stacks :=
  match n with
  | O => α
  | S n => <[l:= [mkItem Unique tg None]]>(init_stacks α (l +ₗ 1) n tg)
  end.

Fixpoint for_each α (l:loc) (n:nat) (dealloc: bool) (f: stack → option stack)
  : option stacks :=
  match n with
  | O => Some α
  | S n =>
      let l' := (l +ₗ n) in
      stk ← α !! l'; stk' ← f stk ;
      if dealloc
      then for_each (delete l' α) l n dealloc f
      else for_each (<[l':=stk']> α) l n dealloc f
  end.

(* Perform the access check on a block of continuous memory.
 * This implements Stacks::memory_read/memory_written/memory_deallocated. *)
Definition memory_read α β l (tg: tag) (n: nat) : option stacks :=
  for_each α l n false (λ stk, nstk' ← access1 stk AccessRead tg β; Some nstk'.2).
Definition memory_written α β l (tg: tag) (n: nat) : option stacks :=
  for_each α l n false (λ stk, nstk' ← access1 stk AccessWrite tg β; Some nstk'.2).
Definition memory_deallocated α β l (tg: tag) (n: nat) : option stacks :=
  for_each α l n true (λ stk, dealloc1 stk tg β ;; Some []).

Definition unsafe_action
  {A: Type} (f: A → loc → nat → bool → option A) (a: A) (l: loc)
  (last frozen_size unsafe_size: nat) :
  option (A * (nat * nat)) :=
  (* Anything between the last UnsafeCell and this UnsafeCell is frozen *)
  a' ← f a (l +ₗ last) frozen_size true;
  (* This UnsafeCell is not frozen *)
  let cur_off := (last + frozen_size)%nat in
    a'' ← f a' (l +ₗ cur_off) unsafe_size false ;
    Some (a'', ((cur_off + unsafe_size)%nat, O))
  .

(** Reborrow *)

(* visit the type left-to-right and apply the action `f`.
 + `last` is the offset of `l` from the last UnsafeCell,
 + `cur_dist` is the distance between `last` and the current offset of the
   visit, which is also the start of the sub-type `T`.
 + a` of type A is the accumulator for the visit.
 When an UnsafeCell is found, the action `f` is applied twice, through
 `unsafe_action`:
 - First `f` is applied for the frozen block, which is the range
   [last, last + cur_dist). `f` is applied with the boolean flag `true`
   (for frozen).
 - Then `f` is applied for the unfrozen block, which is the range
   [last + cur_dist, last + cur_dist + unsafe_block_size). `f` is applied with
   the boolean flag `false`. *)
Section blah.
Context {A: Type}.
Equations visit_freeze_sensitive'
  (h: mem) (l: loc) (f: A → loc → nat → bool → option A)
  (a: A) (last cur_dist: nat) (T: type) : option (A * (nat * nat)) :=
  visit_freeze_sensitive' h l f a last cur_dist (Scalar n) :=
    (* consider frozen, simply extend the distant by n *)
      Some (a, (last, cur_dist + n)%nat) ;
  visit_freeze_sensitive' h l f a last cur_dist (Reference _ _) :=
    (* consider frozen, extend the distant by 1 *)
      Some (a, (last, S cur_dist)) ;
  visit_freeze_sensitive' h l f a last cur_dist (Unsafe T) :=
    (* reach an UnsafeCell, apply the action `f` and return new `last` and
        `cur_dist` *)
      unsafe_action f a l last cur_dist (tsize T) ;
  visit_freeze_sensitive' h l f a last cur_dist (Union Ts) :=
    (* If it's a union, look at the type to see if there is UnsafeCell *)
      if is_freeze (Union Ts)
      (* No UnsafeCell, consider the whole block frozen and simply extend the
          distant. *)
      then Some (a, (last, cur_dist + (tsize (Union Ts)))%nat)
      (* There can be UnsafeCell, consider the whole block unfrozen and perform
          `f a _ _ false` on the whole block. `unsafe_action` will return the
          offsets for the following visit. *)
      else unsafe_action f a l last cur_dist (tsize (Union Ts)) ;
  visit_freeze_sensitive' h l f a last cur_dist (Product Ts) :=
    (* Try a shortcut *)
      if is_freeze (Product Ts)
      (* No UnsafeCell, consider the whole block frozen and simply extend the
        distant. *)
      then Some (a, (last, cur_dist + (tsize (Product Ts)))%nat)
      (* This implements left-to-right search on the type, which guarantees
        that the offsets are increasing. *)
      else visit_LR a last cur_dist Ts
        where visit_LR (a: A) (last cur_dist: nat) (Ts: list type)
          : option (A * (nat * nat)) :=
          { visit_LR a last cur_dist [] := Some (a, (last, cur_dist)) ;
            visit_LR a last cur_dist (T :: Ts) :=
              alc ← visit_freeze_sensitive' h l f a last cur_dist T ;
              visit_LR alc.1 alc.2.1 alc.2.2 Ts } ;
  visit_freeze_sensitive' h l f a last cur_dist (Sum Ts) :=
    (* Try a shortcut *)
      if is_freeze (Sum Ts)
      (* No UnsafeCell, consider the whole block frozen and simply extend the
          distant. *)
      then Some (a, (last, cur_dist + (tsize (Sum Ts)))%nat)
      else
        match h !! (l +ₗ (last + cur_dist)) with
        (* This looks up the current state to see which discriminant currently
            is active (which is an integer) and redirect the visit for the type
            of that discriminant. Note that this consitutes a read-access, and
            should adhere to the access checks. But we are skipping them here.
            FIXME *)
        | Some (LitInt i) =>
            if decide (O ≤ i)
            then (* the discriminant is well-defined, visit with the
                    corresponding type *)
              alc ← visit_lookup Ts (Z.to_nat i) ;
              (* Anything in the padding is considered frozen and will be
                 applied with the action by the following visit.
                 `should_offset` presents the offset that the visit SHOULD
                 arrive at after the visit. If there are padding bytes left,
                 they will be added to the cur_dist. *)
              let should_offset := (last + cur_dist + tsize (Sum Ts))%nat in
                Some (alc.1, (alc.2.1, (should_offset - alc.2.1)%nat))
            else None
        | _ => None
        end
      where visit_lookup (Ts: list type) (i: nat) : option (A * (nat * nat)) :=
            { visit_lookup [] _             := None ;
              visit_lookup (T :: _) O      :=
                visit_freeze_sensitive' h l f a last (S cur_dist) T ;
              visit_lookup (T :: Ts) (S i)  := visit_lookup Ts i }
  .
End blah.

Definition visit_freeze_sensitive {A: Type}
  h (l: loc) (T: type) (f: A → loc → nat → bool → option A) (a: A) : option A :=
  match visit_freeze_sensitive' h l f a O O T with
  | Some (a', (last', cur_dist')) =>
      (* the last block is frozen *)
      f a' (l +ₗ last') cur_dist' true
  | _ => None
  end.


(* Insert `it` into `stk` at `idx` unless `it` is equal to its neighbors. *)
Definition item_insert_dedup (stk: stack) (new: item) (idx: nat) : stack :=
  match idx with
  | O =>
    match stk with
    | [] => [new]
    | it' :: stk' => if decide (new = it') then stk else new :: stk
    end
  | S idx' =>
    match stk !! idx', stk !! idx with
    | None, None => take (S idx') stk ++ [new] ++ drop (S idx') stk
    | Some it_l, Some it_r =>
        if decide (new = it_l) then stk
        else if decide (new = it_r) then stk
             else take (S idx') stk ++ [new] ++ drop (S idx') stk
    | Some it, None | None, Some it =>
        if decide (new = it) then stk
        else take (S idx') stk ++ [new] ++ drop (S idx') stk
    end
  end.

(* Insert a `new` tag derived from a parent tag `derived_from`. *)
Definition grant
  (stk: stack) (derived_from: tag) (new: item) β : option stack :=
  (* Figure out which access `new` allows *)
  let access := if grants new.(perm) AccessWrite then AccessWrite else AccessRead in
  (* Figure out which item grants our parent (`derived_from`) this kind of access *)
  idx_p ← find_granting stk access derived_from;
  match new.(perm) with
  | SharedReadWrite =>
    (* access is AccessWrite *)
    new_idx ← find_first_write_incompatible (take idx_p.1 stk) idx_p.2;
    Some (item_insert_dedup stk new new_idx)
  | _ =>
    (* an actual access check! *)
    nstk' ← access1 stk access derived_from β;
    Some (item_insert_dedup nstk'.2 new O)
  end.

Definition reborrowN α β l n old_tag new_tag pm prot :=
  let it := mkItem pm new_tag prot in
  for_each α l n false (λ stk, grant stk old_tag it β).

(* This implements EvalContextPrivExt::reborrow *)
(* TODO?: alloc.check_bounds(this, ptr, size)?; *)
Definition reborrow h α β l (old_tag: tag) T (kind: ref_kind)
  (new_tag: tag) (protector: option call_id) :=
  match kind with
  | SharedRef | RawRef false =>
      (* for shared refs and const raw pointer, treat Unsafe as SharedReadWrite
        and Freeze as SharedReadOnly *)
      visit_freeze_sensitive h l T
        (λ α' l' sz frozen,
          (* If is in Unsafe, use SharedReadWrite, otherwise SharedReadOnly *)
          let perm := if frozen then SharedReadOnly else SharedReadWrite in
          reborrowN α' β l' sz old_tag new_tag perm protector) α
  | UniqueRef false =>
      (* mutable refs or Box use Unique *)
      reborrowN α β l (tsize T) old_tag new_tag Unique protector
  | UniqueRef true | RawRef true =>
      (* mutable raw pointer uses SharedReadWrite *)
      reborrowN α β l (tsize T) old_tag new_tag SharedReadWrite protector
  end.

(* Retag one pointer *)
(* This implements EvalContextPrivExt::retag_reference *)
Definition retag_ref h α β (clk: ptr_id) l (old_tag: tag) T
  (kind: ref_kind) (protector: option call_id)
  : option (tag * stacks * ptr_id) :=
  match tsize T with
  | O => (* Nothing to do for zero-sized types *)
      Some (old_tag, α, clk)
  | _ =>
      let new_tag := match kind with
                     | RawRef _ => Untagged
                     | _ => Tagged clk
                     end in
      (* reborrow old_tag with new_tag *)
      α' ← reborrow h α β l old_tag T kind new_tag protector;
      Some (new_tag, α', S clk)
  end.

(* This implements EvalContextExt::retag *)
Equations retag (h: mem) α (clk: ptr_id) β (x: loc) (kind: retag_kind) T :
  option (mem * stacks * ptr_id) :=
  retag h α clk β x kind (Scalar _)         := Some (h, α, clk) ;
  retag h α clk β x kind (Union _)          := Some (h, α, clk) ;
  retag h α clk β x kind (Unsafe T)         := retag h α clk β x kind T ;
  retag h α clk β x kind (Reference pk Tr) with h !! x :=
  { | Some (LitLoc l otag) :=
        let qualify : option (ref_kind * option call_id) :=
          match pk, kind with
          (* Mutable reference *)
          | RefPtr Mutable, _ =>
              Some (UniqueRef (is_two_phase kind), adding_protector kind)
          (* Immutable reference *)
          | RefPtr Immutable, _ => Some (SharedRef, adding_protector kind)
          (* If is both raw ptr and Raw retagging, no protector *)
          | RawPtr mut, RawRt => Some (RawRef (bool_decide (mut = Mutable)), None)
          (* Box pointer, no protector *)
          | BoxPtr, _ => Some (UniqueRef false, None)
          (* Ignore Raw pointer otherwise *)
          | RawPtr _, _ => None
          end in
        match qualify with
        | Some (rkind, protector) =>
            bac ← retag_ref h α β clk l otag Tr rkind protector ;
            Some (<[x := LitLoc l bac.1.1]>h, bac.1.2, bac.2)
        | None => Some (h, α, clk)
        end ;
    | _ := None } ;
  retag h α clk β x kind (Product Ts)       := visit_LR h α clk x Ts
    (* left-to-right visit to retag *)
    where visit_LR h α (clk: ptr_id) (x: loc) (Ts: list type)
      : option (mem * stacks * ptr_id) :=
      { visit_LR h α clk x []         := Some (h, α, clk) ;
        visit_LR h α clk x (T :: Ts)  :=
          hac ← retag h α clk β x kind T ;
          visit_LR hac.1.1 hac.1.2 hac.2 (x +ₗ (tsize T)) Ts } ;
  retag h α clk β x kind (Sum Ts) with h !! x :=
  { | Some (LitInt i) :=
        if decide (O ≤ i < length Ts)
        then (* the discriminant is well-defined, visit with the
                corresponding type *)
          visit_lookup Ts (Z.to_nat i)
        else None
        where visit_lookup (Ts: list type) (i: nat) : option (mem * stacks * ptr_id) :=
        { visit_lookup [] i             := None ;
          visit_lookup (T :: Ts) O      := retag h α clk β (x +ₗ 1) kind T ;
          visit_lookup (T :: Ts) (S i)  := visit_lookup Ts i } ;
    | _ := None }
  .

Definition tag_value_included (tg: tag) (clk: ptr_id) : Prop :=
  match tg with
  | Tagged t => (t < clk)%nat
  | _ => True
  end.
Infix "<b" := tag_value_included (at level 60, no associativity).
Definition tag_values_included (vl: list lit) clk :=
  ∀ l tg, LitLoc l tg ∈ vl → tg <b clk.
Infix "<<b" := tag_values_included (at level 60, no associativity).

(** Instrumented step for the stacked borrows *)
(* This ignores CAS for now. *)
Inductive bor_step h α β (clk: ptr_id):
  mem_event → mem → stacks → protectors → ptr_id → Prop :=
| SilentIS :
    bor_step h α β clk SilentEvt h α β clk
(* | SysCallIS id :
    bor_step h α β clk (SysCallEvt id) h α β clk *)
(* This implements EvalContextExt::new_allocation. *)
| AllocIS x T :
    (* Tagged clk is the first borrow of the variable x,
       used when accessing x directly (not through another pointer) *)
    bor_step h α β clk
                      (AllocEvt x (Tagged clk) T) h
                      (init_stacks α x (tsize T) (Tagged clk)) β (S clk)
(* This implements AllocationExtra::memory_read. *)
| CopyIS α' l lbor T vl
    (ACC: memory_read α β l lbor (tsize T) = Some α')
    (BOR: vl <<b clk) :
    bor_step h α β clk (CopyEvt l lbor T vl) h α' β clk
(* This implements AllocationExtra::memory_written. *)
| WriteIS α' l lbor T vl
    (ACC: memory_written α β l lbor (tsize T) = Some α')
    (BOR: vl <<b clk) :
    bor_step h α β clk
                      (WriteEvt l lbor T vl) h α' β clk
(* This implements AllocationExtra::memory_deallocated. *)
| DeallocIS α' l lbor T
    (ACC: memory_deallocated α β l lbor (tsize T) = Some α') :
    bor_step h α β clk
                      (DeallocEvt l lbor T) h α' β clk
| NewCallIS name:
    let call : call_id := fresh (dom (gset call_id) β) in
    bor_step h α β clk
                      (NewCallEvt name call) h α (<[call := true]>β) clk
| EndCallIS call
    (ACTIVE: β !! call = Some true) :
    bor_step h α β clk
                      (EndCallEvt call) h α (<[call := false]>β) clk
| RetagIS h' α' clk' x T kind
    (FNBAR: match kind with FnEntry c => β !! c = Some true | _ => True end)
    (RETAG: retag h α clk β x kind T = Some (h', α', clk')) :
    bor_step h α β clk
                      (RetagEvt x T kind) h' α' β clk'.
