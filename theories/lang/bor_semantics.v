From Equations Require Import Equations.
From stdpp Require Export gmap.

From stbor.lang Require Export lang_base notation.

Set Default Proof Using "Type".

(*** STACKED BORROWS SEMANTICS ---------------------------------------------***)

Implicit Type (α: stacks) (t: ptr_id).

(** CORE SEMANTICS *)

Inductive access_kind := AccessRead | AccessWrite.

(* Since we only have Unique and SharedReadWrite, every item grants
read and write access. *)
Definition grants (perm: permission) (access: access_kind) : bool := true.

Definition matched_grant (access: access_kind) (bor: tag) (it: item) :=
  grants it.(perm) access ∧ it.(tg) = bor.
Instance matched_grant_dec (access: access_kind) (bor: tag) :
  Decision (matched_grant access bor it) := _.

(** Difference from the paper/Miri in indexing of stacks: *)
(** In the paper, we represent stacks as lists with their bottom at the left end
  (head) of the list. That is, in terms of indexing, 0 is the bottom of
  the stack `stk`, and `|stk| - 1` is the top of `stk`.
  In Coq, however, to conveniently perform induction on stacks, we pick the head
  of the list as the top, and the tail of the list as the bottom of the stack.
  In terms of indexing, 0 is thus the top of the stack, and `|stk| - 1` is the
  bottom.  In this case, a smaller index means a higher item in the stack. *)

(* Return the index of the granting item *)
Definition find_granting (stk: stack) (access: access_kind) (bor: tag) :
  option (nat * permission) :=
  (λ nit, (nit.1, nit.2.(perm))) <$> (list_find (matched_grant access bor) stk).

(* Checks to deallocate a location: Like a write access, but also there must be
  no active protectors at all. *)
Definition dealloc1 (stk: stack) (bor: tag) : option unit :=
  (* Step 1: Find granting item. *)
  found ← find_granting stk AccessWrite bor;
  Some ().

(* Find the index RIGHT BEFORE the first incompatiable item.
   Remember that 0 is the top of the stack. *)
Definition find_first_write_incompatible
  (stk: stack) (pm: permission) : option nat :=
  match pm with
  | Unique => Some (length stk)
  | SharedReadWrite =>
      match (list_find (λ it, it.(perm) ≠ SharedReadWrite) (reverse stk)) with
      | Some (idx, _) => Some ((length stk) - idx)%nat
      | _ => Some O
      end
  end.

(* Remove from `stk` the items before `idx`.
  Check that removed items do not have active protectors.
  The check is run from the top to before the `idx`. *)
Fixpoint remove_check (stk: stack) (idx: nat) : option stack :=
  match idx, stk with
  (* Assumption: idx ≤ length stk *)
  | S _, [] => None
  | O, stk => Some stk
  | S idx, it :: stk =>
      remove_check stk idx
  end.

(* Test if a memory `access` using pointer tagged `tg` is granted.
   If yes, return the index (in the old stack) of the item that granted it,
   as well as the new stack. *)
Definition access1 (stk: stack) (access: access_kind) (tg: tag)
  : option (nat * stack) :=
  (* Step 1: Find granting item. *)
  idx_p ← find_granting stk access tg;
  (* Step 2: Remove incompatiable items. *)
  (* Remove everything above the write-compatible items, like a proper stack. *)
  incompat_idx ← find_first_write_incompatible (take idx_p.1 stk) idx_p.2;
  stk' ← remove_check (take idx_p.1 stk) incompat_idx;
  Some (idx_p.1, stk' ++ drop idx_p.1 stk).

(* Initialize [l, l + n) with singleton stacks of `tg` *)
Definition init_stack (t: tag) : stack := [mkItem Unique t].
Fixpoint init_stacks α (l:loc) (n:nat) (tg: tag) : stacks :=
  match n with
  | O => α
  | S n => <[l:= init_stack tg]>(init_stacks α (l +ₗ 1) n tg)
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
Definition memory_read α l (tg: tag) (n: nat) : option stacks :=
  for_each α l n false (λ stk, nstk' ← access1 stk AccessRead tg; Some nstk'.2).
Definition memory_written α l (tg: tag) (n: nat) : option stacks :=
  for_each α l n false (λ stk, nstk' ← access1 stk AccessWrite tg ; Some nstk'.2).
Definition memory_deallocated α l (tg: tag) (n: nat) : option stacks :=
  for_each α l n true (λ stk, dealloc1 stk tg ;; Some []).

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
  (stk: stack) (derived_from: tag) (new: item) : option stack :=
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
    nstk' ← access1 stk access derived_from;
    Some (item_insert_dedup nstk'.2 new O)
  end.

Definition reborrowN α l n old_tag new_tag pm :=
  let it := mkItem pm new_tag in
  for_each α l n false (λ stk, grant stk old_tag it).

(* This implements EvalContextPrivExt::reborrow *)
(* TODO?: alloc.check_bounds(this, ptr, size)?; *)
Definition reborrow α l (old_tag: tag) (Tsize : nat) (kind: ref_kind)
  (new_tag: tag) :=
  match kind with
  | UniqueRef =>
      (* mutable refs or Box use Unique *)
      reborrowN α l Tsize old_tag new_tag Unique
  | RawRef =>
      (* mutable raw pointer uses SharedReadWrite *)
      reborrowN α l Tsize old_tag new_tag SharedReadWrite
  end.

(* Retag one pointer *)
(* This implements EvalContextPrivExt::retag_reference *)
Definition retag_ref α (nxtp: ptr_id) l (old_tag: tag) Tsize
  (kind: ref_kind)
  : option (tag * stacks * ptr_id) :=
  match Tsize with
  | O => (* Nothing to do for zero-sized types *)
      (* TODO: this can be handled by reborrow *)
      Some (old_tag, α, nxtp)
  | _ =>
      let new_tag := match kind with
                     | RawRef => Untagged
                     | _ => Tagged nxtp
                     end in
      (* reborrow old_tag with new_tag *)
      α' ← reborrow α l old_tag Tsize kind new_tag;
      (* TODO: this always increments the [nxtp] field, even though that is not
        necessary when new_tag = Untagged *)
      Some (new_tag, α', S nxtp)
  end.

(* This *partly* implements EvalContextExt::retag *)
(* Assumption: ct ∈ cids *)
Definition retag α (nxtp: ptr_id)
  (l: loc) (otag: tag) (kind: retag_kind) pk Tr :
  option (tag * stacks * ptr_id) :=
    let qualify : option ref_kind :=
      match pk, kind with
      (* Mutable reference *)
      | RefPtr, _ =>
          Some UniqueRef
      (* If is both raw ptr and Raw retagging, no protector *)
      | RawPtr, RawRt => Some RawRef
      (* Box pointer, no protector *)
      | BoxPtr, _ => Some UniqueRef
      (* Ignore Raw pointer otherwise *)
      | RawPtr, _ => None
      end in
    match qualify with
    | Some rkind => retag_ref α nxtp l otag Tr rkind
    | None => Some (otag, α, nxtp)
    end
    .

Definition tag_included (tg: tag) (nxtp: ptr_id) : Prop :=
  match tg with
  | Tagged t => (t < nxtp)%nat
  | _ => True
  end.
Infix "<t" := tag_included (at level 60, no associativity).
Definition tag_values_included (v: value) nxtp :=
  ∀ l tg, ScPtr l tg ∈ v → tg <t nxtp.
Infix "<<t" := tag_values_included (at level 60, no associativity).

(** Instrumented step for the stacked borrows *)
(* This ignores CAS for now. *)
Inductive bor_step α (nxtp: ptr_id) :
  event → stacks → ptr_id → Prop :=
(* | SysCallIS id :
    bor_step h α β nxtp (SysCallEvt id) h α β nxtp *)
(* This implements EvalContextExt::new_allocation. *)
| AllocIS x Tsize :
    (* Tagged nxtp is the first borrow of the variable x,
       used when accessing x directly (not through another pointer) *)
    bor_step α nxtp
              (AllocEvt x (Tagged nxtp) Tsize)
              (init_stacks α x Tsize (Tagged nxtp)) (S nxtp)
(* This implements AllocationExtra::memory_read. *)
| CopyIS α' l lbor Tsize vl
    (ACC: memory_read α l lbor Tsize = Some α')
    (* This comes from wellformedness, but for convenience we require it here *)
    (BOR: vl <<t nxtp):
    bor_step α nxtp (CopyEvt l lbor Tsize vl) α' nxtp
(* This implements AllocationExtra::memory_written. *)
| WriteIS α' l lbor Tsize vl
    (ACC: memory_written α l lbor Tsize = Some α')
    (* This comes from wellformedness, but for convenience we require it here *)
    (BOR: vl <<t nxtp) :
    bor_step α nxtp (WriteEvt l lbor Tsize vl) α' nxtp
(* This implements AllocationExtra::memory_deallocated. *)
| DeallocIS α' l lbor Tsize
    (ACC: memory_deallocated α l lbor Tsize = Some α') :
    bor_step α nxtp (DeallocEvt l lbor Tsize) α' nxtp
| RetagIS α' nxtp' l otag ntag Tsize kind pkind
    (RETAG: retag α nxtp l otag kind pkind Tsize = Some (ntag, α', nxtp')) :
    bor_step α nxtp (RetagEvt l otag ntag pkind Tsize kind) α' nxtp'.
