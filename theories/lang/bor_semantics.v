From stdpp Require Export gmap.

From stbor.lang Require Export lang_base notation.

Set Default Proof Using "Type".

(*** STACKED BORROWS SEMANTICS ---------------------------------------------***)

Implicit Type (α: stacks) (t: ptr_id).

(** CORE SEMANTICS *)

(* TODO: Coq doesn't like it if I leave out the true. Then it seems to
not be able to figure out how to decide the proposition. Also
solve_decision doesn't work for this, but I am not even sure if it's
intended for this situation. *)
Definition matched_grant (bor: tag) (it: item) :=
  true ∧ it.(tg) = bor.
Instance matched_grant_dec (bor: tag) :
  Decision (matched_grant bor it) := _.

(** Difference from the paper/Miri in indexing of stacks: *)
(** In the paper, we represent stacks as lists with their bottom at the left end
  (head) of the list. That is, in terms of indexing, 0 is the bottom of
  the stack `stk`, and `|stk| - 1` is the top of `stk`.
  In Coq, however, to conveniently perform induction on stacks, we pick the head
  of the list as the top, and the tail of the list as the bottom of the stack.
  In terms of indexing, 0 is thus the top of the stack, and `|stk| - 1` is the
  bottom.  In this case, a smaller index means a higher item in the stack. *)

(* Return the index of the granting item *)
Definition find_granting (stk: stack) (bor: tag) : option nat :=
  (λ nit, nit.1) <$> (list_find (matched_grant bor) stk).

(* Test if a memory `access` using pointer tagged `tg` is granted.
   If yes, return the index (in the old stack) of the item that granted it,
   as well as the new stack. *)
Definition access1 (stk: stack) (tg: tag)
  : option stack :=
  (* Step 1: Find granting item. *)
  idx ← find_granting stk tg;
  (* Step 2: Remove incompatable items. *)
  (* Remove everything above the granting item, like a proper stack. *)
  Some (drop idx stk).

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
(* Deallocation also performs an "access" (use), ensuring that the tag is
 * indeed in the stack. *)
Definition memory_use α l (tg: tag) (n: nat) (deallocate: bool) : option stacks :=
  for_each α l n deallocate (λ stk, access1 stk tg).

(** Reborrow *)

(* Push a `new` tag derived from a parent tag `derived_from`. Performs
 * an "access" on the parent tag to ensure it is on top of the stack
 * (by dropping everything above it). *)
Definition grant
  (stk: stack) (derived_from: tag) (new: item) : option stack :=
    (* an actual access check! *)
    nstk' ← access1 stk derived_from;
    Some (new :: nstk').

Definition reborrowN α l n old_tag new_tag pm :=
  let it := mkItem pm new_tag in
  for_each α l n false (λ stk, grant stk old_tag it).

(* This implements EvalContextPrivExt::reborrow *)
(* TODO?: alloc.check_bounds(this, ptr, size)?; *)
Definition reborrow α l (old_tag: tag) (Tsize : nat) (kind: ref_kind)
  (new_tag: tag) :=
  (* mutable refs use Unique *)
  (* mutable raw pointer uses SharedReadWrite *)
  let pm := match kind with UniqueRef => Unique | RawRef => SharedReadWrite end in
  reborrowN α l Tsize old_tag new_tag pm.

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
                     | UniqueRef => Tagged nxtp
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
      | RefPtr, _ => Some UniqueRef
      (* Raw pointer only causes actual retagging if it's a retag[raw]
       * (reference-to-raw cast) *)
      | RawPtr, RawRt => Some RawRef
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
| UseIS α' l lbor Tsize vl
    (ACC: memory_use α l lbor Tsize false = Some α')
    (* This comes from wellformedness, but for convenience we require it here *)
    (BOR: vl <<t nxtp):
    bor_step α nxtp (UseEvt l lbor Tsize vl) α' nxtp
(* (* This implements AllocationExtra::memory_written. *) *)
(* | WriteIS α' l lbor Tsize vl *)
(*     (ACC: memory_use α l lbor Tsize = Some α') *)
(*     (* This comes from wellformedness, but for convenience we require it here *) *)
(*     (BOR: vl <<t nxtp) : *)
(*     bor_step α nxtp (WriteEvt l lbor Tsize vl) α' nxtp *)
(* This implements AllocationExtra::memory_deallocated. *)
| DeallocIS α' l lbor Tsize
    (ACC: memory_use α l lbor Tsize true = Some α') :
    bor_step α nxtp (DeallocEvt l lbor Tsize) α' nxtp
| RetagIS α' nxtp' l otag ntag Tsize kind pkind
    (RETAG: retag α nxtp l otag kind pkind Tsize = Some (ntag, α', nxtp')) :
    bor_step α nxtp (RetagEvt l otag ntag pkind Tsize kind) α' nxtp'.
