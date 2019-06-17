From stbor Require Import cmra simulation_local_base.

(** Public scalar relation *)
(* No case for poison *)
Definition arel (r: resUR) (s1 s2: scalar) : Prop :=
  match s1, s2 with
  | ScInt n1, ScInt n2 => n1 = n2
  | ScFnPtr n1, ScFnPtr n2 => n1 = n2
  | ScPtr l1 tg1, ScPtr l2 tg2 =>
      l1 = l2 ∧ tg1 = tg2 ∧
      match tg1 with
      | Untagged => True
      | Tagged t => ∃ (h: mem), r.1 !! t ≡ Some (to_tagKindR tkPub, to_heapUR h)
      end
  | _, _ => False
  end.

Definition ptrmap_inv (r: resUR) (σ: state) : Prop :=
  ∀ (t: ptr_id) (k: tag_kind) (h: mem), r.1 !! t ≡ Some (to_tagKindR k, to_heapUR h) →
  ∀ (l: loc) (s: scalar), h !! l = Some s →
  ∀ (stk: stack), σ.(sst) !! l = Some stk →
  ∀ pm opro, mkItem pm (Tagged t) opro ∈ stk →
  σ.(shp) !! l = Some s (* ∧ ... *) .

Definition cmap_inv (r: resUR) (σ: state) : Prop :=
  ∀ (c: call_id) (cs: call_state), r.2 !! c ≡ Some (to_callStateR cs) →
  c ∈ σ.(scs) ∧
  match cs with
  (* if c is a private call id *)
  | csOwned T =>
      (* for any tag [t] owned by c *)
      ∀ (t: ptr_id), t ∈ T →
      (* that protects the heaplet [h] *)
      ∀ k h, r.1 !! t ≡ Some (k, to_heapUR h) →
      (* if [l] is in that heaplet [h] *)
      ∀ (l: loc), l ∈ dom (gset loc) h →
      (* then a c-protector must be in the stack of l *)
      ∃ stk pm, σ.(sst) !! l = Some stk ∧ mkItem pm (Tagged t) (Some c) ∈ stk
  (* if c is a public call id *)
  | csPub => True
  end.

(* [l] is private w.r.t to some tag [t] if [t] is uniquely owned and protected
  by some call id [c] and [l] is in [t]'s heaplet [h]. *)
Definition priv_loc (r: resUR) (l: loc) (t: ptr_id) :=
  ∃ (c: call_id) (T: gset ptr_id) h,
  r.2 !! c ≡ Some (to_callStateR (csOwned T)) ∧ t ∈ T ∧
  r.1 !! t = Some (to_tagKindR tkUnique, to_heapUR h) ∧ l ∈ dom (gset loc) h.

(** State relation *)
Definition srel (r: resUR) (σs σt: state) : Prop :=
  σs.(sst) = σt.(sst) ∧ σs.(snp) = σt.(snp) ∧
  σs.(scs) = σt.(scs) ∧ σs.(snc) = σt.(snc) ∧
  ∀ (l: loc) st, σt.(shp) !! l = Some st →
  (∃ ss, σs.(shp) !! l = Some ss ∧ arel r ss st) ∨ (∃ (t: ptr_id), priv_loc r l t).

Definition wsat (r: resUR) (σs σt: state) : Prop :=
  ptrmap_inv r σt ∧ cmap_inv r σt ∧ srel r σs σt.

(** Value relation for function arguments/return values *)
(* Values passed among functions are public *)
Definition vrel (r: resUR) (v1 v2: value) := Forall2 (arel r) v1 v2.
Definition vrel_expr (r: resUR) (e1 e2: expr) :=
  ∃ v1 v2, e1 = Val v1 ∧ e2 = Val v2 ∧ vrel r v1 v2.
