From iris.program_logic Require Export language ectx_language ectxi_language.
From stdpp Require Export strings.
From stdpp Require Import gmap.
Set Default Proof Using "Type".

Open Scope Z_scope.

(** Expressions and vals. *)
Definition block : Set := positive.
Definition loc : Set := block * Z.

Bind Scope loc_scope with loc.
Delimit Scope loc_scope with L.
Open Scope loc_scope.

Inductive bin_op :=
  | AddOp     (* + addition       *)
  | SubOp     (* - subtraction    *)
  | MulOp     (* * multiplication *)
  | DivOp     (* / division       *)
  | RemOp     (* % modulus        *)
  | BitXorOp  (* ^ bit xor        *)
  | BitAndOp  (* & bit and        *)
  | BitOrOp   (* | bit or         *)
  | ShlOp     (* << shift left    *)
  | ShrOp     (* >> shift right   *)
  | EqOp      (* == equality      *)
  | LtOp      (* < less than      *)
  | LeOp      (* <= less than or equal to *)
  | NeOp      (* != not equal to  *)
  | GeOp      (* >= greater than or equal to *)
  | GtOp      (* > greater than   *)
  | OffsetOp  (* . offset         *)
  .

Inductive binder := BAnon | BNamed : string → binder.
Delimit Scope lrust_binder_scope with RustB.
Bind Scope lrust_binder_scope with binder.

Notation "[ ]" := (@nil binder) : lrust_binder_scope.
Notation "a :: b" := (@cons binder a%RustB b%RustB)
  (at level 60, right associativity) : lrust_binder_scope.
Notation "[ x1 ; x2 ; .. ; xn ]" :=
  (@cons binder x1%RustB (@cons binder x2%RustB
        (..(@cons binder xn%RustB (@nil binder))..))) : lrust_binder_scope.
Notation "[ x ]" := (@cons binder x%RustB (@nil binder)) : lrust_binder_scope.

Definition cons_binder (mx : binder) (X : list string) : list string :=
  match mx with BAnon => X | BNamed x => x :: X end.
Infix ":b:" := cons_binder (at level 60, right associativity).
Fixpoint app_binder (mxl : list binder) (X : list string) : list string :=
  match mxl with [] => X | b :: mxl => b :b: app_binder mxl X end.
Infix "+b+" := app_binder (at level 60, right associativity).
Instance binder_dec_eq : EqDecision binder.
Proof. solve_decision. Defined.

Instance set_unfold_cons_binder x mx X P :
  SetUnfold (x ∈ X) P → SetUnfold (x ∈ mx :b: X) (BNamed x = mx ∨ P).
Proof.
  constructor. rewrite -(set_unfold (x ∈ X) P).
  destruct mx; rewrite /= ?elem_of_cons; naive_solver.
Qed.
Instance set_unfold_app_binder x mxl X P :
  SetUnfold (x ∈ X) P → SetUnfold (x ∈ mxl +b+ X) (BNamed x ∈ mxl ∨ P).
Proof.
  constructor. rewrite -(set_unfold (x ∈ X) P).
  induction mxl as [|?? IH]; set_solver.
Qed.

Notation time := nat (only parsing).
Inductive borrow :=
| UniqB (t: time)
| ShrB (ot : option time)
.

Inductive base_lit :=
| LitPoison | LitLoc (l: loc) (tag: borrow) | LitInt (n : Z).

Inductive expr :=
(* variable *)
| Var (x : string)
(* values *)
| Lit (l : base_lit)
| Rec (f : binder) (xl : list binder) (e : expr)
(* lvalue *)
| Place (l: loc) (tag: borrow)
(* bin op *)
| BinOp (op : bin_op) (e1 e2 : expr)
(* application *)
| App (e : expr) (el : list expr)
(* mem op *)
| Read (e : expr)
| Write (e1 e2: expr)
| CAS (e0 e1 e2 : expr)
| Alloc (e : expr)
| Free (e1 e2 : expr)
(* place op *)
| Deref (e: expr)
| Ref (e: expr)
(* case *)
| Case (e : expr) (el : list expr)
(* concurrency *)
| Fork (e : expr).

Arguments App _%E _%E.
Arguments Case _%E _%E.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Var x => bool_decide (x ∈ X)
  | Lit _ | Place _ _ => true
  | Rec f xl e => is_closed (f :b: xl +b+ X) e
  | BinOp _ e1 e2 | Write e1 e2 | Free e1 e2 =>
    is_closed X e1 && is_closed X e2
  | App e el | Case e el => is_closed X e && forallb (is_closed X) el
  | Read e | Alloc e | Deref e | Ref e | Fork e => is_closed X e
  | CAS e0 e1 e2 => is_closed X e0 && is_closed X e1 && is_closed X e2
  end.

Class Closed (X : list string) (e : expr) := closed : is_closed X e.
Instance closed_proof_irrel env e : ProofIrrel (Closed env e).
Proof. rewrite /Closed. apply _. Qed.
Instance closed_decision env e : Decision (Closed env e).
Proof. rewrite /Closed. apply _. Qed.

Inductive immediate :=
| LitV (l : base_lit)
| RecV (f : binder) (xl : list binder) (e : expr) `{Closed (f :b: xl +b+ []) e}.

Inductive val :=
| ImmV (v: immediate)
| PlaceV (l: loc) (tag: borrow)
.

Bind Scope val_scope with val.

Definition of_val (v : val) : expr :=
  match v with
  | ImmV (RecV f x e) => Rec f x e
  | ImmV (LitV l) => Lit l
  | PlaceV l tag => Place  l tag
  end.

Definition to_val (e : expr) : option val :=
  match e with
  | Rec f xl e =>
    if decide (Closed (f :b: xl +b+ []) e) then Some (ImmV (RecV f xl e)) else None
  | Lit l => Some (ImmV (LitV l))
  | Place l tag => Some (PlaceV l tag)
  | _ => None
  end.

(** Substitution *)
Fixpoint subst (x : string) (es : expr) (e : expr) : expr :=
  match e with
  | Var y => if bool_decide (y = x) then es else Var y
  | Lit l => Lit l
  | Rec f xl e =>
    Rec f xl $ if bool_decide (BNamed x ≠ f ∧ BNamed x ∉ xl) then subst x es e else e
  | Place l tag => Place l tag
  | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
  | App e el => App (subst x es e) (map (subst x es) el)
  | Read e => Read (subst x es e)
  | Write e1 e2 => Write (subst x es e1) (subst x es e2)
  | CAS e0 e1 e2 => CAS (subst x es e0) (subst x es e1) (subst x es e2)
  | Alloc e => Alloc (subst x es e)
  | Free e1 e2 => Free (subst x es e1) (subst x es e2)
  | Deref e => Deref (subst x es e)
  | Ref e => Ref (subst x es e)
  | Case e el => Case (subst x es e) (map (subst x es) el)
  | Fork e => Fork (subst x es e)
  end.

Definition subst' (mx : binder) (es : expr) : expr → expr :=
  match mx with BNamed x => subst x es | BAnon => id end.

Fixpoint subst_l (xl : list binder) (esl : list expr) (e : expr) : option expr :=
  match xl, esl with
  | [], [] => Some e
  | x::xl, es::esl => subst' x es <$> subst_l xl esl e
  | _, _ => None
  end.
Arguments subst_l _%RustB _ _%E.

Definition subst_v (xl : list binder) (vsl : vec val (length xl))
                   (e : expr) : expr :=
  Vector.fold_right2 (λ b, subst' b ∘ of_val) e _ (list_to_vec xl) vsl.
Arguments subst_v _%RustB _ _%E.

Lemma subst_v_eq (xl : list binder) (vsl : vec val (length xl)) e :
  Some $ subst_v xl vsl e = subst_l xl (of_val <$> vec_to_list vsl) e.
Proof.
  revert vsl. induction xl=>/= vsl; inv_vec vsl=>//=v vsl. by rewrite -IHxl.
Qed.

(** Evaluation contexts *)
Inductive ectx_item :=
| BinOpLCtx (op : bin_op) (e2 : expr)
| BinOpRCtx (op : bin_op) (v1 : val)
| AppLCtx (e2 : list expr)
| AppRCtx (v : val) (vl : list val) (el : list expr)
| ReadCtx
| WriteLCtx (e : expr)
| WriteRCtx (v : val)
| CasLCtx (e1 e2: expr)
| CasMCtx (v0 : val) (e2 : expr)
| CasRCtx (v0 : val) (v1 : val)
| AllocCtx
| FreeLCtx (e : expr)
| FreeRCtx (v : val)
| DerefCtx
| RefCtx
| CaseCtx (el : list expr).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | BinOpLCtx op e2 => BinOp op e e2
  | BinOpRCtx op v1 => BinOp op (of_val v1) e
  | AppLCtx e2 => App e e2
  | AppRCtx v vl el => App (of_val v) ((of_val <$> vl) ++ e :: el)
  | ReadCtx => Read e
  | WriteLCtx e2 => Write e e2
  | WriteRCtx v1 => Write (of_val v1) e
  | CasLCtx e1 e2 => CAS e e1 e2
  | CasMCtx v0 e2 => CAS (of_val v0) e e2
  | CasRCtx v0 v1 => CAS (of_val v0) (of_val v1) e
  | AllocCtx => Alloc e
  | FreeLCtx e2 => Free e e2
  | FreeRCtx v1 => Free (of_val v1) e
  | DerefCtx => Deref e
  | RefCtx => Ref e
  | CaseCtx el => Case e el
  end.


(** Main state: a heap of immediates. *)
Definition mem := gmap loc immediate.

(** The stepping relation *)
(* Be careful to make sure that poison is always stuck when used for anything
   except for reading from or writing to memory! *)
Definition Z_of_bool (b : bool) : Z :=
  if b then 1 else 0.

Definition lit_of_bool (b : bool) : base_lit :=
  LitInt $ Z_of_bool b.

Definition shift_loc (l : loc) (z : Z) : loc := (l.1, l.2 + z).

Notation "l +ₗ z" := (shift_loc l%L z%Z)
  (at level 50, left associativity) : loc_scope.

Fixpoint init_mem (l:loc) (n:nat) (σ:mem) : mem :=
  match n with
  | O => σ
  | S n => <[l:=LitV LitPoison]>(init_mem (l +ₗ 1) n σ)
  end.

Fixpoint free_mem (l:loc) (n:nat) (σ:mem) : mem :=
  match n with
  | O => σ
  | S n => delete l (free_mem (l +ₗ 1) n σ)
  end.

Inductive lit_eq (σ : mem) : base_lit → base_lit → Prop :=
(* No refl case for poison *)
| IntRefl z : lit_eq σ (LitInt z) (LitInt z)
| LocRefl l tag1 tag2 : lit_eq σ (LitLoc l tag1) (LitLoc l tag2)
(* Comparing unallocated pointers can non-deterministically say they are equal
   even if they are not.  Given that our `free` actually makes addresses
   re-usable, this may not be strictly necessary, but it is the most
   conservative choice that avoids UB (and we cannot use UB as this operation is
   possible in safe Rust).  See
   <https://internals.rust-lang.org/t/comparing-dangling-pointers/3019> for some
   more background. *)
| LocUnallocL l1 l2 tag1 tag2 :
    σ !! l1 = None →
    lit_eq σ (LitLoc l1 tag1) (LitLoc l2 tag2)
| LocUnallocR l1 l2 tag1 tag2 :
    σ !! l2 = None →
    lit_eq σ (LitLoc l1 tag1) (LitLoc l2 tag2).

Inductive lit_neq : base_lit → base_lit → Prop :=
| IntNeq z1 z2 :
    z1 ≠ z2 → lit_neq (LitInt z1) (LitInt z2)
| LocNeq l1 l2 tag1 tag2 :
    l1 ≠ l2 → lit_neq (LitLoc l1 tag1) (LitLoc l2 tag2)
| LocNeqNullR l tag :
    lit_neq (LitLoc l tag) (LitInt 0)
| LocNeqNullL l tag :
    lit_neq (LitInt 0) (LitLoc l tag).

Inductive bin_op_eval (σ : mem) : bin_op → base_lit → base_lit → base_lit → Prop :=
| BinOpPlus z1 z2 :
    bin_op_eval σ AddOp (LitInt z1) (LitInt z2) (LitInt (z1 + z2))
| BinOpMinus z1 z2 :
    bin_op_eval σ SubOp (LitInt z1) (LitInt z2) (LitInt (z1 - z2))
| BinOpLe z1 z2 :
    bin_op_eval σ LeOp (LitInt z1) (LitInt z2) (lit_of_bool $ bool_decide (z1 ≤ z2))
| BinOpEqTrue l1 l2 :
    lit_eq σ l1 l2 → bin_op_eval σ EqOp l1 l2 (lit_of_bool true)
| BinOpEqFalse l1 l2 :
    lit_neq l1 l2 → bin_op_eval σ EqOp l1 l2 (lit_of_bool false)
| BinOpOffset l z tag :
    bin_op_eval σ OffsetOp (LitLoc l tag) (LitInt z) (LitLoc (l +ₗ z) tag).

Definition stuck_term := App (Lit $ LitInt 0) [].

Definition is_unique (bor: borrow) :=
  match bor with | UniqB _ => True | _ => False end.
Definition is_shared (bor: borrow) :=
  match bor with | ShrB _ => True | _ => False end.

Inductive ref_kind :=
(* &mut *)
| UniqueRef
(* & *)
| FrozenRef
(* * (raw) or & to UnsafeCell *)
| RawRef.

Inductive retag_kind := | FnEntry | TwoPhase | Raw | Default.

Notation call_id := nat (only parsing).
Inductive event :=
| AllocEvt (l : loc) (n: positive) (lbor: borrow)
| DeallocEvt (l: loc) (n : positive) (lbor: borrow)
| ReadEvt (l: loc) (lbor: borrow) (v: immediate)
| WriteEvt (l: loc) (lbor: borrow) (v: immediate)
| DerefEvt (l: loc) (lbor: borrow) (ref: ref_kind)
| RetagEvt (x l: loc) (n : positive) (bor bor': borrow)
           (retag: retag_kind) (bar: option call_id)
.

Inductive base_step :
  expr → mem → option event → expr → mem → list expr → Prop :=
| BinOpBS op l1 l2 l' σ :
    bin_op_eval σ op l1 l2 l' →
    base_step (BinOp op (Lit l1) (Lit l2)) σ None (Lit l') σ []
| BetaBS f xl e e' el σ :
    Forall (λ ei, is_Some (to_val ei)) el →
    Closed (f :b: xl +b+ []) e →
    subst_l (f::xl) (Rec f xl e :: el) e = Some e' →
    base_step (App (Rec f xl e) el) σ None e' σ []
| RefBS l lbor σ :
    is_Some (σ !! l) →
    base_step (Ref (Place l lbor)) σ None (Lit (LitLoc l lbor)) σ []
| DerefBS l lbor ref σ :
    is_Some (σ !! l) →
    base_step (Deref (Lit (LitLoc l lbor))) σ
              (Some $ DerefEvt l lbor ref)
              (Place l lbor) σ
              []
| ReadBS l v lbor σ :
    σ !! l = Some v →
    base_step (Read (Place l lbor)) σ
              (Some $ ReadEvt l lbor v)
              (of_val (ImmV v)) σ
              []
| WriteS l e v lbor σ :
    is_Some (σ !! l) →
    to_val e = Some (ImmV v) →
    base_step (Write (Place l lbor) e) σ
              (Some $ WriteEvt l lbor v)
              (Lit LitPoison) (<[l:=v]>σ)
              []
| AllocS n l lbor σ :
    0 < n →
    (∀ m, σ !! (l +ₗ m) = None) →
    base_step (Alloc $ Lit $ LitInt n) σ
              (Some $ AllocEvt l (Z.to_pos n) lbor)
              (Place l lbor) (init_mem l (Z.to_nat n) σ)
              []
| FreeS n l lbor σ :
    0 < n →
    (∀ m, is_Some (σ !! (l +ₗ m)) ↔ 0 ≤ m < n) →
    base_step (Free (Lit $ LitInt n) (Place l lbor)) σ
              (Some $ DeallocEvt l (Z.to_pos n) lbor)
              (Lit LitPoison) (free_mem l (Z.to_nat n) σ)
              []
| CaseS i el e σ :
    0 ≤ i →
    el !! (Z.to_nat i) = Some e →
    base_step (Case (Lit $ LitInt i) el) σ None e σ []
| ForkS e σ:
    base_step (Fork e) σ None (Lit LitPoison) σ [e].

(* Instrumented state: barriers, and stacked borrows. *)
Definition barriers := gmap call_id bool.

Inductive stack_item :=
| Uniq (t: time)
| Shr
| FnBarrier (ci : call_id)
.
Record bor_stack := mkBorStack {
  borrows     : list stack_item;
  frozen_since: option time;
}.
Definition is_frozen (s : bor_stack) : Prop := is_Some s.(frozen_since).

Definition stacks := gmap loc bor_stack.

Fixpoint init_stacks (l:loc) (n:nat) (β:stacks) (si: stack_item) : stacks :=
  match n with
  | O => β
  | S n => <[l:= mkBorStack [si] None]>(init_stacks (l +ₗ 1) n β si)
  end.

(** Dealloc checks for no active barrier on the stack *)
Definition is_active (bar: barriers) (c: call_id) : bool :=
  bool_decide (bar !! c = Some true).

Definition is_active_barrier (bar: barriers) (si: stack_item) :=
  match si with
  | FnBarrier c => bar !! c = Some true
  | _ => False
  end.
Instance is_active_barrier_dec bar : Decision (is_active_barrier bar si).
Proof. move => [?| |?] /=; solve_decision. Qed.

Definition find_top_active_call (stack: list stack_item) (bar: barriers) :
  option call_id := (list_find (is_active_barrier bar) stack) ≫= (Some ∘ fst).

Inductive access_kind := AccessRead | AccessWrite | AccessDealloc.
Definition to_access_kind (kind : ref_kind): access_kind :=
  match kind with
  | UniqueRef => AccessWrite
  | _ => AccessRead
  end.
Definition dealloc_no_active_barrier
  (access: access_kind) (stack: list stack_item) (bar: barriers) : bool :=
  match access with
  | AccessDealloc =>
      if find_top_active_call stack bar then false else true
  | _ => true
  end.

(** Check for accesses *)
(* Return None if the check fails.
 * Return Some stack' where stack' is the new stack. *)
Fixpoint access1
  (stack: list stack_item) (bor: borrow) (access: access_kind) (bar: barriers)
  : option (list stack_item) :=
  match stack, bor, access with
  (* try to pop barriers *)
  | FnBarrier c :: stack', _, _ =>
      (* cannot pop an active barrier *)
      if (is_active bar c) then None
      else access1 stack' bor access bar
  (* Uniq t matches UniqB t *)
  |  Uniq t1 :: stack', UniqB t2, _ =>
      if (decide (t1 = t2))
      then
        (* if deallocating, check that there is no active call_id left *)
        if dealloc_no_active_barrier access stack' bar then Some stack else None
      else access1 stack' bor access bar
  (* a Read can match Shr with both UniqB/ShrB *)
  | Shr :: stack', _, AccessRead => Some stack
  (* Shr matches ShrB *)
  | Shr :: stack', ShrB _, _ =>
      (* if deallocating, check that there is no active call_id left *)
      if dealloc_no_active_barrier access stack' bar then Some stack else None
  (* no current match, continue *)
  | _ :: stack', _, _ => access1 stack' bor access bar
  (* empty stack, no matches *)
  | [], _, _ => None
  end.

Inductive accessN
  (α: stacks) (β: barriers) (bor: borrow) (kind: access_kind) (l: loc)
  : nat → stacks → Prop :=
| ACNBase
  : accessN α β bor kind l O α
| ACNRecursive n stack bors' α'
    (STACK: α !! l = Some stack)
    (ACC1 : access1 stack.(borrows) bor kind β = Some bors')
    (ACCN : accessN (<[l := mkBorStack bors' stack.(frozen_since) ]> α) β bor kind (l +ₗ 1) n α')
  : accessN α β bor kind l (S n) α'.

(* Return the matched item's index if found (0 is the bottom of the stack). *)
Fixpoint match_deref (stack: list stack_item) (bor: borrow) : option nat :=
  match stack, bor with
  | Uniq t1 :: stack', UniqB t2 =>
      (* Uniq t1 matches UniqB t2 *)
      if (decide (t1 = t2))
      then Some (length stack')
      else match_deref stack' bor
  | Shr :: stack', ShrB _ =>
      (* Shr matches ShrB *)
      Some (length stack')
  | _ :: stack', _ =>
      (* no current match, continue *)
      match_deref stack' bor
  | [], _ =>
      (* empty stack, no matches *)
      None
  end.

(** Check for derefs *)
(* Return None if the check fails.
 * Return Some None if the stack is frozen.
 * Return Some (Some i) where i is the matched item's index. *)
Definition check_deref1
  (stack: bor_stack) (bor: borrow) (kind: ref_kind) : option (option nat) :=
  match bor, stack.(frozen_since), kind with
  | ShrB (Some _), _, UniqueRef =>
      (* no shared tag for unique ref *)
      None
  | ShrB (Some _), None, FrozenRef =>
      (* no shared tag and frozen ref on unfrozen stack *)
      None
  | ShrB (Some t1), Some t2, FrozenRef =>
      (* shared tag, frozen stack and frozen ref:
          stack must be frozen at t2 before the tag t1 *)
      if decide (t2 <= t1) then Some None else None
  | ShrB None, Some _, _ =>
      (* raw tag, frozen stack: good *)
      Some None
  | _ , _, _ =>
      (* otherwise, look for the bor in the stack *)
      (match_deref stack.(borrows) bor) ≫= (Some ∘ Some)
  end.

Inductive check_derefN
  (α: stacks) (bor: borrow) (kind: ref_kind) (l: loc)
  : nat → Prop :=
| DRNBase
  : check_derefN α bor kind l O
| DRNRecursive n stack
    (STACK: α !! l = Some stack)
    (DR1 : is_Some (check_deref1 stack bor kind))
    (DRN : check_derefN α bor kind (l +ₗ 1) n)
  : check_derefN α bor kind l (S n).

(** Reborrow *)

Definition bor_redundant_check
  (stack: bor_stack) (bor': borrow) (kind: ref_kind) (idx: option time): Prop :=
  match (check_deref1 stack bor' kind) with
  | Some idx' => match idx, idx' with
                 | _, None => True
                 | Some t, Some t' => t <= t'
                 | None, Some _ => False
                 end
  | None => False
  end.
Instance bor_redundant_check_dec stack bor' kind idx :
  Decision (bor_redundant_check stack bor' kind idx).
Proof.
  rewrite /bor_redundant_check.
  destruct (check_deref1 stack bor' kind) as [idx'|]; [|solve_decision].
  destruct idx as [t|], idx' as [t'|]; solve_decision.
Qed.

Definition add_barrier (stack: list stack_item) (c: call_id) : list stack_item :=
  match stack with
  | FnBarrier c' :: stack' =>
      (* Avoid stacking multiple identical barriers on top of each other. *)
      if decide (c' = c) then stack else FnBarrier c :: stack
  | _ => FnBarrier c :: stack
  end.

Inductive push_borrow (stack: bor_stack) : borrow → ref_kind → bor_stack → Prop :=
| PBShrFrozen (t t': time)
    (* Already frozen earlier at t, nothing to do *)
    (FROZEN: stack.(frozen_since) = Some t)
    (EARLIER: (t ≤ t')%nat)
  : push_borrow stack (ShrB (Some t')) FrozenRef stack
| PBShrFreeze (t': time)
    (* Not frozen, freeze now at t' *)
    (UNFROZEN: stack.(frozen_since) = None)
  : push_borrow stack (ShrB (Some t')) FrozenRef (mkBorStack stack.(borrows) (Some t'))
| PBPushShr ot kind bors'
    (* Not frozen, try to add new item, unless it's redundant *)
    (UNFROZEN: stack.(frozen_since) = None)
    (NOTFREEZE: kind ≠ FrozenRef)
    (STACK: bors' = match stack.(borrows) with
                    | Shr :: _ => stack.(borrows)
                    | _ => Shr :: stack.(borrows)
                    end)
  : push_borrow stack (ShrB ot) kind (mkBorStack bors' None)
| PBPushUniq t' kind
    (* Not frozen, add new item *)
    (UNFROZEN: stack.(frozen_since) = None)
    (NOTFREEZE: kind ≠ FrozenRef)
  : push_borrow stack (UniqB t') kind (mkBorStack (Uniq t' :: stack.(borrows)) None).

Inductive reborrow1
  (stack: bor_stack) (bor: borrow) (kind: ref_kind) (β: barriers) :
  option call_id → borrow → bor_stack → Prop :=
| RB1Redundant bor' ptr_idx
    (OLD_DEREF: check_deref1 stack bor kind = Some ptr_idx)
    (REDUNDANT: bor_redundant_check stack bor' kind ptr_idx)
    (SHARED   : is_shared bor')
  : reborrow1 stack bor kind β None bor' stack
| RB1NonRedundantNoBarrier bor' bors' stack' ptr_idx
    (OLD_DEREF : check_deref1 stack bor kind = Some ptr_idx)
    (REDUNDANT : ¬ bor_redundant_check stack bor' kind ptr_idx)
    (REACTIVATE: access1 stack.(borrows) bor (to_access_kind kind) β = Some bors')
    (PUSH: push_borrow (mkBorStack bors' None) bor' kind stack')
  : reborrow1 stack bor kind β None bor' stack'
| RB1NonRedundantBarrier c bor' bors' stack'
    (OLD_DEREF : is_Some (check_deref1 stack bor kind))
    (REACTIVATE: access1 stack.(borrows) bor (to_access_kind kind) β = Some bors')
    (PUSH: push_borrow (mkBorStack (add_barrier bors' c) None) bor' kind stack')
  : reborrow1 stack bor kind β (Some c) bor' stack'.

Inductive reborrowN
  (α: stacks) (β: barriers) (bor: borrow) (kind: ref_kind)  (l: loc)
  : nat → option call_id → borrow → stacks → Prop :=
| RBNBase bar bor'
  : reborrowN α β bor kind l O bar bor' α
| RBNRecursive n stack stack' bar bor' α'
    (STACK: α !! l = Some stack)
    (REBOR1: reborrow1 stack bor kind β bar bor' stack')
    (REBORN: reborrowN (<[ l := stack' ]> α) β bor kind (l +ₗ 1) n bar bor' α')
  : reborrowN α β bor kind l (S n) bar bor' α'.

(** Instrumented step for the stacked borrows *)
(* This ignores CAS for now. *)
Inductive instrumented_step :
  mem → stacks → barriers → option event → mem → stacks → Prop :=
| DefaultIS σ α β :
    instrumented_step σ α β None σ α
| AllocHeapIS σ σ' α β l n :
    instrumented_step σ α β
                      (Some $ AllocEvt l n (ShrB None)) σ'
                      (init_stacks l (Pos.to_nat n) α Shr)
| AllocStackIS σ σ' α β t x n :
    instrumented_step σ α β
                      (Some $ AllocEvt x n (UniqB t)) σ'
                      (init_stacks x (Pos.to_nat n) α (Uniq t))
| ReadFrozenIS σ α β l v lbor stack :
    (α !! l = Some stack) →
    is_frozen stack →
    instrumented_step σ α β
                      (Some $ ReadEvt l lbor v) σ α
| ReadUnfrozenIS σ α β l v lbor stack stack':
    (α !! l = Some stack) →
    (¬ is_frozen stack) →
    (access1 stack.(borrows) lbor AccessRead β = Some stack') →
    instrumented_step σ α β
                      (Some $ ReadEvt l lbor v) σ
                      (<[ l := mkBorStack stack' None ]> α)
| WriteIS σ σ' α β l v lbor stack stack' :
    (α !! l = Some stack) →
    (access1 stack.(borrows) lbor AccessWrite β = Some stack') →
    instrumented_step σ α β
                      (Some $ WriteEvt l lbor v) σ'
                      (<[ l := mkBorStack stack' None ]> α)
| DeallocIS σ σ' α β l n lbor stack stack' :
    (α !! l = Some stack) →
    (access1 stack.(borrows) lbor AccessDealloc β = Some stack') →
    instrumented_step σ α β
                      (Some $ DeallocEvt l n lbor) σ'
                      (<[ l := mkBorStack stack' None ]> α)
| DerefIS σ α β l n lbor kind :
    check_derefN α lbor kind l n →
    instrumented_step σ α β
                      (Some $ DerefEvt l lbor kind) σ α
| RetagIS σ α α' β x l n bor bor' rkind rtkind bar :
    (σ !! x = Some $ LitV $ LitLoc l bor) →
    (reborrowN α β bor rkind l (Pos.to_nat n) bar bor' α') →
    instrumented_step σ α β
                      (Some $ RetagEvt x l n bor bor' rtkind bar)
                      (<[ x := LitV $ LitLoc l bor' ]> σ) α'.
