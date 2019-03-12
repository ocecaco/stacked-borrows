From iris.program_logic Require Export language ectx_language ectxi_language.
From stdpp Require Export strings.
From stdpp Require Import gmap infinite.
Set Default Proof Using "Type".

Module bor_lang.
Open Scope Z_scope.

(** Locations *)
Definition block : Set := positive.
Definition loc : Set := block * Z.

Bind Scope loc_scope with loc.
Delimit Scope loc_scope with L.
Open Scope loc_scope.

Definition shift_loc (l : loc) (z : Z) : loc := (l.1, l.2 + z).

Notation "l +ₗ z" := (shift_loc l%L z%Z)
  (at level 50, left associativity) : loc_scope.

Notation time := nat (only parsing).
Notation call_id := nat (only parsing).

(** Types *)
(* Reference types *)
Inductive mutability := Mutable | Immutable.
Inductive ref_kind :=
  | UniqueRef (* &mut *)
  | FrozenRef (* & *)
  | RawRef    (* * (raw) or & to UnsafeCell, or Box *)
  .
Definition is_unique_ref (kind: ref_kind) : bool :=
  match kind with UniqueRef => true | _ => false end.

Inductive pointer_kind := RefPtr (mut: mutability) | RawPtr | BoxPtr .
Inductive type :=
  | Scala (sz: nat)
  | Reference (kind: pointer_kind) (T: type)
  | Unsafe (T: type)
  | Union (T1: type) (T2: type)
  | Product (T1: type) (T2: type)
  (* TODO: | Sum (T1: type) (T2: type) *)
  .

Fixpoint tsize (T: type) : nat :=
  match T with
  | Scala sz => sz
  | Reference _ _ => 1%nat     (* We do not go beyond pointers *)
  | Unsafe T => tsize T
  | Union T1 T2 => Nat.max (tsize T1) (tsize T2)
  | Product T1 T2 => (tsize T1) + (tsize T2)
  end.

(* Type doesn't contain UnsafeCells. *)
Fixpoint is_freeze (T: type) : bool :=
  match T with
  | Scala _ | Reference _ _ => true
  | Unsafe _ => false
  | Union T1 T2 | Product T1 T2 => is_freeze T1 && is_freeze T2
  end.

(** Instrumented states *)
(* Borrow types *)
Inductive borrow :=
  | UniqB (t: time)           (* A unique (mutable) reference. *)
  | AliasB (ot : option time) (* An aliasing reference, also for raw pointers
                                 whose ot is None. *)
  .

Definition is_unique (bor: borrow) :=
  match bor with | UniqB _ => true | _ => false end.
Definition is_aliasing (bor: borrow) :=
  match bor with | AliasB _ => true | _ => false end.
Notation borrow_default := (AliasB None).

(* Retag types *)
Inductive retag_kind := | FnEntry (c: call_id) | TwoPhase | RawRt | Default.

(* Barrier tracker: track if a call_id is active, i.e. the call is still running *)
Definition barriers := gmap call_id bool.

(* Stacks of borrows. *)
Inductive stack_item :=
  | Uniq (t: time)            (* A unique reference may mutate this location. *)
  | Raw                       (* The location has been mutably shared, for both
                                 raw pointers and unfrozen shared refs. *)
  | FnBarrier (ci : call_id)  (* A barrier for a call *)
  .

Record bstack := mkBorStack {
  borrows       : list stack_item;  (* used as a stack, never empty *)
  frozen_since  : option time;      (* frozen item that is always on top *)
}.
Definition is_frozen (s : bstack) : Prop := is_Some s.(frozen_since).
Definition bstacks := gmap loc bstack.

Implicit Type (α: bstacks) (β: barriers) (t: time) (c: call_id) (T: type).


(*** BASE SEMANTICS --------------------------------------------------------***)

(** Unary/Binary ops *)
Inductive bin_op :=
  | AddOp     (* + addition       *)
  | SubOp     (* - subtraction    *)
(* | MulOp     (* * multiplication *)
  | DivOp     (* / division       *)
  | RemOp     (* % modulus        *)
  | BitXorOp  (* ^ bit xor        *)
  | BitAndOp  (* & bit and        *)
  | BitOrOp   (* | bit or         *)
  | ShlOp     (* << shift left    *)
  | ShrOp     (* >> shift right   *) *)
  | EqOp      (* == equality      *)
  | LtOp      (* < less than      *)
  | LeOp      (* <= less than or equal to *)
(* | NeOp      (* != not equal to  *)
  | GeOp      (* >= greater than or equal to *)
  | GtOp      (* > greater than   *) *)
  | OffsetOp  (* . offset         *)
  .

(** Base values *)
Inductive lit :=
| LitPoison | LitLoc (l: loc) (tag: borrow) | LitInt (n : Z).

(** Allocation destination *)
Inductive alloc_mod := Heap | Stack.

(** Binders for lambdas: list of formal arguments to functions *)
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

(** Expressions *)
Inductive expr :=
(* base values *)
| Lit (l : lit)
(* base lambda calculus *)
| Var (x : string)
| App (e : expr) (el : list expr)
| Rec (f : binder) (xl : list binder) (e : expr)
(* bin op *)
| BinOp (op : bin_op) (e1 e2 : expr)
(* lvalue *)
| Place (l: loc) (tag: borrow)    (* A place is a tagged pointer: every access
                                     to memory revolves around a place. *)
| Deref (e: expr) (T: type) (mut: option mutability)
                                  (* Deference a pointer `e` into a place
                                     presenting the location that `e` points to.
                                     The location has type `T` and the pointer
                                     has mutable kind `mut`. *)
| Ref (e: expr)                   (* Turn a place `e` into a pointer value. *)
| Field (e1 e2: expr)             (* Create a place that points to a component
                                     of the place `e1`. *)
(* mem op *)
| Read (e : expr)                 (* Read from the place `e` *)
| Write (e1 e2: expr)             (* Write the value `e2` to the place `e1` *)
| CAS (e0 e1 e2 : expr)           (* CAS the value `e2` for `e1` to the place `e0` *)
| Alloc (T: type) (amod: alloc_mod) (* Allocate a place of type `T` *)
| Free (e : expr) (T: type)       (* Free the place `e` of type `T` *)
(* function call tracking *)
| NewCall                         (* Issue a fresh id for the call *)
| EndCall (e: expr)               (* End the call with id `e` *)
(* retag *)
| Retag (e: expr) (T: type) (kind: retag_kind)
                                  (* Retag the place `e` of type `T` with retag
                                     kind `kind`. *)
(* case *)
| Case (e : expr) (el : list expr)
(* concurrency *)
| Fork (e : expr)
.

Bind Scope expr_scope with expr.
Delimit Scope expr_scope with E.
Arguments App _%E _%E.
Arguments Case _%E _%E.
Arguments BinOp _ _%E _%E.
Arguments Case _%E _%E.
Arguments Fork _%E.
Arguments Read _%E.
Arguments Write _%E _%E.
Arguments CAS _%E _%E _%E.
Arguments Free _%E _.
Arguments Deref _%E _ _.
Arguments Ref _%E.
Arguments Field _%E _%E.
Arguments Retag _%E _ _.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Lit _ | Place _ _ | Alloc _ _ | NewCall => true
  | Var x => bool_decide (x ∈ X)
  | Rec f xl e => is_closed (f :b: xl +b+ X) e
  | BinOp _ e1 e2 | Write e1 e2  | Field e1 e2 =>
    is_closed X e1 && is_closed X e2
  | App e el | Case e el => is_closed X e && forallb (is_closed X) el
  | Read e | Deref e _ _ | Ref e | Free e _ | EndCall e | Retag e _ _ | Fork e =>
      is_closed X e
  | CAS e0 e1 e2 => is_closed X e0 && is_closed X e1 && is_closed X e2
  end.

Class Closed (X : list string) (e : expr) := closed : is_closed X e.
Instance closed_proof_irrel env e : ProofIrrel (Closed env e).
Proof. rewrite /Closed. apply _. Qed.
Instance closed_decision env e : Decision (Closed env e).
Proof. rewrite /Closed. apply _. Qed.

Inductive immediate :=
| LitV (l : lit)
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
  | PlaceV l tag => Place l tag
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
  | Alloc T amod => Alloc T amod
  | Free e T => Free (subst x es e) T
  | Deref e T mut => Deref (subst x es e) T mut
  | Ref e => Ref (subst x es e)
  | Field e1 e2 => Field (subst x es e1) (subst x es e2)
  | NewCall => NewCall
  | EndCall e => EndCall (subst x es e)
  | Retag e T kind => Retag (subst x es e) T kind
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
| FreeCtx (T: type)
| DerefCtx (T: type) (mut: option mutability)
| RefCtx
| FieldLCtx (e : expr)
| FieldRCtx (v : val)
| EndCallCtx
| RetagCtx (T: type) (kind: retag_kind)
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
  | FreeCtx T => Free e T
  | DerefCtx T mut => Deref e T mut
  | RefCtx => Ref e
  | FieldLCtx e2 => Field e e2
  | FieldRCtx v1 => Field (of_val v1) e
  | EndCallCtx => EndCall e
  | RetagCtx T kind => Retag e T kind
  | CaseCtx el => Case e el
  end.

(** Main state: a heap of immediates. *)
Definition mem := gmap loc immediate.
Implicit Type (h: mem).

(** The stepping relation *)
(* Be careful to make sure that poison is always stuck when used for anything
   except for reading from or writing to memory! *)
Definition Z_of_bool (b : bool) : Z :=
  if b then 1 else 0.

Definition lit_of_bool (b : bool) : lit :=
  LitInt $ Z_of_bool b.

Fixpoint init_mem (l:loc) (n:nat) h : mem :=
  match n with
  | O => h
  | S n => <[l:=LitV LitPoison]>(init_mem (l +ₗ 1) n h)
  end.

Fixpoint free_mem (l:loc) (n:nat) h : mem :=
  match n with
  | O => h
  | S n => delete l (free_mem (l +ₗ 1) n h)
  end.

Inductive lit_eq h : lit → lit → Prop :=
(* No refl case for poison *)
| IntRefl z : lit_eq h (LitInt z) (LitInt z)
| LocRefl l tag1 tag2 : lit_eq h (LitLoc l tag1) (LitLoc l tag2)
(* Comparing unallocated pointers can non-deterministically say they are equal
   even if they are not.  Given that our `free` actually makes addresses
   re-usable, this may not be strictly necessary, but it is the most
   conservative choice that avoids UB (and we cannot use UB as this operation is
   possible in safe Rust).  See
   <https://internals.rust-lang.org/t/comparing-dangling-pointers/3019> for some
   more background. *)
| LocUnallocL l1 l2 tag1 tag2 :
    h !! l1 = None →
    lit_eq h (LitLoc l1 tag1) (LitLoc l2 tag2)
| LocUnallocR l1 l2 tag1 tag2 :
    h !! l2 = None →
    lit_eq h (LitLoc l1 tag1) (LitLoc l2 tag2).

Inductive lit_neq : lit → lit → Prop :=
| IntNeq z1 z2 :
    z1 ≠ z2 → lit_neq (LitInt z1) (LitInt z2)
| LocNeq l1 l2 tag1 tag2 :
    l1 ≠ l2 → lit_neq (LitLoc l1 tag1) (LitLoc l2 tag2)
| LocNeqNullR l tag :
    lit_neq (LitLoc l tag) (LitInt 0)
| LocNeqNullL l tag :
    lit_neq (LitInt 0) (LitLoc l tag).

Inductive bin_op_eval h : bin_op → lit → lit → lit → Prop :=
| BinOpPlus z1 z2 :
    bin_op_eval h AddOp (LitInt z1) (LitInt z2) (LitInt (z1 + z2))
| BinOpMinus z1 z2 :
    bin_op_eval h SubOp (LitInt z1) (LitInt z2) (LitInt (z1 - z2))
| BinOpLe z1 z2 :
    bin_op_eval h LeOp (LitInt z1) (LitInt z2) (lit_of_bool $ bool_decide (z1 ≤ z2))
| BinOpLt z1 z2 :
    bin_op_eval h LtOp (LitInt z1) (LitInt z2) (lit_of_bool $ bool_decide (z1 < z2))
| BinOpEqTrue l1 l2 :
    lit_eq h l1 l2 → bin_op_eval h EqOp l1 l2 (lit_of_bool true)
| BinOpEqFalse l1 l2 :
    lit_neq l1 l2 → bin_op_eval h EqOp l1 l2 (lit_of_bool false)
| BinOpOffset l z tag :
    bin_op_eval h OffsetOp (LitLoc l tag) (LitInt z) (LitLoc (l +ₗ z) tag).

Definition stuck_term := App (Lit $ LitInt 0) [].

Inductive event :=
| AllocEvt (l : loc) (n: positive) (lbor: borrow) (amod: alloc_mod)
| DeallocEvt (l: loc) (n : positive) (lbor: borrow)
| ReadEvt (l: loc) (lbor: borrow) (v: immediate)
| WriteEvt (l: loc) (lbor: borrow) (v: immediate)
| DerefEvt (l: loc) (lbor: borrow) (T: type) (mut: option mutability)
| NewCallEvt (call: call_id)
| EndCallEvt (call: call_id)
| RetagEvt (x: loc) (T: type) (kind: retag_kind)
.

Inductive base_step :
  expr → mem → option event → expr → mem → list expr → Prop :=
| BinOpBS op l1 l2 l' h :
    bin_op_eval h op l1 l2 l' →
    base_step (BinOp op (Lit l1) (Lit l2)) h None (Lit l') h []
| BetaBS f xl e e' el h :
    Forall (λ ei, is_Some (to_val ei)) el →
    Closed (f :b: xl +b+ []) e →
    subst_l (f::xl) (Rec f xl e :: el) e = Some e' →
    base_step (App (Rec f xl e) el) h None e' h []
| ReadBS l v lbor h :
    h !! l = Some v →
    base_step (Read (Place l lbor)) h
              (Some $ ReadEvt l lbor v)
              (of_val (ImmV v)) h
              []
| WriteBS l e v lbor h :
    is_Some (h !! l) →
    to_val e = Some (ImmV v) →
    base_step (Write (Place l lbor) e) h
              (Some $ WriteEvt l lbor v)
              (Lit LitPoison) (<[l:=v]>h)
              []
| AllocBS T l lbor amod h :
    (∀ m, h !! (l +ₗ m) = None) →
    base_step (Alloc T amod) h
              (Some $ AllocEvt l (Pos.of_nat (tsize T)) lbor amod)
              (Place l lbor) (init_mem l (tsize T) h)
              []
| FreeBS T l lbor h :
    (∀ m, is_Some (h !! (l +ₗ m)) ↔ 0 ≤ m < tsize T) →
    base_step (Free (Place l lbor) T) h
              (Some $ DeallocEvt l (Pos.of_nat (tsize T)) lbor)
              (Lit LitPoison) (free_mem l (tsize T) h)
              []
| NewCallBS call h:
    base_step NewCall h
              (Some $ NewCallEvt call) (Lit $ LitInt call) h []
| EndCallBS call h:
    (0 ≤ call) →
    base_step (EndCall (Lit $ LitInt call)) h
              (Some $ EndCallEvt (Z.to_nat call)) (Lit LitPoison) h []
| RefBS l lbor h :
    is_Some (h !! l) →
    base_step (Ref (Place l lbor)) h None (Lit (LitLoc l lbor)) h []
| DerefBS l lbor mut T h :
    is_Some (h !! l) →
    base_step (Deref (Lit (LitLoc l lbor)) T mut) h
              (Some $ DerefEvt l lbor T mut)
              (Place l lbor) h
              []
| FieldBS l lbor z h :
    base_step (Field (Place l lbor) (Lit $ LitInt z)) h
              None (Place (l +ₗ z) lbor) h []
| RetagBS x xbor T kind h:
    base_step (Retag (Place x xbor) T kind) h
              (Some $ RetagEvt x T kind) (Lit LitPoison) h []
| CaseBS i el e h :
    0 ≤ i →
    el !! (Z.to_nat i) = Some e →
    base_step (Case (Lit $ LitInt i) el) h None e h []
| ForkBS e h:
    base_step (Fork e) h None (Lit LitPoison) h [e].

(*** STACKED BORROWS SEMANTICS ---------------------------------------------***)

(* Initialize [l, l + n) with non-frozen singleton stacks of si *)
Fixpoint init_stacks (l:loc) (n:nat) α (si: stack_item) : bstacks :=
  match n with
  | O => α
  | S n => <[l:= mkBorStack [si] None]>(init_stacks (l +ₗ 1) n α si)
  end.

(** Dealloc check for no active barrier on the stack *)
Definition is_active β (c: call_id) : bool :=
  bool_decide (β !! c = Some true).

Definition is_active_barrier β (si: stack_item) :=
  match si with
  | FnBarrier c => β !! c = Some true
  | _ => False
  end.
Instance is_active_barrier_dec β : Decision (is_active_barrier β si).
Proof. move => [?| |?] /=; solve_decision. Qed.

(* Return the index of the found top active call *)
Definition find_top_active_call (stack: list stack_item) β :
  option nat := (list_find (is_active_barrier β) stack) ≫= (Some ∘ fst).

Inductive access_kind := AccessRead | AccessWrite | AccessDealloc.
Definition to_access_kind (kind : ref_kind): access_kind :=
  match kind with
  | UniqueRef => AccessWrite
  | _ => AccessRead
  end.
Definition dealloc_no_active_barrier
  (access: access_kind) (stack: list stack_item) β : bool :=
  match access with
  | AccessDealloc =>
      if find_top_active_call stack β then false else true
  | _ => true
  end.

(** Access check *)
(* Check for access per location.
 * Return None if the check fails.
 * Return Some stack' where stack' is the new stack. *)
Fixpoint access1'
  (stack: list stack_item) (bor: borrow) (access: access_kind) β
  : option (list stack_item) :=
  match stack, bor, access with
  (* try to pop barriers *)
  | FnBarrier c :: stack', _, _ =>
      if (is_active β c)
      (* cannot pop an active barrier *)
      then None
      (* otherwise, just pop *)
      else access1' stack' bor access β
  (* Uniq t matches UniqB t *)
  |  Uniq t1 :: stack', UniqB t2, _ =>
      if (decide (t1 = t2))
      (* if matched *)
      then
        (* if deallocating, check that there is no active call_id left *)
        if dealloc_no_active_barrier access stack' β then Some stack else None
      (* otherwise, just pop *)
      else access1' stack' bor access β
  (* a Read can match Raw with both UniqB/AliasB *)
  | Raw :: stack', _, AccessRead => Some stack
  (* Raw matches AliasB *)
  | Raw :: stack', AliasB _, _ =>
      (* if deallocating, check that there is no active call_id left *)
      if dealloc_no_active_barrier access stack' β then Some stack else None
  (* no current match, pop and continue *)
  | _ :: stack', _, _ => access1' stack' bor access β
  (* empty stack, no matches *)
  | [], _, _ => None
  end.

(* This implements Stack::access. *)
Definition access1 β (stack: bstack) bor (kind: access_kind) : option bstack :=
  match stack.(frozen_since), kind with
  (* accept all reads if frozen *)
  | Some _, AccessRead => Some stack
  (* otherwise, unfreeze *)
  | _,_ => match access1' stack.(borrows) bor kind β with
           | Some stack' => Some (mkBorStack stack' None)
           | _ => None
           end
  end.

(* Perform the access check on a block of continuous memory.
 * This implements Stacks::access. *)
Fixpoint accessN α β l (bor: borrow) (n: nat) kind : option bstacks :=
  match n with
  | O => Some α
  | S n =>
      let l' := (l +ₗ n) in
      match (α !! l') with
      | Some stack => match (access1 β stack bor kind) with
                      | Some stack' =>
                          accessN (<[l' := stack']> α) β l bor n kind
                      | _ => None
                      end
      | _ => None
      end
  end.

(** Deref check *)
(* Find the item that matches `bor`, then return its index (0 is the bottom of
 * the stack). *)
Fixpoint match_deref (stack: list stack_item) (bor: borrow) : option nat :=
  match stack, bor with
  | Uniq t1 :: stack', UniqB t2 =>
      if (decide (t1 = t2))
      (* Uniq t1 matches UniqB t2 *)
      then Some (length stack')         (* this is the index of Uniq t1 *)
      (* otherwise, pop and continue *)
      else match_deref stack' bor
  | Raw :: stack', AliasB _ =>
      (* Raw matches AliasB *)
      Some (length stack')              (* this is the index of Raw *)
  | _ :: stack', _ =>
      (* no current match, continue. This one ignores barriers! *)
      match_deref stack' bor
  | [], _ =>
      (* empty stack, no matches *)
      None
  end.

(* Return None if the check fails.
 * Return Some None if the stack is frozen.
 * Return Some (Some i) where i is the matched item's index.
 * This implements Stack::deref. *)
Definition deref1
  (stack: bstack) (bor: borrow) (kind: ref_kind) : option (option nat) :=
  match bor, stack.(frozen_since), kind with
  | AliasB (Some _), _, UniqueRef =>
      (* no shared tag for unique ref *)
      None
  | AliasB (Some t1), Some t2, _ =>
      (* shared tag, frozen stack: stack must be frozen at t2 before the tag's t1 *)
      if decide (t2 <= t1) then Some None else None
  | AliasB _, Some _, _ =>
      (* raw tag, frozen stack: good *)
      Some None
  | _ , _, _ =>
      (* otherwise, look for bor on the stack *)
      (match_deref stack.(borrows) bor) ≫= (Some ∘ Some)
  end.

(* Perform the deref check on a block of continuous memory.
 * This implements Stacks::deref. *)
Fixpoint derefN α l (bor: borrow) (n: nat) (kind: ref_kind) : option unit :=
match n with
| O => Some ()
| S n =>
    let l' := (l +ₗ n) in
    match (α !! l') with
    | Some stack => if (deref1 stack bor kind) then derefN α l bor n kind else None
    | _ => None
    end
end.

Definition unsafe_action
  {A: Type} (f: A → loc → nat → bool → option A) (a: A) (l: loc)
  (last frozen_size unsafe_size: nat) :
  option (A * (nat * nat)) :=
  (* anything between the last UnsafeCell and this UnsafeCell is frozen *)
  match f a (l +ₗ last) frozen_size true with
  | Some a' =>
      (* This UnsafeCell is not frozen *)
      let cur_ptr := (last + frozen_size)%nat in
      match f a' (l +ₗ cur_ptr) unsafe_size false with
      | Some a'' => Some (a'', ((cur_ptr + unsafe_size)%nat, O))
      | _ => None
      end
  | _ => None
  end.

(* visit the type left-to-right, where `last` is the offset of `l` from the last
UnsafeCell, and `cur_dist` is the distance between `last` and the current offset
which is the start of the sub-type `t`. `a` of type A is the accumulator for the
visit. *)
Fixpoint visit_freeze_sensitive' {A: Type}
  (l: loc) (T: type) (f: A → loc → nat → bool → option A) (a: A)
  (last cur_dist: nat) :
  option (A * (nat * nat)) :=
  match T with
  | Scala n => Some (a, (last, cur_dist + n)%nat)
  | Reference _ _ => Some (a, (last, S cur_dist))
  | Unsafe T =>
      (* apply the action `f` and return new `last` and `cur_dist` *)
      unsafe_action f a l last cur_dist (tsize T)
  | Union _ _ =>
      (* If it's a union, look at the type to see if there is Unsafe *)
      if is_freeze T
      (* No UnsafeCell, continue *)
      then Some (a, (last, cur_dist + (tsize T))%nat)
      (* There can be UnsafeCell, perform `f a _ _ false` on the whole block *)
      else unsafe_action f a l last cur_dist (tsize T)
  | Product T1 T2 =>
      (* this implements left-to-right search on the type, which guarantees
         that the indices are increasing. *)
      match visit_freeze_sensitive' l T1 f a last cur_dist with
      | Some (a', (last', cur_dist')) =>
          visit_freeze_sensitive' l T2 f a' last' cur_dist'
      | _ => None
      end
  end.

Definition visit_freeze_sensitive {A: Type}
  (l: loc) (t: type) (f: A → loc → nat → bool → option A) (a: A) : option A :=
  match visit_freeze_sensitive' l t f a O O with
  | Some (a', (last', cur_dist')) =>
      (* the last block is not inside UnsafeCell *)
      f a' (l +ₗ last') cur_dist' true
  | _ => None
  end.

(* Perform the deref check on a block of continuous memory where some of them
 * can be inside UnsafeCells, which are described by the type `t` of the block.
 * This implements EvalContextExt::ptr_dereference. *)
(* TODO?: bound check of l for size (tsize t)? alloc.check_bounds(this, ptr, size)?; *)
Definition ptr_deref α (l: loc) (bor: borrow) T (mut: option mutability) : Prop :=
  match bor, mut with
  | _, None =>
      (* This is a raw pointer, no checks. *)
      True
  | AliasB (Some _), Some mut =>
      (* must be immutable reference *)
      mut = Immutable ∧
      (* We need freeze-sensitive check, depending on whether some memory is in
         UnsafeCell or not *)
      is_Some (
        visit_freeze_sensitive l T
          (λ _ l' sz frozen,
              (* If is in Unsafe, treat as a RawRef, otherwise FrozenRef *)
              let kind := if frozen then FrozenRef else RawRef in
                derefN α l' bor sz kind) ())
  | _, Some mut =>
      (* Otherwise, just treat this as one big chunk. *)
      let kind := match mut with Mutable => UniqueRef | _ => RawRef end in
      is_Some (derefN α l bor (tsize T) kind)
  end.


(** Reborrow *)

(* This implements Stack::barrier. *)
Definition add_barrier (stack: bstack) (c: call_id) : bstack :=
  match stack.(borrows) with
  | FnBarrier c' :: stack' =>
      (* Avoid stacking multiple identical barriers on top of each other. *)
      if decide (c' = c) then stack else mkBorStack (FnBarrier c :: stack') stack.(frozen_since)
  | _ => mkBorStack (FnBarrier c :: stack.(borrows)) stack.(frozen_since)
  end.

(* This implements Stack::create. *)
Definition create_borrow (stack: bstack) bor (kind: ref_kind) : option bstack :=
  match kind with
  | FrozenRef =>
      match bor, stack.(frozen_since) with
      (* Already frozen earlier at t' ≤ t, nothing to do *)
      | AliasB (Some t), Some t' =>
          if (decide (t' ≤ t)%nat) then Some stack else None
      (* Not frozen, freeze now at t *)
      | AliasB (Some t), None => Some (mkBorStack stack.(borrows) (Some t))
      | _, _ => None
      end
  | _ =>
      match bor, stack.(frozen_since) with
      (* Not frozen, add new item *)
      | UniqB t, None => Some (mkBorStack (Uniq t :: stack.(borrows)) None)
      (* Not frozen, try to add new item, unless it's redundant *)
      | AliasB _, None => let bors' := (match stack.(borrows) with
                                        (* avoid stacking multiple Raw's *)
                                        | Raw :: _ => stack.(borrows)
                                        | _ => Raw :: stack.(borrows)
                                        end) in Some (mkBorStack bors' None)
      | _, _ => None
      end
  end.

Definition bor_redundant_check
  (stack: bstack) (bor': borrow) (kind': ref_kind) (idx: option time): Prop :=
  match idx, (deref1 stack bor' kind') with
  | _, Some None => True
  | Some t, Some (Some t') => (t ≤ t')%nat
  | _,_ => False
  end.
Instance bor_redundant_check_dec stack bor' kind idx :
  Decision (bor_redundant_check stack bor' kind idx).
Proof.
  rewrite /bor_redundant_check.
  destruct idx as [t|]; destruct (deref1 stack bor' kind) as [[t'|]|]; solve_decision.
Qed.

Definition reborrow1 (stack: bstack) bor bor' (kind': ref_kind)
  β (bar: option call_id) : option bstack :=
  match (deref1 stack bor kind') with
  | Some ptr_idx =>
      match bar, ptr_idx, deref1 stack bor' kind' with
      | None, _, Some None =>
          (* bor' must be aliasing *)
          if is_aliasing bor' then Some stack else None
      | None, Some ptr_idx, Some (Some new_idx) =>
          if decide (ptr_idx ≤ new_idx)%nat
          then (* bor' must be aliasing *)
               if is_aliasing bor' then Some stack else None
          else (* check for access with bor, then reborrow with bor' *)
               match access1 β stack bor (to_access_kind kind') with
               | Some stack1 => create_borrow stack1 bor' kind'
               | None => None
               end
      | None, _ ,_ =>
          (* check for access with bor, then reborrow with bor' *)
          match access1 β stack bor (to_access_kind kind') with
          | Some stack1 => create_borrow stack1 bor' kind'
          | None => None
          end
      | Some c, _, _ =>
          (* check for access with bor, then add barrier & reborrow with bor' *)
          match access1 β stack bor (to_access_kind kind') with
          | Some stack1 => create_borrow (add_barrier stack1 c) bor' kind'
          | None => None
          end
      end
  | None => None
  end.

Fixpoint reborrowN α β l n bor bor' kind' bar : option bstacks :=
match n with
| O => Some α
| S n =>
    let l' := (l +ₗ n) in
    match (α !! l') with
    | Some stack =>
        match reborrow1 stack bor bor' kind' β bar with
        | Some stack' =>
            reborrowN (<[l' := stack']> α) β l n bor bor' kind' bar
        | _ => None
        end
    | _ => None
    end
end.

(* This implements Stacks::reborrow *)
Definition reborrowBlock α β l n bor bor' kind' bar : option bstacks :=
  if xorb (is_unique bor') (is_unique_ref kind') then None
  else let bar' := match kind' with RawRef => None | _ => bar end in
       reborrowN α β l n bor bor' kind' bar.

(* This implements EvalContextPrivExt::reborrow *)
(* TODO?: alloc.check_bounds(this, ptr, size)?; *)
Definition reborrow α β l bor T (bar: option call_id) bor' :=
  match bor' with
  | AliasB (Some _) =>
      (* We need freeze-sensitive reborrow, depending on whether some memory is
         in UnsafeCell or not *)
      visit_freeze_sensitive l T
          (λ α' l' sz frozen,
              (* If is in Unsafe, treat as a RawRef, otherwise FrozenRef *)
              let kind' := if frozen then FrozenRef else RawRef in
                reborrowBlock α' β l' sz bor bor' kind' bar) α
  | _ =>
      (* Just treat this as one big chunk. *)
      let kind' := if is_unique bor' then UniqueRef else RawRef in
      reborrowBlock α β l (tsize T) bor bor' kind' bar
  end.

(* Retag one pointer *)
(* This implements EvalContextPrivExt::retag_reference *)
Definition retag_ref α β (clock: time) l bor (T: type) (mut: option mutability)
  (bar: option call_id) (two_phase: bool) : option (borrow * bstacks * time) :=
  match tsize T with
  | O => (* Nothing to do for zero-sized types *)
      Some (bor, α, clock)
  | _ => let bor' := match mut with
                     | None => borrow_default | Some Mutable => UniqB clock
                     | Some Immutable => AliasB (Some clock)
                     end in
         (* reborrow bor with bor' *)
         match reborrow α β l bor T bar bor' with
         | Some α' => if two_phase
                      then match mut with
                           | Some Mutable => (* two-phase only for mut borrow *)
                                let bor'' := AliasB (Some (S clock)) in
                                (* second reborrow, no barrier *)
                                match reborrow α' β l bor T None bor'' with
                                | Some α'' => Some (bor'', α'', S (S clock))
                                | None => None
                                end
                           | _ => None
                           end
                      else Some (bor', α', S clock)
         | None => None
         end
  end.

Definition is_two_phase (kind: retag_kind) : bool :=
  match kind with TwoPhase => true | _ => false end.
Definition adding_barrier (kind: retag_kind) : option call_id :=
  match kind with FnEntry c => Some c | _ => None end.
(* This implements EvalContextExt::retag *)
Fixpoint retag h α (clock: time) β x T (kind: retag_kind) :
  option (mem * bstacks * time) :=
  match T with
  | Scala _ | Union _ _ => Some (h, α, clock)
  | Unsafe T => retag h α clock β x T kind
  | Product T1 T2 =>
      match retag h α clock β x T1 kind with
      | Some (h', α', clock') =>
          retag h' α' clock' β (x +ₗ (tsize T1)) T2 kind
      | _ => None
      end
  | Reference pkind Tref =>
      match h !! x with
      | Some (LitV (LitLoc l bor)) =>
            match pkind, kind with
            (* Reference pointer *)
            | RefPtr mut, _ =>
                match retag_ref α β clock l bor Tref (Some mut)
                                (adding_barrier kind) (is_two_phase kind) with
                | Some (bor', α', clock') =>
                    Some (<[x := LitV (LitLoc l bor')]>h, α', clock')
                | _ => None
                end
            (* RawPtr can only be Raw-retagged, no barrier *)
            | RawPtr, RawRt =>
                match retag_ref α β clock l bor Tref None None false with
                | Some (bor', α', clock') =>
                    Some (<[x := LitV (LitLoc l bor')]>h, α', clock')
                | _ => None
                end
            (* Box pointer *)
            | BoxPtr, _ =>
                match retag_ref α β clock l bor Tref (Some Mutable)
                                None (is_two_phase kind) with
                | Some (bor', α', clock') =>
                    Some (<[x := LitV (LitLoc l bor')]>h, α', clock')
                | _ => None
                end
            | _, _ => None
            end
      | _ => None
      end
  end.

(** Instrumented step for the stacked borrows *)
(* This ignores CAS for now. *)
Inductive instrumented_step h α β (clock: time):
  option event → mem → bstacks → barriers → time → Prop :=
| DefaultIS :
    instrumented_step h α β clock None h α β clock
(* This implements EvalContextExt::tag_new_allocation for heap locations. *)
| AllocHeapIS l n :
    instrumented_step h α β clock
                      (Some $ AllocEvt l n borrow_default Heap) h
                      (init_stacks l (Pos.to_nat n) α Raw) β clock
(* This implements EvalContextExt::tag_new_allocation for stack variables. *)
| AllocStackIS t x n :
    (* UniqB t is the first borrow of the variable x,
       used when accessing x directly (not through another pointer) *)
    instrumented_step h α β clock
                      (Some $ AllocEvt x n (UniqB t) Stack) h
                      (init_stacks x (Pos.to_nat n) α (Uniq clock)) β (S clock)
(* This implements AllocationExtra::memory_read, but only for size 1. *)
| Read1IS l v lbor stack stack' :
    (α !! l = Some stack) →
    (access1 β stack lbor AccessRead = Some stack') →
    instrumented_step h α β clock
                      (Some $ ReadEvt l lbor v) h (<[l := stack']> α) β clock
(* This implements AllocationExtra::memory_written, but only for size 1. *)
| WriteIS l v lbor stack stack' :
    (α !! l = Some stack) →
    (access1 β stack lbor AccessWrite = Some stack') →
    instrumented_step h α β clock
                      (Some $ WriteEvt l lbor v) h (<[l := stack']> α) β clock
(* This implements AllocationExtra::memory_deallocated. *)
| DeallocIS α' l n lbor :
    (accessN α β l lbor (Pos.to_nat n) AccessDealloc = Some α') →
    instrumented_step h α β clock
                      (Some $ DeallocEvt l n lbor) h α' β clock
| NewCallIS:
    let call : call_id := fresh (dom (gset call_id) β) in
    instrumented_step h α β clock
                      (Some $ NewCallEvt call) h α (<[call := true]>β) clock
| EndCallIS call
    (ACTIVE: β !! call = Some true) :
    instrumented_step h α β clock
                      (Some $ EndCallEvt call) h α (<[call := false]>β) clock
(* Deferencing a pointer value to a place *)
| DerefIS l lbor T mut
    (DEREF: ptr_deref α l lbor T mut) :
    instrumented_step h α β clock
                      (Some $ DerefEvt l lbor T mut) h α β clock
| RetagIS h' α' clock' x T kind
    (RETAG: retag h α clock β x T kind = Some (h', α', clock')) :
    instrumented_step h α β clock
                      (Some $ RetagEvt x T kind) h' α' β clock'.

(** COMBINED SEMANTICS -------------------------------------------------------*)
Record state := mkState {
  cheap: mem;
  cstk : bstacks;
  cbar : barriers;
  cclk : time;
}.

Implicit Type (σ: state).

Inductive head_step :
  expr → state → list Empty_set → expr → state → list expr → Prop :=
  | BaseHS σ e e' efs h'
      (BaseStep : base_step e σ.(cheap) None e' h' efs)
  : head_step e σ [] e' (mkState h' σ.(cstk) σ.(cbar) σ.(cclk)) efs
  | InstrHS σ e e' evt h0 h' α' β' clock'
      (BaseStep : base_step e σ.(cheap) (Some evt) e' h0 [])
      (InstrStep: instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk) (Some evt) h' α' β' clock')
  : head_step e σ [] e' (mkState h' α' β' clock') [] .

(** Closed expressions *)
Lemma is_closed_weaken X Y e : is_closed X e → X ⊆ Y → is_closed Y e.
Proof.
  revert e X Y. fix FIX 1; destruct e=>X Y/=; try naive_solver.
  - rewrite !andb_True. intros [He Hel] HXY. split. by eauto.
    induction el=>/=; naive_solver.
  - naive_solver set_solver.
  - rewrite !andb_True. intros [He Hel] HXY. split. by eauto.
    induction el=>/=; naive_solver.
Qed.

Lemma is_closed_weaken_nil X e : is_closed [] e → is_closed X e.
Proof. intros. by apply is_closed_weaken with [], list_subseteq_nil. Qed.

Lemma is_closed_subst X e x es : is_closed X e → x ∉ X → subst x es e = e.
Proof.
  revert e X. fix FIX 1; destruct e=> X /=; rewrite ?bool_decide_spec ?andb_True=> He ?;
    repeat case_bool_decide; simplify_eq/=; f_equal;
    try by intuition eauto with set_solver.
  - case He=> _. clear He. induction el=>//=. rewrite andb_True=>?.
    f_equal; intuition eauto with set_solver.
  - case He=> _. clear He. induction el=>//=. rewrite andb_True=>?.
    f_equal; intuition eauto with set_solver.
Qed.

Lemma is_closed_nil_subst e x es : is_closed [] e → subst x es e = e.
Proof. intros. apply is_closed_subst with []; set_solver. Qed.

Lemma is_closed_of_val X v : is_closed X (of_val v).
Proof. apply is_closed_weaken_nil. destruct v as [[]|]; simpl; auto. Qed.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  by destruct v as [[]|]; simplify_option_eq; [| |done|]; repeat f_equal;
    try apply (proof_irrel _).
Qed.
Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=; [|case decide => ? //|]; by intros [= <-]. Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

Lemma is_closed_to_val X e v : to_val e = Some v → is_closed X e.
Proof. intros <-%of_to_val. apply is_closed_of_val. Qed.

Lemma subst_is_closed X x es e :
  is_closed X es → is_closed (x::X) e → is_closed X (subst x es e).
Proof.
  revert e X. fix FIX 1; destruct e=>X //=; repeat (case_bool_decide=>//=);
    try naive_solver; rewrite ?andb_True; intros.
  - set_solver.
  - split; first naive_solver. induction el; naive_solver.
  - eauto using is_closed_weaken with set_solver.
  - eapply is_closed_weaken; first done.
    destruct (decide (BNamed x = f)), (decide (BNamed x ∈ xl)); set_solver.
  - split; first naive_solver. induction el; naive_solver.
Qed.

Lemma subst'_is_closed X b es e :
  is_closed X es → is_closed (b:b:X) e → is_closed X (subst' b es e).
Proof. destruct b; first done. apply subst_is_closed. Qed.

(** Equality and other typeclass stuff *)
Instance binder_countable : Countable binder.
Proof.
  refine (inj_countable'
    (λ b, match b with BAnon => None | BNamed s => Some s end)
    (from_option BNamed BAnon) _); by intros [].
Qed.

Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Instance bin_op_countable : Countable bin_op.
Proof.
  refine (inj_countable'
    (λ o, match o with AddOp => 0 | SubOp => 1 | LeOp => 2 |
                  LtOp => 3 | EqOp => 4 | OffsetOp => 5 end)
    (λ x, match x with 0 => AddOp | 1 => SubOp | 2 => LeOp |
                  3 => LtOp | 4 => EqOp | _ => OffsetOp end) _); by intros [].
Qed.

Instance borrow_eq_dec : EqDecision borrow.
Proof. solve_decision. Defined.
Instance borrow_countable : Countable borrow.
Proof.
  refine (inj_countable
          (λ b, match b with
              | UniqB n => inl n
              | AliasB n => inr n
              end)
          (λ s, match s with
              | inl n => Some $ UniqB n
              | inr n => Some $ AliasB n
              end) _); by intros [].
Qed.

Instance lit_eq_dec : EqDecision lit.
Proof. solve_decision. Defined.
Instance lit_countable : Countable lit.
Proof.
  refine (inj_countable
          (λ v, match v with
              | LitPoison => inl ()
              | LitLoc l bor => inr (inl (l,bor))
              | LitInt n => inr (inr n)
              end)
          (λ s, match s with
              | inl () => Some LitPoison
              | inr (inl (l,bor)) => Some $ LitLoc l bor
              | inr (inr n) => Some $ LitInt n
              end) _); by intros [].
Qed.

Instance mutability_eq_dec : EqDecision mutability.
Proof. solve_decision. Defined.
Instance mutability_countable : Countable mutability.
Proof.
  refine (inj_countable'
    (λ m, match m with Mutable => 0 | Immutable => 1 end)
    (λ x, match x with 0 => Mutable | _ => Immutable end) _); by intros [].
Qed.

Instance pointer_kind_eq_dec : EqDecision pointer_kind.
Proof. solve_decision. Defined.
Instance pointer_kind_countable : Countable pointer_kind.
Proof.
  refine (inj_countable
          (λ k, match k with
              | RefPtr mut => inl $ inl mut
              | RawPtr => inl $ inr ()
              | BoxPtr => inr ()
              end)
          (λ s, match s with
              | inl (inl mut) => Some $ RefPtr mut
              | inl (inr _) => Some  RawPtr
              | inr _ => Some BoxPtr
              end) _); by intros [].
Qed.
Instance retag_kind_eq_dec : EqDecision retag_kind.
Proof. solve_decision. Defined.
Instance retag_kind_countable : Countable retag_kind.
Proof.
  refine (inj_countable
          (λ k, match k with
              | FnEntry n => inl $ inl n
              | TwoPhase => inl $ inr ()
              | RawRt => inr $ inl ()
              | Default => inr $ inr ()
              end)
          (λ s, match s with
              | inl (inl n) => Some $ FnEntry n
              | inl (inr _) => Some TwoPhase
              | inr (inl _) => Some RawRt
              | inr (inr _) => Some Default
              end) _); by intros [].
Qed.
Instance alloc_mod_eq_dec : EqDecision alloc_mod.
Proof. solve_decision. Defined.
Instance alloc_mod_countable : Countable alloc_mod.
Proof.
  refine (inj_countable
          (λ m, match m with
              | Heap => Some ()
              | Stack => None
              end)
          (λ s, match s with
              | Some _ => Some Heap
              | None => Some Stack
              end) _); by intros [].
Qed.

Instance type_eq_dec : EqDecision type.
Proof. solve_decision. Defined.
Instance type_countable : Countable type.
Proof.
  refine (inj_countable'
    (fix go T := match T with
     | Scala sz => GenNode 0 [GenLeaf $ inl sz]
     | Reference kind T => GenNode 1 [GenLeaf $ inr kind; go T]
     | Unsafe T => GenNode 2 [go T]
     | Union T1 T2 => GenNode 3 [go T1; go T2]
     | Product T1 T2 => GenNode 4 [go T1; go T2]
     end)
    (fix go s := match s with
     | GenNode 0 [GenLeaf (inl sz)] => Scala sz
     | GenNode 1 [GenLeaf (inr kind); T] => Reference kind (go T)
     | GenNode 2 [T] => Unsafe (go T)
     | GenNode 3 [T1; T2] => Union (go T1) (go T2)
     | GenNode 4 [T1; T2] => Product (go T1) (go T2)
     | _ => Scala 0
     end) _).
  fix FIX 1. intros []; f_equal=>//.
Qed.

Fixpoint expr_beq (e : expr) (e' : expr) : bool :=
  let fix expr_list_beq el el' :=
    match el, el' with
    | [], [] => true
    | eh::eq, eh'::eq' => expr_beq eh eh' && expr_list_beq eq eq'
    | _, _ => false
    end
  in
  match e, e' with
  | Lit l, Lit l' => bool_decide (l = l')
  | Var x, Var x' => bool_decide (x = x')
  | App e el, App e' el' | Case e el, Case e' el' =>
    expr_beq e e' && expr_list_beq el el'
  | Rec f xl e, Rec f' xl' e' =>
    bool_decide (f = f') && bool_decide (xl = xl') && expr_beq e e'
  | BinOp op e1 e2, BinOp op' e1' e2' =>
    bool_decide (op = op') && expr_beq e1 e1' && expr_beq e2 e2'
  | Place l bor, Place l' bor' => bool_decide (l = l') && bool_decide (bor = bor')
  | Deref e T mut, Deref e' T' mut' =>
      bool_decide (T = T') && bool_decide (mut = mut') && expr_beq e e'
  | NewCall, NewCall => true
  | Retag e T kind, Retag e' T' kind' =>
      bool_decide (T = T') && bool_decide (kind = kind') && expr_beq e e'
  | Read e, Read e' | Ref e, Ref e' | EndCall e, EndCall e' => expr_beq e e'
  | Write e1 e2, Write e1' e2'| Field e1 e2, Field e1' e2' =>
      expr_beq e1 e1' && expr_beq e2 e2'
  | CAS e0 e1 e2, CAS e0' e1' e2' =>
      expr_beq e0 e0' && expr_beq e1 e1' && expr_beq e2 e2'
  | Fork e, Fork e' => expr_beq e e'
  | Alloc T am, Alloc T' am' => bool_decide (T = T') && bool_decide (am = am')
  | Free e T, Free e' T' => bool_decide (T = T') && expr_beq e e'
  | _, _ => false
  end.

Lemma expr_beq_correct (e1 e2 : expr) : expr_beq e1 e2 ↔ e1 = e2.
Proof.
  revert e1 e2; fix FIX 1;
    destruct e1 as [| |? el1| | | | | | | | | | | | | | |? el1|],
             e2 as [| |? el2| | | | | | | | | | | | | | |? el2|];
    simpl; try done;
    rewrite ?andb_True ?bool_decide_spec ?FIX;
    try (split; intro; [destruct_and?|split_and?]; congruence).
  - match goal with |- context [?F el1 el2] => assert (F el1 el2 ↔ el1 = el2) end.
    { revert el2. induction el1 as [|el1h el1q]; destruct el2; try done.
      specialize (FIX el1h). naive_solver. }
    clear FIX. naive_solver.
  - match goal with |- context [?F el1 el2] => assert (F el1 el2 ↔ el1 = el2) end.
    { revert el2. induction el1 as [|el1h el1q]; destruct el2; try done.
      specialize (FIX el1h). naive_solver. }
    clear FIX. naive_solver.
Qed.

Instance expr_dec_eq : EqDecision expr.
Proof.
  refine (λ e1 e2, cast_if (decide (expr_beq e1 e2))); by rewrite -expr_beq_correct.
Defined.
Instance expr_countable : Countable expr.
Proof.
  refine (inj_countable'
    (fix go e := match e with
      | Var x => GenNode 0 [GenLeaf $ inl $ inl $ inl $ inl x]
      | Lit l => GenNode 1 [GenLeaf $ inl $ inl $ inl $ inr l]
      | Rec f xl e => GenNode 2 [GenLeaf $ inl $ inl $ inr $ inl f;
                                 GenLeaf $ inl $ inl $ inr $ inr xl; go e]
      | Place l tag => GenNode 3 [GenLeaf $ inl $ inr $ inl $ inl l;
                                  GenLeaf $ inl $ inr $ inl $ inr tag]
      | BinOp op e1 e2 => GenNode 4 [GenLeaf $ inl $ inr $ inr $ inl op;
                                     go e1; go e2]
      | App e el => GenNode 5 (go e :: (go <$> el))
      | Read e => GenNode 6 [go e]
      | Write e1 e2 => GenNode 7 [go e1; go e2]
      | CAS e0 e1 e2 => GenNode 8 [go e0; go e1; go e2]
      | Free e T => GenNode 9 [GenLeaf $ inl $ inr $ inr $ inr T; go e]
      | Alloc T amod => GenNode 10 [GenLeaf $ inr $ inl $ inl $ inl T;
                                    GenLeaf $ inr $ inl $ inl $ inr amod]
      | Deref e T mut => GenNode 11 [GenLeaf $ inr $ inl $ inr $ inl T;
                                     GenLeaf $ inr $ inl $ inr $ inr mut;
                                     go e]
      | Ref e => GenNode 12 [go e]
      | Field e1 e2 => GenNode 13 [go e1; go e2]
      | NewCall => GenNode 14 []
      | EndCall e => GenNode 15 [go e]
      | Retag e T kind => GenNode 16 [GenLeaf $ inr $ inr $ inl T;
                                      GenLeaf $ inr $ inr $ inr kind;
                                      go e]
      | Case e el => GenNode 17 (go e :: (go <$> el))
      | Fork e => GenNode 18 [go e]
     end)
    (fix go s := match s with
     | GenNode 0 [GenLeaf (inl (inl (inl (inl x))))] => Var x
     | GenNode 1 [GenLeaf (inl (inl (inl (inr l))))] => Lit l
     | GenNode 2 [GenLeaf (inl (inl (inr (inl f))));
                  GenLeaf (inl (inl (inr (inr xl)))); e] => Rec f xl (go e)
     | GenNode 3 [GenLeaf (inl (inr (inl (inl l))));
                  GenLeaf (inl (inr (inl (inr tag))))] => Place l tag
     | GenNode 4 [GenLeaf (inl (inr (inr (inl op)))); e1; e2] => BinOp op (go e1) (go e2)
     | GenNode 5 (e :: el) => App (go e) (go <$> el)
     | GenNode 6 [e] => Read (go e)
     | GenNode 7 [e1; e2] => Write (go e1) (go e2)
     | GenNode 8 [e0; e1; e2] => CAS (go e0) (go e1) (go e2)
     | GenNode 9 [GenLeaf (inl (inr (inr (inr T)))); e] => Free (go e) T
     | GenNode 10 [GenLeaf (inr (inl (inl (inl T))));
                   GenLeaf (inr (inl (inl (inr amod))))] => Alloc T amod
     | GenNode 11 [GenLeaf (inr (inl (inr (inl T))));
                   GenLeaf (inr (inl (inr (inr mut)))); e] => Deref (go e) T mut
     | GenNode 12 [e] => Ref (go e)
     | GenNode 13 [e1; e2] => Field (go e1) (go e2)
     | GenNode 14 [] => NewCall
     | GenNode 15 [e] => EndCall (go e)
     | GenNode 16 [GenLeaf (inr (inr (inl T)));
                   GenLeaf (inr (inr (inr kind))); e] => Retag (go e) T kind
     | GenNode 17 (e :: el) => Case (go e) (go <$> el)
     | GenNode 18 [e] => Fork (go e)
     | _ => Lit LitPoison
     end) _).
  fix FIX 1. intros []; f_equal=>//; revert el; clear -FIX.
  - fix FIX_INNER 1. intros []; [done|]. by simpl; f_equal.
  - fix FIX_INNER 1. intros []; [done|]. by simpl; f_equal.
Qed.

Instance val_dec_eq : EqDecision val.
Proof.
  refine (λ v1 v2, cast_if (decide (of_val v1 = of_val v2))); abstract naive_solver.
Defined.
Instance val_countable : Countable val.
Proof.
  refine (inj_countable
    (λ v, match v with
          | ImmV (LitV l) => inl $ inl l
          | ImmV (RecV f xl e) => inl $ inr (f, xl, e)
          | PlaceV l bor => inr (l, bor)
          end)
    (λ x, match x with
          | inl (inl l) => Some $ ImmV $ LitV l
          | inl (inr (f, xl, e)) =>
              match decide _ with left C => Some $ ImmV $ @RecV f xl e C | _ => None end
          | inr (l, bor) => Some $ PlaceV l bor
          end) _).
  intros [[]|] =>//; by rewrite decide_left.
Qed.

Instance type_inhabited : Inhabited type := populate (Scala 0).
Instance expr_inhabited : Inhabited expr := populate (Lit LitPoison).
Instance val_inhabited : Inhabited val := populate (ImmV $ LitV LitPoison).
Instance state_Inhabited : Inhabited state.
Proof. do 2!econstructor; exact: inhabitant. Qed.

Canonical Structure locC := leibnizC loc.
Canonical Structure valC := leibnizC val.
Canonical Structure exprC := leibnizC expr.
Canonical Structure stateC := leibnizC state.

(** Basic properties about the language *)

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2 :
  to_val e1 = None → to_val e2 = None →
  map of_val vl1 ++ e1 :: el1 = map of_val vl2 ++ e2 :: el2 →
  vl1 = vl2 ∧ el1 = el2.
Proof.
  revert vl2; induction vl1; destruct vl2; intros H1 H2; inversion 1.
  - done.
  - subst. by rewrite to_of_val in H1.
  - subst. by rewrite to_of_val in H2.
  - destruct (IHvl1 vl2); auto. split; f_equal; auto. by apply (inj of_val).
Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1 as [| | |v1 vl1 el1| | | | | | | | | | | | | |],
           Ki2 as [| | |v2 vl2 el2| | | | | | | | | | | | | |];
  intros He1 He2 EQ; try discriminate; simplify_eq/=;
    repeat match goal with
    | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
    end; auto.
  destruct (list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2); auto. congruence.
Qed.

Lemma val_head_stuck e1 σ1 κ e2 σ2 efs : head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; inversion BaseStep; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 efs :
  head_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
Proof.
  destruct Ki; inversion_clear 1; inversion_clear BaseStep;
    simplify_option_eq; eauto; [done|].
  eapply (Forall_forall (λ ei, is_Some (to_val ei))); eauto. set_solver.
Qed.

Lemma bor_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
Qed.
End bor_lang.

(** Language *)
Canonical Structure bor_ectxi_lang := EctxiLanguage bor_lang.bor_lang_mixin.
Canonical Structure bor_ectx_lang := EctxLanguageOfEctxi bor_ectxi_lang.
Canonical Structure bor_lang := LanguageOfEctx bor_ectx_lang.

Export bor_lang.

(** Some derived forms. *)
Notation Lam xl e := (Rec BAnon xl e).
Notation Let x e1 e2 := (App (Lam [x] e2) [e1]).
Notation Seq e1 e2 := (Let BAnon e1 e2).
Notation LamV xl e := (ImmV (RecV BAnon xl e)).
Notation LetCtx x e2 := (AppRCtx (LamV [x] e2) [] []).
Notation SeqCtx e2 := (LetCtx BAnon e2).
Notation Skip := (Seq (Lit LitPoison) (Lit LitPoison)).
Notation If e0 e1 e2 := (Case e0 [e2;e1]).

Coercion lit_of_bool : bool >-> lit.
Coercion LitInt : Z >-> lit.

(** Shifting for locations *)
Lemma shift_loc_assoc l n n' : l +ₗ n +ₗ n' = l +ₗ (n + n').
Proof. rewrite /shift_loc /=. f_equal. lia. Qed.
Lemma shift_loc_0 l : l +ₗ 0 = l.
Proof. destruct l as [b o]. rewrite /shift_loc /=. f_equal. lia. Qed.

Lemma shift_loc_assoc_nat l (n n' : nat) : l +ₗ n +ₗ n' = l +ₗ (n + n')%nat.
Proof. rewrite /shift_loc /=. f_equal. lia. Qed.
Lemma shift_loc_0_nat l : l +ₗ 0%nat = l.
Proof. destruct l as [b o]. rewrite /shift_loc /=. f_equal. lia. Qed.

Instance shift_loc_inj l : Inj (=) (=) (shift_loc l).
Proof. destruct l as [b o]; intros n n' [=?]; lia. Qed.

Lemma shift_loc_block l n : (l +ₗ n).1 = l.1.
Proof. done. Qed.
