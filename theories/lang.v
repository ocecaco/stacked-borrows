From Equations Require Import Equations.
From iris.program_logic Require Export language ectx_language ectxi_language.
From stdpp Require Export strings list gmap infinite.
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
Inductive pointer_kind := RefPtr (mut: mutability) | RawPtr | BoxPtr.

Inductive type :=
  | Scalar (sz: nat)
  | Reference (kind: pointer_kind) (T: type)
  | Unsafe (T: type)
  | Union (Ts: list type)
  | Product (Ts: list type)
  | Sum (Ts: list type)
  .
Bind Scope lrust_type with type.
Delimit Scope lrust_type with RustT.

(* Physical size of types *)
Fixpoint list_nat_max (ns: list nat) (d: nat) :=
  match ns with
  | [] => d
  | n :: ns => n `max` ((list_nat_max ns) d)
  end.

Lemma list_nat_max_spec ns :
  ns = [] ∧ list_nat_max ns O = O ∨
  list_nat_max ns O ∈ ns ∧ ∀ (i: nat), i ∈ ns → (i ≤ list_nat_max ns O)%nat.
Proof.
  induction ns as [|i ns IHi]; simpl; [rewrite elem_of_nil; naive_solver|].
  right. destruct IHi as [[]|[In MAX]].
  - subst. rewrite /= Nat.max_0_r elem_of_list_singleton.
    setoid_rewrite elem_of_list_singleton. naive_solver.
  - split.
    + apply Max.max_case; [by left|by right].
    + move => i' /elem_of_cons [->|In']. apply Nat.le_max_l.
      etrans; first by apply MAX. apply Nat.le_max_r.
Qed.

Fixpoint tsize (T: type) : nat :=
  match T with
  | Scalar sz => sz
  | Reference _ _ => 1%nat     (* We do not go beyond pointers *)
  | Unsafe T => tsize T
  | Union Ts => list_nat_max (tsize <$> Ts) O
  | Product Ts => foldl (λ sz T, sz + tsize T)%nat O Ts
  | Sum Ts => 1 + list_nat_max (tsize <$> Ts) O
  end.

(* Type doesn't contain UnsafeCells. *)
Fixpoint is_freeze (T: type) : bool :=
  match T with
  | Scalar _ | Reference _ _ => true
  | Unsafe _ => false
  | Union Ts | Product Ts | Sum Ts => forallb is_freeze Ts
  end.

(** Instrumented states *)
(* Borrow types *)
Inductive borrow :=
  | UniqB (t: time)           (* A unique (mutable) reference. *)
  | AliasB (ot : option time) (* An aliasing reference, also for raw pointers
                                 whose ot is None. *)
  .

Definition is_unique (bor: borrow) :=
  match bor with UniqB _ => true | _ => false end.
Definition is_aliasing (bor: borrow) :=
  match bor with AliasB _ => true | _ => false end.
Notation borrow_default := (AliasB None).

(* Retag kinds *)
Inductive retag_kind := FnEntry (c: call_id) | TwoPhase | RawRt | Default.

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
Inductive lit := LitPoison | LitLoc (l: loc) (tag: borrow) | LitInt (n : Z).

(** Binders for lambdas: list of formal arguments to functions *)
Inductive binder := BAnon | BNamed : string → binder.
Bind Scope lrust_binder_scope with binder.
Delimit Scope lrust_binder_scope with RustB.

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
| Lit (l: lit)
(* base lambda calculus *)
| Var (x : string)
| App (e : expr) (el: list expr)
| Rec (f : binder) (xl : list binder) (e : expr)
(* temp values *)
| TVal (el: list expr)
| Proj (e1 e2 : expr)
| Conc (e1 e2: expr)
(* bin op *)
| BinOp (op : bin_op) (e1 e2 : expr)
(* place operation *)
| Place (l: loc) (tag: borrow) (T: type)
                                  (* A place is a tagged pointer: every access
                                     to memory revolves around a place. *)
| Deref (e: expr) (T: type) (mut: option mutability)
                                  (* Deference a pointer `e` into a place
                                     presenting the location that `e` points to.
                                     The location has type `T` and the pointer
                                     has mutable kind `mut`. *)
| Ref (e: expr)                   (* Turn a place `e` into a pointer value. *)
| Field (e: expr) (path: list nat)(* Create a place that points to a component
                                     of the place `e`. `path` defines the path
                                     through the type. *)
(* mem op *)
| Copy (e : expr)                 (* Read from the place `e` *)
| Write (e1 e2: expr)             (* Write the value `e2` to the place `e1` *)
| Alloc (T: type)                 (* Allocate a place of type `T` *)
| Free (e : expr)                 (* Free the place `e` *)
(* atomic mem op *)
| CAS (e0 e1 e2 : expr)           (* CAS the value `e2` for `e1` to the place `e0` *)
| AtomWrite (e1 e2: expr)
| AtomRead (e: expr)
(* function call tracking *)
| NewCall                         (* Issue a fresh id for the call *)
| EndCall (e: expr)               (* End the call with id `e` *)
(* retag *)
| Retag (e : expr) (kind: retag_kind) (call_id: expr)
                                  (* Retag the place `e` with retag kind `kind`. *)
(* case *)
| Case (e : expr) (el: list expr)
(* concurrency *)
| Fork (e : expr)
(* observable behavior *)
| SysCall (id: nat)
.

Bind Scope expr_scope with expr.
Delimit Scope expr_scope with E.

Arguments App _%E _%E.
Arguments BinOp _ _%E _%E.
Arguments TVal _%E.
Arguments Proj _%E _%E.
Arguments Conc _%E _%E.
Arguments Deref _%E _%RustT _.
Arguments Ref _%E.
Arguments Field _%E _.
Arguments Copy _%E.
Arguments Write _%E _%E.
Arguments Alloc _%RustT.
Arguments Free _%E.
Arguments CAS _%E _%E _%E.
Arguments AtomWrite _%E _%E.
Arguments AtomRead _%E.
Arguments Retag _%E _ _%E.
Arguments Case _%E _%E.
Arguments Fork _%E.

(** Closedness *)
Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Lit _ | Place _ _ _ | Alloc _ | NewCall | SysCall _ => true
  | Var x => bool_decide (x ∈ X)
  | Rec f xl e => is_closed (f :b: xl +b+ X) e
  | BinOp _ e1 e2 | AtomWrite e1 e2 | Write e1 e2 | Retag e1 _ e2
    | Conc e1 e2 | Proj e1 e2 => is_closed X e1 && is_closed X e2
  | TVal el => forallb (is_closed X) el
  | App e el | Case e el => is_closed X e && forallb (is_closed X) el
  | AtomRead e | Copy e | Deref e _ _ | Ref e | Field e _
    | Free e | EndCall e | Fork e => is_closed X e
  | CAS e0 e1 e2 => is_closed X e0 && is_closed X e1 && is_closed X e2
  end.

Class Closed (X : list string) (e : expr) := closed : is_closed X e.
Instance closed_proof_irrel env e : ProofIrrel (Closed env e).
Proof. rewrite /Closed. apply _. Qed.
Instance closed_decision env e : Decision (Closed env e).
Proof. rewrite /Closed. apply _. Qed.

(** Heap values *)
Inductive immediate :=
| LitV (l : lit)
| RecV (f : binder) (xl : list binder) (e : expr) `{Closed (f :b: xl +b+ []) e}.

(** Irreducible (language values) *)
Inductive val :=
| ImmV (v : immediate)
| TValV (vl : list immediate)
| PlaceV (l: loc) (tag: borrow) (T: type)
.
Bind Scope val_scope with val.
Delimit Scope val_scope with V.

Definition of_immediate (v: immediate) : expr :=
  match v with
  | LitV l => Lit l
  | RecV f xl e => Rec f xl e
  end.
Definition to_immediate (e: expr): option immediate :=
  match e with
  | Rec f xl e =>
    if decide (Closed (f :b: xl +b+ []) e) then Some (RecV f xl e) else None
  | Lit l => Some (LitV l)
  | _ => None
  end.
Definition to_immediates (vl : list immediate) (el: list expr)
  : option (list immediate) :=
  foldl (λ acc e, vl ← acc; v ← to_immediate e; Some (vl ++ [v])) (Some vl) el.

Definition of_val (v : val) : expr :=
  match v with
  | ImmV v => of_immediate v
  | TValV vl => TVal (of_immediate <$> vl)
  | PlaceV l tag T => Place l tag T
  end.
Definition to_val (e : expr) : option val :=
  match e with
  | Rec _ _ _ | Lit _ => ImmV <$> (to_immediate e)
  | Place l T tag => Some (PlaceV l T tag)
  | TVal el => vl ← to_immediates [] el; Some (TValV vl)
  | _ => None
  end.

(** Substitution *)
Fixpoint subst (x : string) (es : expr) (e : expr) : expr :=
  match e with
  | Var y => if bool_decide (y = x) then es else Var y
  | Lit l => Lit l
  | Rec f xl e =>
    Rec f xl $ if bool_decide (BNamed x ≠ f ∧ BNamed x ∉ xl) then subst x es e else e
  | Place l tag T => Place l tag T
  | App e1 el => App (subst x es e1) (map (subst x es) el)
  | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
  | TVal el => TVal (map (subst x es) el)
  | Proj e1 e2 => Proj (subst x es e1) (subst x es e2)
  | Conc e1 e2 => Conc (subst x es e1) (subst x es e2)
  | Copy e => Copy (subst x es e)
  | Write e1 e2 => Write (subst x es e1) (subst x es e2)
  | Alloc T => Alloc T
  | Free e => Free (subst x es e)
  | CAS e0 e1 e2 => CAS (subst x es e0) (subst x es e1) (subst x es e2)
  | AtomWrite e1 e2 => AtomWrite (subst x es e1) (subst x es e2)
  | AtomRead e => AtomRead (subst x es e)
  | Deref e T mut => Deref (subst x es e) T mut
  | Ref e => Ref (subst x es e)
  | Field e path => Field (subst x es e) path
  | NewCall => NewCall
  | EndCall e => EndCall (subst x es e)
  | Retag e kind call => Retag (subst x es e) kind (subst x es call)
  | Case e el => Case (subst x es e) (map (subst x es) el)
  | Fork e => Fork (subst x es e)
  | SysCall id => SysCall id
  end.

(* formal argument list substitution *)
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
| AppLCtx (el : list expr)
| AppRCtx (v : val) (vl : list val) (el : list expr)
| BinOpLCtx (op : bin_op) (e2 : expr)
| BinOpRCtx (op : bin_op) (v1 : val)
| TValCtx (vl : list val) (el : list expr)
| ProjLCtx (e : expr)
| ProjRCtx (v : val)
| ConcLCtx (e : expr)
| ConcRCtx (v : val)
| CopyCtx
| WriteLCtx (e : expr)
| WriteRCtx (v : val)
| FreeCtx
| CasLCtx (e1 e2: expr)
| CasMCtx (v0 : val) (e2 : expr)
| CasRCtx (v0 : val) (v1 : val)
| AtRdCtx
| AtWrLCtx (e : expr)
| AtWrRCtx (v : val)
| DerefCtx (T: type) (mut: option mutability)
| RefCtx
| FieldCtx (path : list nat)
| EndCallCtx
| RetagLCtx (kind: retag_kind) (call: expr)
| RetagRCtx (v: val) (kind: retag_kind)
| CaseCtx (el : list expr).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx el => App e el
  | AppRCtx v vl el => App (of_val v) ((of_val <$> vl) ++ e :: el)
  | BinOpLCtx op e2 => BinOp op e e2
  | BinOpRCtx op v1 => BinOp op (of_val v1) e
  | TValCtx vl el => TVal ((of_val <$> vl) ++ e :: el)
  | ProjLCtx e2 => Proj e e2
  | ProjRCtx v1 => Proj (of_val v1) e
  | ConcLCtx e2 => Conc e e2
  | ConcRCtx v1 => Conc (of_val v1) e
  | CopyCtx => Copy e
  | WriteLCtx e2 => Write e e2
  | WriteRCtx v1 => Write (of_val v1) e
  | FreeCtx => Free e
  | CasLCtx e1 e2 => CAS e e1 e2
  | CasMCtx v0 e2 => CAS (of_val v0) e e2
  | CasRCtx v0 v1 => CAS (of_val v0) (of_val v1) e
  | AtRdCtx => AtomRead e
  | AtWrLCtx e2 => AtomWrite e e2
  | AtWrRCtx v1 => AtomWrite (of_val v1) e
  | DerefCtx T mut => Deref e T mut
  | RefCtx => Ref e
  | FieldCtx path => Field e path
  | EndCallCtx => EndCall e
  | RetagLCtx kind call => Retag e kind call
  | RetagRCtx v kind => Retag (of_val v) kind e
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
| AllocEvt (l : loc) (lbor: borrow) (T: type)
| DeallocEvt (l: loc) (lbor: borrow) (T: type)
| CopyEvt (l: loc) (lbor: borrow) (T: type) (vl: list immediate)
| WriteEvt (l: loc) (lbor: borrow) (T: type) (vl: list immediate)
| DerefEvt (l: loc) (lbor: borrow) (T: type) (mut: option mutability)
| NewCallEvt (call: call_id)
| EndCallEvt (call: call_id)
| RetagEvt (x: loc) (T: type) (kind: retag_kind)
| SysCallEvt (id: nat)
| SilentEvt
.

(* Compute subtype of `T` and offset to it from `path` *)
Fixpoint field_access (T: type) (path : list nat) :
  option (nat * type) :=
  match path with
  | [] => Some (O, T)
  | i :: path =>
    match T with
    | Scalar sz => if decide (i ≤ sz) then Some (i, Scalar (sz - i)) else None
    | Reference _ _ => match i with O => Some (O, T) | _ => None end
    | Unsafe T => field_access T path
    | Union Ts => T ← Ts !! i ; field_access T path
    | Product Ts =>
        T ← Ts !! i ; offT ← field_access T path;
        let sz : nat := foldl (λ sz T', sz + tsize T')%nat O (take i Ts) in
        Some (offT.1 + sz, offT.2)%nat
    | Sum Ts =>
        T ← Ts !! i ; offT ← field_access T path; Some (offT.1 + 1, offT.2)%nat
    end
  end.

Fixpoint write_mem l (vl: list immediate) h: mem :=
  match vl with
  | [] => h
  | v :: vl => write_mem (l +ₗ 1) vl (<[l := v]> h)
  end.

Equations read_mem (l: loc) (n: nat) (h: mem) : option (list immediate) :=
  read_mem l n h := go l n (Some [])
  where go : loc → nat → option (list immediate) → option (list immediate) :=
        go l O      oacc := oacc;
        go l (S n)  oacc :=
          acc ← oacc ;
          v ← h !! l;
          go (l +ₗ 1) n (Some (acc ++ [v])).

Inductive base_step :
  expr → mem → event → expr → mem → list expr → Prop :=
| BinOpBS op l1 l2 l' h :
    bin_op_eval h op l1 l2 l' →
    base_step (BinOp op (TVal [Lit l1]) (TVal [Lit l2])) h
              SilentEvt (TVal [Lit l']) h []
| BetaBS f xl e e' el h :
    Forall (λ ei, is_Some (to_val ei)) el →
    Closed (f :b: xl +b+ []) e →
    subst_l (f::xl) (Rec f xl e :: el) e = Some e' →
    base_step (App (Rec f xl e) el) h SilentEvt e' h []
(* TODO: add more operations for tempvalue lists *)
| ProjBS h el i vl v
    (DEFINED: 0 ≤ i ∧ vl !! (Z.to_nat i) = Some v)
    (VALUES: to_val (TVal el) = Some (TValV vl)) :
    base_step (Proj (TVal el) (Lit $ LitInt i)) h SilentEvt (of_val (ImmV v)) h []
| ConcBS h el1 el2 vl1 vl2
    (VALUES1: to_val (TVal el1) = Some (TValV vl1))
    (VALUES2: to_val (TVal el2) = Some (TValV vl2)):
    base_step (Conc (TVal el1) (TVal el2)) h
              SilentEvt (of_val (TValV (vl1 ++ vl2))) h []
| CopyBS l lbor T (vl: list immediate) h
    (READ: read_mem l (tsize T) h = Some vl)
    (* (LEN: length vl = tsize T)
    (VALUES: ∀ (i: nat), (i < length vl)%nat → h !! (l +ₗ i) = vl !! i) *) :
    base_step (Copy (Place l lbor T)) h
              (CopyEvt l lbor T vl)
              (of_val (TValV vl)) h
              []
| WriteBS l lbor T el vl h (LENe: length el = tsize T)
    (DEFINED: ∀ (i: nat), (i < length vl)%nat → is_Some (h !! (l +ₗ i)))
    (VALUES: to_val (TVal el) = Some (TValV vl)) :
    base_step (Write (Place l lbor T) (TVal el)) h
              (WriteEvt l lbor T vl)
              (Lit LitPoison) (write_mem l vl h)
              []
| AllocBS l lbor T h :
    (∀ m, h !! (l +ₗ m) = None) →
    base_step (Alloc T) h
              (AllocEvt l lbor T)
              (Place l lbor T) (init_mem l (tsize T) h)
              []
| DeallocBS T l lbor h :
    (∀ m, is_Some (h !! (l +ₗ m)) ↔ 0 ≤ m < tsize T) →
    base_step (Free (Place l lbor T)) h
              (DeallocEvt l lbor T)
              (Lit LitPoison) (free_mem l (tsize T) h)
              []
| NewCallBS call h:
    base_step NewCall h (NewCallEvt call) (Lit $ LitInt call) h []
| EndCallBS (call: Z) h:
    (0 ≤ Z.to_nat call)%nat →
    base_step (EndCall (Lit $ LitInt call)) h
              (EndCallEvt (Z.to_nat call)) (Lit LitPoison) h []
| RefBS l lbor T h :
    is_Some (h !! l) →
    base_step (Ref (Place l lbor T)) h SilentEvt (Lit (LitLoc l lbor)) h []
| DerefBS l lbor T mut h :
    is_Some (h !! l) →
    base_step (Deref (Lit (LitLoc l lbor)) T mut) h
              (DerefEvt l lbor T mut)
              (Place l lbor T) h
              []
| FieldBS l lbor T path off T' h
    (FIELD: field_access T path = Some (off, T')) :
    base_step (Field (Place l lbor T) path) h
              SilentEvt (Place (l +ₗ off) lbor T') h []
| RetagBS x xbor T kind kind' h e v
    (VAL: to_val e = Some v)
    (KIND: match kind with
           | FnEntry _ => ∃ call, v = ImmV $ LitV $ LitInt call ∧
                          0 ≤ call ∧ kind' = FnEntry (Z.to_nat call)
           | _ => kind' = kind
           end) :
    base_step (Retag (Place x xbor T) kind e) h
              (RetagEvt x T kind' ) (Lit LitPoison) h []
| CaseBS i el e h :
    0 ≤ i →
    el !! (Z.to_nat i) = Some e →
    base_step (Case (Lit $ LitInt i) el) h SilentEvt e h []
| ForkBS e h:
    base_step (Fork e) h SilentEvt (Lit LitPoison) h [e]
(* observable behavior *)
| SysCallBS id h:
    base_step (SysCall id) h (SysCallEvt id) (Lit LitPoison) h [].

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
  | _,_ =>
    stack' ← access1' stack.(borrows) bor kind β ; Some (mkBorStack stack' None)
  end.

(* Perform the access check on a block of continuous memory.
 * This implements Stacks::access. *)
Fixpoint accessN α β l (bor: borrow) (n: nat) kind : option bstacks :=
  match n with
  | O => Some α
  | S n =>
      let l' := (l +ₗ n) in
      stack ← α !! l'; stack' ← (access1 β stack bor kind) ;
        match kind with
        | AccessDealloc => accessN (delete l' α) β l bor n kind
        | _ => accessN (<[l':=stack']> α) β l bor n kind
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
  | S n => stack ← α !! (l +ₗ n) ; deref1 stack bor kind ;; derefN α l bor n kind
  end.

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
  visit_freeze_sensitive' h l f a last cur_dist (Scalar n)
    := (* consider frozen, simply extend the distant to the last unsafe *)
       Some (a, (last, cur_dist + n)%nat) ;
  visit_freeze_sensitive' h l f a last cur_dist (Reference _ _)
    := (* consider frozen, extend the distant by 1 *)
       Some (a, (last, S cur_dist)) ;
  visit_freeze_sensitive' h l f a last cur_dist (Unsafe T)
    := (* reach an UnsafeCell, apply the action `f` and return new `last` and
          `cur_dist` *)
       unsafe_action f a l last cur_dist (tsize T) ;
  visit_freeze_sensitive' h l f a last cur_dist (Union Ts)
    := (* If it's a union, look at the type to see if there is UnsafeCell *)
       if is_freeze (Union Ts)
       (* No UnsafeCell, consider the whole block frozen and simply extend the
          distant. *)
       then Some (a, (last, cur_dist + (tsize (Union Ts)))%nat)
       (* There can be UnsafeCell, consider the whole block unfrozen and perform
          `f a _ _ false` on the whole block. `unsafe_action` will return the
          offsets for the following visit. *)
       else unsafe_action f a l last cur_dist (tsize (Union Ts)) ;
  visit_freeze_sensitive' h l f a last cur_dist (Product Ts)
    := (* This implements left-to-right search on the type, which guarantees
          that the offsets are increasing. *)
       visit_LR a last cur_dist Ts
    where visit_LR (a: A) (last cur_dist: nat) (Ts: list type)
      : option (A * (nat * nat)) :=
      { visit_LR a last cur_dist [] := Some (a, (last, cur_dist)) ;
        visit_LR a last cur_dist (T :: Ts) :=
          alc ← visit_freeze_sensitive' h l f a last cur_dist T ;
          visit_LR alc.1 alc.2.1 alc.2.2 Ts } ;
  visit_freeze_sensitive' h l f a last cur_dist (Sum Ts) with h !! l
    := {
    (* This looks up the current state to see which discriminant currently is
       active (which is an integer) and redirect the visit for the type of that
       discriminant. Note that this consitutes a read-access, and should adhere
       to the access checks. But we are skipping them here. FIXME *)
    | Some (LitV (LitInt i)) :=
        if decide (O ≤ i < length Ts)
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
        where visit_lookup (Ts: list type) (i: nat) : option (A * (nat * nat)) :=
        { visit_lookup [] i             := None ;
          visit_lookup (T :: Ts) O      :=
            visit_freeze_sensitive' h l f a last (S cur_dist) T ;
          visit_lookup (T :: Ts) (S i)  := visit_lookup Ts i } ;
    | _ := None }
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

(* Perform the deref check on a block of continuous memory where some of them
 * can be inside UnsafeCells, which are described by the type `t` of the block.
 * This implements EvalContextExt::ptr_dereference. *)
(* TODO?: bound check of l for size (tsize t)? alloc.check_bounds(this, ptr, size)?; *)
Definition ptr_deref h α (l: loc) (bor: borrow) T (mut: option mutability) : Prop :=
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
        visit_freeze_sensitive h l T
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
      if decide (c' = c) then stack
      else mkBorStack (FnBarrier c :: stack') stack.(frozen_since)
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
  ptr_idx ← (deref1 stack bor kind');
  match bar, ptr_idx, deref1 stack bor' kind' with
  | None, _, Some None =>
      (* bor' must be aliasing *)
      if is_aliasing bor' then Some stack else None
  | None, Some ptr_idx, Some (Some new_idx) =>
      if decide (ptr_idx ≤ new_idx)%nat
      then (* bor' must be aliasing *)
           if is_aliasing bor' then Some stack else None
      else (* check for access with bor, then reborrow with bor' *)
           stack1 ← access1 β stack bor (to_access_kind kind') ;
           create_borrow stack1 bor' kind'
  | None, _ ,_ =>
      (* check for access with bor, then reborrow with bor' *)
      stack1 ← access1 β stack bor (to_access_kind kind') ;
      create_borrow stack1 bor' kind'
  | Some c, _, _ =>
      (* check for access with bor, then add barrier & reborrow with bor' *)
      stack1 ← access1 β stack bor (to_access_kind kind') ;
      create_borrow (add_barrier stack1 c) bor' kind'
  end.
Fixpoint reborrowN α β l n bor bor' kind' bar : option bstacks :=
  match n with
  | O => Some α
  | S n =>
      let l' := (l +ₗ n) in
      stack  ← (α !! l') ;
      stack' ← reborrow1 stack bor bor' kind' β bar ;
      reborrowN (<[l' := stack']> α) β l n bor bor' kind' bar
  end.

(* This implements Stacks::reborrow *)
Definition reborrowBlock α β l n bor bor' kind' bar : option bstacks :=
  if xorb (is_unique bor') (is_unique_ref kind') then None
  else let bar' := match kind' with RawRef => None | _ => bar end in
       reborrowN α β l n bor bor' kind' bar.

(* This implements EvalContextPrivExt::reborrow *)
(* TODO?: alloc.check_bounds(this, ptr, size)?; *)
Definition reborrow h α β l bor T (bar: option call_id) bor' :=
  match bor' with
  | AliasB (Some _) =>
      (* We need freeze-sensitive reborrow, depending on whether some memory is
         in UnsafeCell or not *)
      visit_freeze_sensitive h l T
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
Definition retag_ref h α β (clock: time) l bor (T: type) (mut: option mutability)
  (bar: option call_id) (two_phase: bool) : option (borrow * bstacks * time) :=
  match tsize T with
  | O => (* Nothing to do for zero-sized types *)
      Some (bor, α, clock)
  | _ =>
      let bor' := match mut with
                     | None => borrow_default | Some Mutable => UniqB clock
                     | Some Immutable => AliasB (Some clock)
                     end in
      (* reborrow bor with bor' *)
      α' ← reborrow h α β l bor T bar bor';
      if two_phase
      then match mut with
            | Some Mutable => (* two-phase only for mut borrow *)
                let bor'' := AliasB (Some (S clock)) in
                 (* second reborrow, no barrier *)
                α'' ← reborrow h α' β l bor T None bor'' ;
                Some (bor'', α'', S (S clock))
            | _ => None
          end
      else Some (bor', α', S clock)
  end.

Definition is_two_phase (kind: retag_kind) : bool :=
  match kind with TwoPhase => true | _ => false end.
Definition adding_barrier (kind: retag_kind) : option call_id :=
  match kind with FnEntry c => Some c | _ => None end.
(* This implements EvalContextExt::retag *)
Equations retag h α (clock: time) β (x: loc) (kind: retag_kind) T :
  option (mem * bstacks * time) :=
  retag h α clock β x kind (Scalar _)         := Some (h, α, clock) ;
  retag h α clock β x kind (Union _)          := Some (h, α, clock) ;
  retag h α clock β x kind (Unsafe T)         := retag h α clock β x kind T ;
  retag h α clock β x kind (Reference pk Tr) with h !! x :=
  { | Some (LitV (LitLoc l bor)) :=
        match pk, kind with
        (* Reference pointer *)
        | RefPtr mut, _ =>
            bac ← retag_ref h α β clock l bor Tr (Some mut)
                            (adding_barrier kind) (is_two_phase kind) ;
            Some (<[x := LitV (LitLoc l bac.1.1)]>h, bac.1.2, bac.2)
        (* Box pointer *)
        | BoxPtr, _ =>
            bac ← retag_ref h α β clock l bor Tr (Some Mutable)
                            None (is_two_phase kind) ;
            Some (<[x := LitV (LitLoc l bac.1.1)]>h, bac.1.2, bac.2)
        (* If is Raw retagging, also retag raw ptr, no barrier *)
        | RawPtr, RawRt =>
            bac ← retag_ref h α β clock l bor Tr None None false ;
            Some (<[x := LitV (LitLoc l bac.1.1)]>h, bac.1.2, bac.2)
        (* Ignore Raw pointer otherwise *)
        | RawPtr, _ => Some (h, α, clock)
        end ;
    | _ := None } ;
  retag h α clock β x kind (Product Ts)       := visit_LR h α clock x Ts
    (* left-to-right visit to retag *)
    where visit_LR h α (clock: time) (x: loc) (Ts: list type)
      : option (mem * bstacks * time) :=
      { visit_LR h α clock x []         := Some (h, α, clock) ;
        visit_LR h α clock x (T :: Ts)  :=
          hac ← retag h α clock β x kind T ;
          visit_LR hac.1.1 hac.1.2 hac.2 (x +ₗ (tsize T)) Ts } ;
  retag h α clock β x kind (Sum Ts) with h !! x :=
  { | Some (LitV (LitInt i)) :=
        if decide (O ≤ i < length Ts)
        then (* the discriminant is well-defined, visit with the
                corresponding type *)
          visit_lookup Ts (Z.to_nat i)
        else None
        where visit_lookup (Ts: list type) (i: nat) : option (mem * bstacks * time) :=
        { visit_lookup [] i             := None ;
          visit_lookup (T :: Ts) O      := retag h α clock β (x +ₗ 1) kind T ;
          visit_lookup (T :: Ts) (S i)  := visit_lookup Ts i } ;
    | _ := None }
  .

Definition bor_value_included (bor: borrow) (clock: time) : Prop :=
  match bor with
  | UniqB t | AliasB (Some t) => (t < clock)%nat
  | _ => True
  end.
Infix "<b" := bor_value_included (at level 60, no associativity).
Definition bor_values_included (vl: list immediate) clock :=
  ∀ l bor, (LitV (LitLoc l bor)) ∈ vl → bor <b clock.
Infix "<<b" := bor_values_included (at level 60, no associativity).

(** Instrumented step for the stacked borrows *)
(* This ignores CAS for now. *)
Inductive instrumented_step h α β (clock: time):
  event → mem → bstacks → barriers → time → Prop :=
| SilentIS :
    instrumented_step h α β clock SilentEvt h α β clock
| SysCallIS id :
    instrumented_step h α β clock (SysCallEvt id) h α β clock
(* This implements EvalContextExt::tag_new_allocation. *)
| AllocIS t x T :
    (* UniqB t is the first borrow of the variable x,
       used when accessing x directly (not through another pointer) *)
    instrumented_step h α β clock
                      (AllocEvt x (UniqB t) T) h
                      (init_stacks x (tsize T) α (Uniq clock)) β (S clock)
(* This implements AllocationExtra::memory_read. *)
| CopyIS α' l lbor T vl
    (ACC: accessN α β l lbor (tsize T) AccessRead = Some α')
    (BOR: vl <<b clock) :
    instrumented_step h α β clock (CopyEvt l lbor T vl) h α' β clock
(* This implements AllocationExtra::memory_written. *)
| WriteIS α' l lbor T vl
    (ACC: accessN α β l lbor (tsize T) AccessWrite = Some α')
    (BOR: vl <<b clock) :
    instrumented_step h α β clock
                      (WriteEvt l lbor T vl) h α' β clock
(* This implements AllocationExtra::memory_deallocated. *)
| DeallocIS α' l lbor T
    (ACC: accessN α β l lbor (tsize T) AccessDealloc = Some α') :
    instrumented_step h α β clock
                      (DeallocEvt l lbor T) h α' β clock
| NewCallIS:
    let call : call_id := fresh (dom (gset call_id) β) in
    instrumented_step h α β clock
                      (NewCallEvt call) h α (<[call := true]>β) clock
| EndCallIS call
    (ACTIVE: β !! call = Some true) :
    instrumented_step h α β clock
                      (EndCallEvt call) h α (<[call := false]>β) clock
(* Deferencing a pointer value to a place *)
| DerefIS l lbor T mut
    (DEREF: ptr_deref h α l lbor T mut) :
    instrumented_step h α β clock
                      (DerefEvt l lbor T mut) h α β clock
| RetagIS h' α' clock' x T kind
    (FNBAR: match kind with FnEntry c => β !! c = Some true | _ => True end)
    (RETAG: retag h α clock β x kind T = Some (h', α', clock')) :
    instrumented_step h α β clock
                      (RetagEvt x T kind) h' α' β clock'.

(** COMBINED SEMANTICS -------------------------------------------------------*)
Record state := mkState {
  cheap: mem;
  cstk : bstacks;
  cbar : barriers;
  cclk : time;
}.

Implicit Type (σ: state).

Inductive head_step :
  expr → state → list event → expr → state → list expr → Prop :=
  | HeadStep σ e e' efs ev h0 h' α' β' clock'
      (BaseStep : base_step e σ.(cheap) ev e' h0 efs)
      (InstrStep: instrumented_step h0 σ.(cstk) σ.(cbar) σ.(cclk) ev h' α' β' clock')
  : head_step e σ [ev] e' (mkState h' α' β' clock') efs .

(** Closed expressions *)
Lemma is_closed_weaken X Y e : is_closed X e → X ⊆ Y → is_closed Y e.
Proof.
  revert e X Y. fix FIX 1; destruct e=>X Y/=; try naive_solver.
  - rewrite !andb_True. intros [He Hel] HXY. split. by eauto.
    induction el=>/=; naive_solver.
  - naive_solver set_solver.
  - intros Hel HXY. induction el=>/=; naive_solver.
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
  - move : He. induction el=>//=. rewrite andb_True=>?.
    f_equal; intuition eauto with set_solver.
  - case He=> _. clear He. induction el=>//=. rewrite andb_True=>?.
    f_equal; intuition eauto with set_solver.
Qed.

Lemma is_closed_nil_subst e x es : is_closed [] e → subst x es e = e.
Proof. intros. apply is_closed_subst with []; set_solver. Qed.

Lemma is_closed_of_val X v : is_closed X (of_val v).
Proof.
  apply is_closed_weaken_nil. destruct v as [[]|vl|]; auto.
  induction vl as [|v vl]; first auto. destruct v; simpl; auto.
Qed.

Lemma to_immediates_cons vl e el:
  to_immediates vl (e :: el) = v ← to_immediate e; to_immediates (vl ++ [v]) el.
Proof.
  rewrite /to_immediates /=. destruct (to_immediate e); simpl; [done|].
  by induction el.
Qed.
Lemma to_immediates_app vl el1 el2 :
  to_immediates vl (el1 ++ el2) = vl' ← to_immediates vl el1; to_immediates vl' el2.
Proof.
  revert vl. induction el1 as [|e el1 IH]; intros vl; [done|].
  rewrite /= 2!to_immediates_cons option_bind_assoc.
  apply option_bind_ext; [|done]. intros; by apply IH.
Qed.

Lemma to_of_immediate v: to_immediate (of_immediate v) = Some v.
Proof.
  destruct v; [done|]. simplify_option_eq; [|done].
  repeat f_equal. apply (proof_irrel _).
Qed.
Lemma of_to_immediate e v : to_immediate e = Some v → of_immediate v = e.
Proof. destruct e=>//=; [|case decide => ? //]; by intros [= <-]. Qed.
Lemma to_of_immediates vl1 vl2 :
  to_immediates vl1 (of_immediate <$> vl2) = Some (vl1 ++ vl2).
Proof.
  revert vl1. induction vl2 as [|v vl2 IH]; intros vl1; [by rewrite app_nil_r|].
  rewrite fmap_cons to_immediates_cons to_of_immediate /= IH. f_equal.
  by rewrite (cons_middle v vl1 vl2) app_assoc.
Qed.
Lemma of_to_immediates vl1 el2 vl:
  to_immediates vl1 el2 = Some vl →
  of_val (TValV vl) = (TVal ((of_immediate <$> vl1) ++ el2)).
Proof.
  revert vl1 vl. induction el2 as [|e el2 IH]; intros vl1 vl.
  - by rewrite /to_immediates /= app_nil_r => [[->]].
  - rewrite to_immediates_cons.
    destruct (to_immediate e) as [v|] eqn:Eqv; [|done].
    move => /(IH _ _) ->. f_equal.
    by rewrite fmap_app -(of_to_immediate _ _ Eqv) /= -app_assoc cons_middle.
Qed.
Instance of_immediate_inj : Inj (=) (=) of_immediate.
Proof. by intros ?? Hv; apply (inj Some); rewrite -2!to_of_immediate Hv /=. Qed.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  destruct v as [[]|vl|]; [done|..|done].
  - simplify_option_eq; [|done]. repeat f_equal. apply (proof_irrel _).
  - by rewrite /= to_of_immediates /=.
Qed.
Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  destruct e=>//=; [|case decide => ? //
                    |destruct (to_immediates [] el) as [vl|] eqn:Eq; [|done]
                    |]; intros [= <-]; auto.
  by rewrite (of_to_immediates _ _ _ Eq).
Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -2!to_of_val Hv /=. Qed.

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
  - induction el; naive_solver.
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

Fixpoint type_beq (T T': type) : bool :=
  let fix type_list_beq Ts Ts' :=
    match Ts, Ts' with
    | [], [] => true
    | T::Ts, T'::Ts' => type_beq T T' && type_list_beq Ts Ts'
    | _, _ => false
    end
  in
  match T, T' with
  | Scalar n, Scalar n' => bool_decide (n = n')
  | Reference k T, Reference k' T' => bool_decide (k = k') && type_beq T T'
  | Unsafe T, Unsafe T' => type_beq T T'
  | Union Ts, Union Ts' | Product Ts, Product Ts' | Sum Ts, Sum Ts' =>
      type_list_beq Ts Ts'
  | _, _ => false
  end.
Lemma type_beq_correct (T1 T2 : type) : type_beq T1 T2 ↔ T1 = T2.
Proof.
  revert T1 T2; fix FIX 1;
    destruct T1 as [| | |Ts1|Ts1|Ts1],
             T2 as [| | |Ts2|Ts2|Ts2];
    simpl; try done;
    rewrite ?andb_True ?bool_decide_spec ?FIX;
    try (split; intro; [destruct_and?|split_and?]; congruence).
  - match goal with |- context [?F Ts1 Ts2] => assert (F Ts1 Ts2 ↔ Ts1 = Ts2) end.
    { revert Ts2. induction Ts1 as [|Ts1h Ts1q]; destruct Ts2; try done.
      specialize (FIX Ts1h). naive_solver. }
    clear FIX. naive_solver.
  - match goal with |- context [?F Ts1 Ts2] => assert (F Ts1 Ts2 ↔ Ts1 = Ts2) end.
    { revert Ts2. induction Ts1 as [|Ts1h Ts1q]; destruct Ts2; try done.
      specialize (FIX Ts1h). naive_solver. }
    clear FIX. naive_solver.
  - match goal with |- context [?F Ts1 Ts2] => assert (F Ts1 Ts2 ↔ Ts1 = Ts2) end.
    { revert Ts2. induction Ts1 as [|Ts1h Ts1q]; destruct Ts2; try done.
      specialize (FIX Ts1h). naive_solver. }
    clear FIX. naive_solver.
Qed.
Instance type_eq_dec : EqDecision type.
Proof.
  refine (λ T1 T2, cast_if (decide (type_beq T1 T2))); by rewrite -type_beq_correct.
Defined.
Instance type_countable : Countable type.
Proof.
  refine (inj_countable'
    (fix go T := match T with
     | Scalar sz => GenNode 0 [GenLeaf $ inl sz]
     | Reference kind T => GenNode 1 [GenLeaf $ inr kind; go T]
     | Unsafe T => GenNode 2 [go T]
     | Union Ts => GenNode 3 (go <$> Ts)
     | Product Ts => GenNode 4 (go <$> Ts)
     | Sum Ts => GenNode 5 (go <$> Ts)
     end)
    (fix go s := match s with
     | GenNode 0 [GenLeaf (inl sz)] => Scalar sz
     | GenNode 1 [GenLeaf (inr kind); T] => Reference kind (go T)
     | GenNode 2 [T] => Unsafe (go T)
     | GenNode 3 Ts => Union (go <$> Ts)
     | GenNode 4 Ts => Product (go <$> Ts)
     | GenNode 5 Ts => Sum (go <$> Ts)
     | _ => Scalar 0
     end) _).
  fix FIX 1. intros []; f_equal=>//; revert Ts; clear -FIX.
  - fix FIX_INNER 1. intros []; [done|]. by simpl; f_equal.
  - fix FIX_INNER 1. intros []; [done|]. by simpl; f_equal.
  - fix FIX_INNER 1. intros []; [done|]. by simpl; f_equal.
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
  | TVal el, TVal el' => expr_list_beq el el'
  | Place l bor T , Place l' bor' T' =>
      bool_decide (l = l') && bool_decide (bor = bor') && bool_decide (T = T')
  | Deref e T mut, Deref e' T' mut' =>
      bool_decide (T = T') && bool_decide (mut = mut') && expr_beq e e'
  | NewCall, NewCall => true
  | Retag e kind call, Retag e' kind' call' =>
     bool_decide (kind = kind') && expr_beq e e' && expr_beq call call'
  | Copy e, Copy e' | Ref e, Ref e'
  | AtomRead e, AtomRead e' | EndCall e, EndCall e' => expr_beq e e'
  | Proj e1 e2, Proj e1' e2' | Conc e1 e2, Conc e1' e2'
    | Write e1 e2, Write e1' e2' | AtomWrite e1 e2, AtomWrite e1' e2' =>
      expr_beq e1 e1' && expr_beq e2 e2'
  | Field e path, Field e' path' => expr_beq e e' && bool_decide (path = path')
  | CAS e0 e1 e2, CAS e0' e1' e2' =>
      expr_beq e0 e0' && expr_beq e1 e1' && expr_beq e2 e2'
  | Fork e, Fork e' => expr_beq e e'
  | Alloc T, Alloc T' => bool_decide (T = T')
  | Free e, Free e' => expr_beq e e'
  | SysCall id, SysCall id' => bool_decide (id = id')
  | _, _ => false
  end.

Lemma expr_beq_correct (e1 e2 : expr) : expr_beq e1 e2 ↔ e1 = e2.
Proof.
  revert e1 e2; fix FIX 1;
    destruct e1 as [| |? el1| |el1| | | | | | | | | | | | | | | | | |? el1| |],
             e2 as [| |? el2| |el2| | | | | | | | | | | | | | | | | |? el2| |];
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
      | App e el => GenNode 3 (go e :: (go <$> el))
      | BinOp op e1 e2 => GenNode 4 [GenLeaf $ inl $ inr $ inr $ inr op;
                                     go e1; go e2]
      | TVal el => GenNode 5 (go <$> el)
      | Proj e1 e2 => GenNode 6 [go e1; go e2]
      | Conc e1 e2 => GenNode 7 [go e1; go e2]
      | Place l tag T => GenNode 8 [GenLeaf $ inl $ inr $ inl $ inl l;
                                    GenLeaf $ inl $ inr $ inl $ inr tag;
                                    GenLeaf $ inl $ inr $ inr $ inl T]
      | Copy e => GenNode 9 [go e]
      | Write e1 e2 => GenNode 10 [go e1; go e2]
      | Free e => GenNode 11 [go e]
      | Alloc T => GenNode 12 [GenLeaf $ inr $ inl $ inl $ inl T]
      | CAS e0 e1 e2 => GenNode 13 [go e0; go e1; go e2]
      | AtomWrite e1 e2 => GenNode 14 [go e1; go e2]
      | AtomRead e => GenNode 15 [go e]
      | Deref e T mut => GenNode 16 [GenLeaf $ inr $ inl $ inl $ inr T;
                                     GenLeaf $ inr $ inl $ inr mut;
                                     go e]
      | Ref e => GenNode 17 [go e]
      | Field e path => GenNode 18 [GenLeaf $ inr $ inr $ inl $ inl path; go e]
      | NewCall => GenNode 19 []
      | EndCall e => GenNode 20 [go e]
      | Retag e kind call => GenNode 21 [GenLeaf $ inr $ inr $ inl $ inr kind; go e; go call]
      | Case e el => GenNode 22 (go e :: (go <$> el))
      | Fork e => GenNode 23 [go e]
      | SysCall id => GenNode 24 [GenLeaf $ inr $ inr $ inr id]
     end)
    (fix go s := match s with
     | GenNode 0 [GenLeaf (inl (inl (inl (inl x))))] => Var x
     | GenNode 1 [GenLeaf (inl (inl (inl (inr l))))] => Lit l
     | GenNode 2 [GenLeaf (inl (inl (inr (inl f))));
                  GenLeaf (inl (inl (inr (inr xl)))); e] => Rec f xl (go e)
     | GenNode 3 (e :: el) => App (go e) (go <$> el)
     | GenNode 4 [GenLeaf (inl (inr (inr (inr op)))); e1; e2] => BinOp op (go e1) (go e2)
     | GenNode 5 el => TVal (go <$> el)
     | GenNode 6 [e1; e2] => Proj (go e1) (go e2)
     | GenNode 7 [e1; e2] => Conc (go e1) (go e2)
     | GenNode 8 [GenLeaf (inl (inr (inl (inl l))));
                  GenLeaf (inl (inr (inl (inr tag))));
                  GenLeaf (inl (inr (inr (inl T))))] => Place l tag T
     | GenNode 9 [e] => Copy (go e)
     | GenNode 10 [e1; e2] => Write (go e1) (go e2)
     | GenNode 11 [e] => Free (go e)
     | GenNode 12 [GenLeaf (inr (inl (inl (inl T))))] => Alloc T
     | GenNode 13 [e0; e1; e2] => CAS (go e0) (go e1) (go e2)
     | GenNode 14 [e1; e2] => AtomWrite (go e1) (go e2)
     | GenNode 15 [e] => AtomRead (go e)
     | GenNode 16 [GenLeaf (inr (inl (inl (inr T))));
                   GenLeaf (inr (inl (inr mut))); e] => Deref (go e) T mut
     | GenNode 17 [e] => Ref (go e)
     | GenNode 18 [GenLeaf (inr (inr (inl (inl path)))); e] => Field (go e) path
     | GenNode 19 [] => NewCall
     | GenNode 20 [e] => EndCall (go e)
     | GenNode 21 [GenLeaf (inr (inr (inl (inr kind)))); e; call] =>
        Retag (go e) kind (go call)
     | GenNode 22 (e :: el) => Case (go e) (go <$> el)
     | GenNode 23 [e] => Fork (go e)
     | GenNode 24 [GenLeaf (inr (inr (inr id)))] => SysCall id
     | _ => Lit LitPoison
     end) _).
  fix FIX 1. intros []; f_equal=>//; revert el; clear -FIX.
  - fix FIX_INNER 1. intros []; [done|]. by simpl; f_equal.
  - fix FIX_INNER 1. intros []; [done|]. by simpl; f_equal.
  - fix FIX_INNER 1. intros []; [done|]. by simpl; f_equal.
Qed.

Instance immediate_dec_eq: EqDecision immediate.
Proof.
  refine (λ v1 v2, cast_if (decide (of_immediate v1 = of_immediate v2)));
    abstract naive_solver.
Defined.
Instance immediate_countable : Countable immediate.
Proof.
  refine (inj_countable
    (λ v, match v with
          | LitV l => inl  l
          | RecV f xl e => inr (f, xl, e)
          end)
    (λ x, match x with
          | inl l => Some $ LitV l
          | inr (f, xl, e) =>
              match decide _ with left C => Some $ @RecV f xl e C | _ => None end
          end) _).
  intros [] =>//. by rewrite decide_left.
Qed.

Instance val_dec_eq : EqDecision val.
Proof.
  refine (λ v1 v2, cast_if (decide (of_val v1 = of_val v2))); abstract naive_solver.
Defined.
Instance val_countable : Countable val.
Proof.
  refine (inj_countable
    (λ v, match v with
          | ImmV v => inl $ inl v
          | TValV vl => inl $ inr vl
          | PlaceV l bor T => inr (l, bor, T)
          end)
    (λ x, match x with
          | inl (inl v) => Some $ ImmV $ v
          | inl (inr vl) => Some $ TValV vl
          | inr (l, bor, T) => Some $ PlaceV l bor T
          end) _).
  by intros [].
Qed.

Instance type_inhabited : Inhabited type := populate (Scalar 0).
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

Lemma to_immediates_elem_Some vl vl' el e:
  to_immediates vl el = Some vl' → e ∈ el → is_Some (to_val e).
Proof.
  revert vl. induction el as [|e' ? IH]; intros vl; [by intros _ ?%elem_of_nil|].
  rewrite to_immediates_cons.
  destruct (to_immediate e') as [v'|] eqn:Eq'; [|done].
  move => /= /IH In /elem_of_cons [->|/In //]. rewrite -(of_to_immediate _ _ Eq').
  destruct v'; simpl; [|rewrite decide_left]; naive_solver.
Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof.
  intros [v ?]. destruct Ki; simplify_option_eq; eauto.
  eapply to_immediates_elem_Some; eauto. set_solver.
Qed.

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
  destruct Ki1 as [|v1 vl1 el1| | |vl1 el1| | | | | | | | | | | | | | | | | | | | |],
           Ki2 as [|v2 vl2 el2| | |vl2 el2| | | | | | | | | | | | | | | | | | | | |];
  intros He1 He2 EQ; try discriminate; simplify_eq/=;
    repeat match goal with
    | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
    end; auto;
  destruct (list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2); auto; congruence.
Qed.

Lemma val_head_stuck e1 σ1 κ e2 σ2 efs :
  head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; inversion BaseStep; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 efs :
  head_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
Proof.
  destruct Ki; inversion_clear 1; inversion_clear BaseStep;
    simplify_option_eq; eauto; [done|..].
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
