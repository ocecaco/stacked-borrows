From iris.program_logic Require Export language ectx_language ectxi_language.
From stdpp Require Export strings.
From stdpp Require Import gmap infinite.
Set Default Proof Using "Type".

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

Inductive type :=
  | Scala (sz: positive)
  | Reference (kind: mutability) (t: type)
  | Unsafe (t: type)
  | Union (t1: type) (t2: type)
  | Product (t1: type) (t2: type)
  (* TODO: | Sum (t1: type) (t2: type) *)
  .

Fixpoint tsize (t: type) : positive :=
  match t with
  | Scala sz => sz
  | Reference _ _ => 1%positive     (* We do not go beyond pointers *)
  | Unsafe t1 => tsize t1
  | Union t1 t2 => Pos.max (tsize t1) (tsize t2)
  | Product t1 t2 => (tsize t1) + (tsize t2)
  end.

(* Type doesn't contain UnsafeCells. *)
Fixpoint is_freeze (t: type) : bool :=
  match t with
  | Scala _ | Reference _ _ => true
  | Unsafe _ => false
  | Union t1 t2 | Product t1 t2 => is_freeze t1 && is_freeze t2
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

Implicit Type (α: bstacks) (β: barriers).


(*** BASE SEMANTICS --------------------------------------------------------***)

(** Unary/Binary ops *)
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

(** Base values *)
Inductive base_lit :=
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
| Lit (l : base_lit)
(* base lambda calculus *)
| Var (x : string)
| App (e : expr) (el : list expr)
| Rec (f : binder) (xl : list binder) (e : expr)
(* bin op *)
| BinOp (op : bin_op) (e1 e2 : expr)
(* lvalue *)
| Place (l: loc) (tag: borrow)    (* A place is a tagged pointer: every access
                                     to memory revolves around a place. *)
| Deref (e: expr) (t: type) (kind: ref_kind)
                                  (* Deference a pointer `e` into a place
                                     presenting the location that `e` points to.
                                     The location has type `t` and the pointer
                                     has reference kind `kind`. *)
| Ref (e: expr)                   (* Turn a place `e` into a pointer value. *)
| Field (e1 e2: expr)             (* Create a place that points to a component
                                     of the place `e1`. *)
(* mem op *)
| Read (e : expr)                 (* Read from the place `e` *)
| Write (e1 e2: expr)             (* Write the value `e2` to the place `e1` *)
| CAS (e0 e1 e2 : expr)           (* CAS the value `e2` for `e1` to the place `e0` *)
| Alloc (t: type) (amod: alloc_mod) (* Allocate a place of type `t` *)
| Free (e : expr) (t: type)       (* Free the place `e` of type `t` *)
(* function call tracking *)
| NewCall                         (* Issue a fresh id for the call *)
| EndCall (e: expr)               (* End the call with id `e` *)
(* retag *)
| Retag (e: expr) (t: type) (kind: retag_kind)
                                  (* Retag the place `e` of type `t` with retag
                                     kind `kind`. *)
(* case *)
| Case (e : expr) (el : list expr)
(* concurrency *)
| Fork (e : expr)
.

Arguments App _%E _%E.
Arguments Case _%E _%E.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Lit _ | Place _ _ | Alloc _ _ | NewCall => true
  | Var x => bool_decide (x ∈ X)
  | Rec f xl e => is_closed (f :b: xl +b+ X) e
  | BinOp _ e1 e2 | Write e1 e2  | Field e1 e2 =>
    is_closed X e1 && is_closed X e2
  | App e el | Case e el => is_closed X e && forallb (is_closed X) el
  | Read e | Deref e _ _ | Ref e | Free e _ | EndCall e | Retag e _ _ | Fork e => is_closed X e
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
  | Alloc t amod => Alloc t amod
  | Free e t => Free (subst x es e) t
  | Deref e t kind => Deref (subst x es e) t kind
  | Ref e => Ref (subst x es e)
  | Field e1 e2 => Field (subst x es e1) (subst x es e2)
  | NewCall => NewCall
  | EndCall e => EndCall (subst x es e)
  | Retag e t kind => Retag (subst x es e) t kind
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
| FreeCtx (t: type)
| DerefCtx (t: type) (kind: ref_kind)
| RefCtx
| FieldLCtx (e : expr)
| FieldRCtx (v : val)
| EndCallCtx
| RetagCtx (t: type) (kind: retag_kind)
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
  | FreeCtx t=> Free e t
  | DerefCtx t kind => Deref e t kind
  | RefCtx => Ref e
  | FieldLCtx e2 => Field e e2
  | FieldRCtx v1 => Field (of_val v1) e
  | EndCallCtx => EndCall e
  | RetagCtx t kind => Retag e t kind
  | CaseCtx el => Case e el
  end.

(** Main state: a heap of immediates. *)
Definition mem := gmap loc immediate.
Implicit Type (σ: mem).

(** The stepping relation *)
(* Be careful to make sure that poison is always stuck when used for anything
   except for reading from or writing to memory! *)
Definition Z_of_bool (b : bool) : Z :=
  if b then 1 else 0.

Definition lit_of_bool (b : bool) : base_lit :=
  LitInt $ Z_of_bool b.

Fixpoint init_mem (l:loc) (n:nat) σ : mem :=
  match n with
  | O => σ
  | S n => <[l:=LitV LitPoison]>(init_mem (l +ₗ 1) n σ)
  end.

Fixpoint free_mem (l:loc) (n:nat) σ : mem :=
  match n with
  | O => σ
  | S n => delete l (free_mem (l +ₗ 1) n σ)
  end.

Inductive lit_eq σ : base_lit → base_lit → Prop :=
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

Inductive bin_op_eval σ : bin_op → base_lit → base_lit → base_lit → Prop :=
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

Inductive event :=
| AllocEvt (l : loc) (n: positive) (lbor: borrow) (amod: alloc_mod)
| DeallocEvt (l: loc) (n : positive) (lbor: borrow)
| ReadEvt (l: loc) (lbor: borrow) (v: immediate)
| WriteEvt (l: loc) (lbor: borrow) (v: immediate)
| DerefEvt (l: loc) (lbor: borrow) (t: type) (ref: ref_kind)
| NewCallEvt (call: call_id)
| EndCallEvt (call: call_id)
| RetagEvt (x l: loc) (t: type) (bor bor': borrow)
           (mut: option mutability) (rt: retag_kind)
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
| ReadBS l v lbor σ :
    σ !! l = Some v →
    base_step (Read (Place l lbor)) σ
              (Some $ ReadEvt l lbor v)
              (of_val (ImmV v)) σ
              []
| WriteBS l e v lbor σ :
    is_Some (σ !! l) →
    to_val e = Some (ImmV v) →
    base_step (Write (Place l lbor) e) σ
              (Some $ WriteEvt l lbor v)
              (Lit LitPoison) (<[l:=v]>σ)
              []
| AllocBS t l lbor amod σ :
    (∀ m, σ !! (l +ₗ m) = None) →
    base_step (Alloc t amod) σ
              (Some $ AllocEvt l (tsize t) lbor amod)
              (Place l lbor) (init_mem l (Pos.to_nat (tsize t)) σ)
              []
| FreeBS t l lbor σ :
    (∀ m, is_Some (σ !! (l +ₗ m)) ↔ 0 ≤ m < Z.pos (tsize t)) →
    base_step (Free (Place l lbor) t) σ
              (Some $ DeallocEvt l (tsize t) lbor)
              (Lit LitPoison) (free_mem l (Pos.to_nat (tsize t)) σ)
              []
| NewCallBS call σ:
    base_step NewCall σ
              (Some $ NewCallEvt call) (Lit $ LitInt call) σ []
| EndCallBS call σ:
    (0 ≤ call) →
    base_step (EndCall (Lit $ LitInt call)) σ
              (Some $ EndCallEvt (Z.to_nat call)) (Lit LitPoison) σ []
| RefBS l lbor σ :
    is_Some (σ !! l) →
    base_step (Ref (Place l lbor)) σ None (Lit (LitLoc l lbor)) σ []
| DerefBS l lbor ref t σ :
    is_Some (σ !! l) →
    base_step (Deref (Lit (LitLoc l lbor)) t ref) σ
              (Some $ DerefEvt l lbor t ref)
              (Place l lbor) σ
              []
| FieldBS l lbor z σ :
    base_step (Field (Place l lbor) (Lit $ LitInt z)) σ
              None (Place (l +ₗ z) lbor) σ []
| RetagBS x xbor l lbor lbor' om t kind σ:
    base_step (Retag (Place x xbor) t kind) σ
              (Some $ RetagEvt x l t lbor lbor' om kind) (Lit LitPoison) σ []
| CaseBS i el e σ :
    0 ≤ i →
    el !! (Z.to_nat i) = Some e →
    base_step (Case (Lit $ LitInt i) el) σ None e σ []
| ForkBS e σ:
    base_step (Fork e) σ None (Lit LitPoison) σ [e].

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
Definition access1 (stack: bstack) bor access β : option bstack :=
  match stack.(frozen_since), access with
  (* accept all reads if frozen *)
  | Some _, AccessRead => Some stack
  (* otherwise, unfreeze *)
  | _,_ => match access1' stack.(borrows) bor access β with
           | Some stack' => Some (mkBorStack stack' None)
           | _ => None
           end
  end.

(* Perform the access check on a block of continuous memory.
 * This implements Stacks::access. *)
Fixpoint accessN α β l (bor: borrow) (n: nat) (kind: access_kind) : option bstacks :=
  match n with
  | O => Some α
  | S n =>
      let l' := (l +ₗ n) in
      match (α !! l') with
      | Some stack => match (access1 stack bor kind β) with
                      | Some stack' =>
                          accessN (<[l' := stack']> α) β l bor n kind
                      | _ => None
                      end
      | _ => None
      end
  end.

(* Alternative definition as Inductive predicate.
Inductive accessN α β (bor: borrow) (kind: access_kind) l : nat → bstacks → Prop :=
| ACNBase
  : accessN α β bor kind l O α
| ACNRecursive n stack stack' α'
    (STACK: α !! l = Some stack)
    (ACC1 : access1 stack bor kind β = Some stack')
    (ACCN : accessN (<[l := stack']> α) β bor kind (l +ₗ 1) n α')
  : accessN α β bor kind l (S n) α'.
*)

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

(* Alternative definition as Inductive predicate.
Inductive derefN α (bor: borrow) (kind: ref_kind) l : nat → Prop :=
| DRNBase
  : derefN α bor kind l O
| DRNRecursive n stack
    (STACK: α !! l = Some stack)
    (DR1 : is_Some (deref1 stack bor kind))
    (DRN : derefN α bor kind (l +ₗ 1) n)
  : derefN α bor kind l (S n).
*)

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
  (l: loc) (t: type) (f: A → loc → nat → bool → option A) (a: A)
  (last cur_dist: nat) :
  option (A * (nat * nat)) :=
  match t with
  | Scala n => Some (a, (last, cur_dist + Pos.to_nat n)%nat)
  | Reference _ _ => Some (a, (last, S cur_dist))
  | Unsafe t1 =>
      (* apply the action `f` and return new `last` and `cur_dist` *)
      unsafe_action f a l last cur_dist (Pos.to_nat (tsize t1))
  | Union _ _ =>
      (* If it's a union, look at the type to see if there is Unsafe *)
      if is_freeze t
      (* No UnsafeCell, continue *)
      then Some (a, (last, cur_dist + (Pos.to_nat (tsize t)))%nat)
      (* There can be UnsafeCell, perform `f a _ _ false` on the whole block *)
      else unsafe_action f a l last cur_dist (Pos.to_nat (tsize t))
  | Product t1 t2 =>
      (* this implements left-to-right search on the type, which guarantees
         that the indices are increasing. *)
      match visit_freeze_sensitive' l t1 f a last cur_dist with
      | Some (a', (last', cur_dist')) =>
          visit_freeze_sensitive' l t2 f a' last' cur_dist'
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
Definition ptr_deref α (l: loc) (bor: borrow) (t: type) (mut: option mutability) : Prop :=
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
        visit_freeze_sensitive l t
          (λ _ l' sz frozen,
              (* If is in Unsafe, treat as a RawRef, otherwise FrozenRef *)
              let kind := if frozen then FrozenRef else RawRef in
                derefN α l' bor sz kind) ())
  | _, Some mut =>
      (* Otherwise, just treat this as one big chunk. *)
      let kind := match mut with Mutable => UniqueRef | _ => RawRef end in
      is_Some (derefN α l bor (Pos.to_nat (tsize t)) kind)
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
               match access1 stack bor (to_access_kind kind') β with
               | Some stack1 => create_borrow stack1 bor' kind'
               | None => None
               end
      | None, _ ,_ =>
          (* check for access with bor, then reborrow with bor' *)
          match access1 stack bor (to_access_kind kind') β with
          | Some stack1 => create_borrow stack1 bor' kind'
          | None => None
          end
      | Some c, _, _ =>
          (* check for access with bor, then add barrier & reborrow with bor' *)
          match access1 stack bor (to_access_kind kind') β with
          | Some stack1 => create_borrow (add_barrier stack1 c) bor' kind'
          | None => None
          end
      end
  | None => None
  end.

(*
Inductive reborrow1
  (stack: bstack) (bor: borrow) (kind': ref_kind) β :
  option call_id → borrow → bstack → Prop :=
| RB1Redundant bor' ptr_idx
    (* Try deref1 with old tag `bor` but new `kind'`*)
    (OLD_DEREF: deref1 stack bor kind' = Some ptr_idx)
    (* Redundant check when there's no barrier *)
    (REDUNDANT: bor_redundant_check stack bor' kind' ptr_idx)
    (SHARED   : is_aliasing bor')
  : reborrow1 stack bor kind' β None bor' stack
| RB1NonRedundantNoBarrier bor' stack1 stack' ptr_idx
    (OLD_DEREF : deref1 stack bor kind' = Some ptr_idx)
    (REDUNDANT : ¬ bor_redundant_check stack bor' kind' ptr_idx)
    (REACTIVATE: access1 stack bor (to_access_kind kind') β = Some stack1)
    (PUSH: push_borrow stack1 bor' kind' stack')
  : reborrow1 stack bor kind' β None bor' stack'
| RB1NonRedundantBarrier c bor' stack1 stack'
    (OLD_DEREF : is_Some (deref1 stack bor kind'))
    (REACTIVATE: access1 stack bor (to_access_kind kind') β = Some stack1)
    (PUSH: push_borrow (add_barrier stack1 c) bor' kind' stack')
  : reborrow1 stack bor kind' β (Some c) bor' stack'. *)

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

(* Inductive reborrowN α β (bor: borrow) (kind': ref_kind) (l: loc)
  : nat → option call_id → borrow → bstacks → Prop :=
| RBNBase bar bor'
  : reborrowN α β bor kind' l O bar bor' α
| RBNRecursive n stack stack' bar bor' α'
    (STACK: α !! l = Some stack)
    (REBOR1: reborrow1 stack bor kind' β bar bor' stack')
    (REBORN: reborrowN (<[l := stack']> α) β bor kind' (l +ₗ 1) n bar bor' α')
  : reborrowN α β bor kind' l (S n) bar bor' α'. *)

(* This implements Stacks::reborrow *)
Definition reborrowBlock α β l n bor bor' kind' bar : option bstacks :=
  if xorb (is_unique bor') (is_unique_ref kind') then None
  else let bar' := match kind' with RawRef => None | _ => bar end in
       reborrowN α β l n bor bor' kind' bar.

(* Inductive reborrowBlock α β l bor n bar bor' kind' α': Prop :=
| RBBBase bar'
    (UNIQUE: is_unique bor' ↔ kind' = UniqueRef)
    (BAR: bar' = match kind' with
                 | RawRef => None
                 | _ => bar
                 end)
    (BOR: reborrowN α β bor kind' l n bar' bor' α').
 *)

(* This implements EvalContextPrivExt::reborrow *)
(* TODO?: alloc.check_bounds(this, ptr, size)?; *)
Definition reborrow α β l bor (t: type) (bar: option call_id) bor' :=
  match bor' with
  | AliasB (Some _) =>
      (* We need freeze-sensitive reborrow, depending on whether some memory is
         in UnsafeCell or not *)
      visit_freeze_sensitive l t
          (λ α' l' sz frozen,
              (* If is in Unsafe, treat as a RawRef, otherwise FrozenRef *)
              let kind' := if frozen then FrozenRef else RawRef in
                reborrowBlock α' β l' sz bor bor' kind' bar) α
  | _ =>
      (* Just treat this as one big chunk. *)
      let kind' := match bor' with UniqB _ => UniqueRef | _ => RawRef end in
      reborrowBlock α β l (Pos.to_nat (tsize t)) bor bor' kind' bar
  end.

(* Inductive reborrow α β l bor (t: type)
  : option call_id → borrow → stacks → Prop :=
| RBBlock n bar bor' α'
  (* Only Unique or Raw reborrow *)
  (RBB: match bor' with
        | UniqB _ => reborrowBlock α β bor UniqueRef l n bar bor' α'
        | AliasB None => reborrowBlock α β bor RawRef l n bar bor' α'
        | _ => False
        end)
  : reborrow α β bor l (inl n) bar bor' α'
| RBRange t rs bar α'
  (* Freezing possibly with UnsafeCell *)
  (RBF: reborrowFreezeSensitive α β bor l t rs bar α')
  : reborrow α β bor l (inr rs) bar (AliasB (Some t)) α'. *)

(** Instrumented step for the stacked borrows *)
(* This ignores CAS for now. *)
Inductive instrumented_step σ α β (clock: time):
  option event → mem → stacks → barriers → time → Prop :=
| DefaultIS :
    instrumented_step σ α β clock None σ α β clock
| AllocHeapIS σ' l n :
    instrumented_step σ α β clock
                      (Some $ AllocEvt l n (AliasB None) Heap) σ'
                      (init_stacks l (Pos.to_nat n) α Raw) β clock
| AllocStackIS σ' t x n :
    instrumented_step σ α β clock
                      (Some $ AllocEvt x n (UniqB t) Stack) σ'
                      (init_stacks x (Pos.to_nat n) α (Uniq clock)) β (clock + 1)
| ReadFrozenIS l v lbor stack :
    (α !! l = Some stack) →
    is_frozen stack →
    instrumented_step σ α β clock
                      (Some $ ReadEvt l lbor v) σ α β clock
| ReadUnfrozenIS l v lbor stack stack':
    (α !! l = Some stack) →
    (¬ is_frozen stack) →
    (access1 stack.(borrows) lbor AccessRead β = Some stack') →
    instrumented_step σ α β clock
                      (Some $ ReadEvt l lbor v) σ
                      (<[ l := mkBorStack stack' None ]> α) β clock
| WriteIS σ' l v lbor stack stack' :
    (α !! l = Some stack) →
    (access1 stack.(borrows) lbor AccessWrite β = Some stack') →
    instrumented_step σ α β clock
                      (Some $ WriteEvt l lbor v) σ'
                      (<[ l := mkBorStack stack' None ]> α) β clock
| DeallocIS σ' l n lbor stack stack' :
    (α !! l = Some stack) →
    (access1 stack.(borrows) lbor AccessDealloc β = Some stack') →
    instrumented_step σ α β clock
                      (Some $ DeallocEvt l n lbor) σ'
                      (<[ l := mkBorStack stack' None ]> α) β clock
| DerefIS l n lbor kind :
    check_derefN α lbor kind l n →
    instrumented_step σ α β clock
                      (Some $ DerefEvt l lbor kind) σ α β clock
| NewCallIS:
    let call : call_id := fresh_generic (dom (gset call_id) β) in
    instrumented_step σ α β clock
                      (Some $ NewCallEvt call) σ α (<[call := true]>β) clock
| EndCallIS call
    (ACTIVE: β !! call = Some true):
    instrumented_step σ α β clock
                      (Some $ EndCallEvt call) σ α (<[call := false]>β) clock.
(* | RetagIS α' x l n bor bor' rkind bar :
    (σ !! x = Some $ LitV $ LitLoc l bor) →
    (reborrowN α β bor rkind l (Pos.to_nat n) bar bor' α') →
    instrumented_step σ α β
                      (Some $ RetagEvt x l n bor bor' bar)
                      (<[ x := LitV $ LitLoc l bor' ]> σ) α'. *)

(** COMBINED SEMANTICS -------------------------------------------------------*)
