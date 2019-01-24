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

Inductive base_lit :=
| LitPoison | LitLoc (l : loc) | LitInt (n : Z).

Inductive expr :=
(* variable *)
| Var (x : string)
(* values *)
| Lit (l : base_lit)
| Rec (f : binder) (xl : list binder) (e : expr)
(* lvalue *)
| Place (l : loc)
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
  | Lit _ | Place _ => true
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
| PlaceV (l: loc)
.

Bind Scope val_scope with val.

Definition of_val (v : val) : expr :=
  match v with
  | ImmV (RecV f x e) => Rec f x e
  | ImmV (LitV l) => Lit l
  | PlaceV l => Place l
  end.

Definition to_val (e : expr) : option val :=
  match e with
  | Rec f xl e =>
    if decide (Closed (f :b: xl +b+ []) e) then Some (ImmV (RecV f xl e)) else None
  | Lit l => Some (ImmV (LitV l))
  | Place l => Some (PlaceV l)
  | _ => None
  end.

(** Substitution *)
Fixpoint subst (x : string) (es : expr) (e : expr) : expr :=
  match e with
  | Var y => if bool_decide (y = x) then es else Var y
  | Lit l => Lit l
  | Rec f xl e =>
    Rec f xl $ if bool_decide (BNamed x ≠ f ∧ BNamed x ∉ xl) then subst x es e else e
  | Place l => Place l
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
| LocRefl l : lit_eq σ (LitLoc l) (LitLoc l)
(* Comparing unallocated pointers can non-deterministically say they are equal
   even if they are not.  Given that our `free` actually makes addresses
   re-usable, this may not be strictly necessary, but it is the most
   conservative choice that avoids UB (and we cannot use UB as this operation is
   possible in safe Rust).  See
   <https://internals.rust-lang.org/t/comparing-dangling-pointers/3019> for some
   more background. *)
| LocUnallocL l1 l2 :
    σ !! l1 = None →
    lit_eq σ (LitLoc l1) (LitLoc l2)
| LocUnallocR l1 l2 :
    σ !! l2 = None →
    lit_eq σ (LitLoc l1) (LitLoc l2).

Inductive lit_neq : base_lit → base_lit → Prop :=
| IntNeq z1 z2 :
    z1 ≠ z2 → lit_neq (LitInt z1) (LitInt z2)
| LocNeq l1 l2 :
    l1 ≠ l2 → lit_neq (LitLoc l1) (LitLoc l2)
| LocNeqNullR l :
    lit_neq (LitLoc l) (LitInt 0)
| LocNeqNullL l :
    lit_neq (LitInt 0) (LitLoc l).

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
| BinOpOffset l z :
    bin_op_eval σ OffsetOp (LitLoc l) (LitInt z) (LitLoc $ l +ₗ z).

Definition stuck_term := App (Lit $ LitInt 0) [].


Notation time := nat.

Inductive borrow :=
| UniqB (t: time)
| ShrB (ot : option time)
.

Inductive ref_kind := | UniqueRef | FrozenRef | RawRef.

Inductive event :=
| AllocEvt (l : loc) (n: positive) (bor: borrow)
| DeallocEvt (l: loc) (n : positive) (bor: borrow)
| ReadEvt (l: loc) (v: immediate) (bor: borrow)
| WriteEvt (l: loc) (v: immediate) (bor: borrow)
| UpdateEvt (l: loc) (vr vw: immediate) (bor: borrow)
| DerefEvt (l: loc) (bor: borrow) (ref: ref_kind)
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
| RefBS l σ :
    is_Some (σ !! l) →
    base_step (Ref (Place l)) σ None (Lit (LitLoc l)) σ []
| DerefBS l bor ref σ :
    is_Some (σ !! l) →
    base_step (Deref (Lit (LitLoc l))) σ
              (Some $ DerefEvt l bor ref)
              (Place l) σ
              []
| ReadBS l v bor σ :
    σ !! l = Some v →
    base_step (Read (Place l)) σ
              (Some $ ReadEvt l v bor)
              (of_val (ImmV v)) σ
              []
| WriteS l e v bor σ :
    is_Some (σ !! l) →
    to_val e = Some (ImmV v) →
    base_step (Write (Place l) e) σ
              (Some $ WriteEvt l v bor)
              (Lit LitPoison) (<[l:=v]>σ)
              []
| CasFailS l e1 v1 e2 v2 vr bor σ :
    to_val e1 = Some $ ImmV $ LitV v1 → to_val e2 = Some $ ImmV $ LitV v2 →
    σ !! l = Some (LitV vr) →
    lit_neq v1 vr →
    base_step (CAS (Place l) e1 e2) σ
              (Some $ ReadEvt l (LitV vr) bor)
              (Lit $ lit_of_bool false) σ
              []
| CasSucS l e1 v1 e2 v2 vr bor σ :
    to_val e1 = Some $ ImmV $ LitV v1 → to_val e2 = Some $ ImmV $ LitV v2 →
    σ !! l = Some (LitV vr) →
    lit_eq σ v1 vr →
    base_step (CAS (Place l) e1 e2) σ
              (Some $ UpdateEvt l (LitV vr) (LitV v2) bor)
              (Lit $ lit_of_bool true) (<[l:=(LitV v2)]>σ)
              []
| AllocS n l bor σ :
    0 < n →
    (∀ m, σ !! (l +ₗ m) = None) →
    base_step (Alloc $ Lit $ LitInt n) σ
              (Some $ AllocEvt l (Z.to_pos n) bor)
              (Place l) (init_mem l (Z.to_nat n) σ)
              []
| FreeS n l bor σ :
    0 < n →
    (∀ m, is_Some (σ !! (l +ₗ m)) ↔ 0 ≤ m < n) →
    base_step (Free (Lit $ LitInt n) (Place l)) σ
              (Some $ DeallocEvt l (Z.to_pos n) bor)
              (Lit LitPoison) (free_mem l (Z.to_nat n) σ)
              []
| CaseS i el e σ :
    0 ≤ i →
    el !! (Z.to_nat i) = Some e →
    base_step (Case (Lit $ LitInt i) el) σ None e σ []
| ForkS e σ:
    base_step (Fork e) σ None (Lit LitPoison) σ [e].

(* Instrumented state: tags and stack borrows. *)
Definition tags := gmap loc borrow.

Notation call_id := nat.

Inductive stack_item :=
| Uniq (t: time)
| Shr
| FnBarrier (ci : call_id)
.

Record bor_stack := mkBorStack {
  borrows     : list stack_item;
  frozen_since: option time;
}.

Definition stacks := gmap loc bor_stack.

Inductive retag_kind :=
| FnEntry
| TwoPhase
| Raw
| Default
.

Fixpoint init_stack (l:loc) (n:nat) (β:stacks) (si: stack_item) : stacks :=
  match n with
  | O => β
  | S n => <[l:= mkBorStack [si] None]>(init_stack (l +ₗ 1) n β si)
  end.

Definition is_frozen (s : bor_stack) : Prop := is_Some s.(frozen_since).

Definition barriers := gmap call_id bool.

Definition is_active (bar: barriers) (c: call_id) : bool :=
  bool_decide (bar !! c = Some true).

Fixpoint match_access
  (stack: list stack_item) (bor: borrow) (read: bool) (bar: barriers)
  : option (list stack_item) :=
  match stack, bor with
  | FnBarrier c :: stack', _ =>
      if (is_active bar c) then None
      else match_access stack' bor read bar
  |  Uniq t1 :: stack', UniqB t2 =>
      if (decide (t1 = t2))
      then Some stack
      else match_access stack' bor read bar
  | Shr :: _, ShrB _ => Some stack
  | Shr :: stack', _ =>
      if read
      then Some stack
      else match_access stack' bor read bar
  | _ :: stack', _ => match_access stack' bor read bar
  | _, _ => None
  end.


Inductive instrumented_step :
  tags → stacks → barriers → option event → tags → stacks → Prop :=
| DefaultIS τ α β :
    instrumented_step τ α β None τ α
| AllocHeapIS τ α β l n :
    instrumented_step τ α β
                      (Some $ AllocEvt l n (ShrB None))
                      (<[l := ShrB None]> τ)
                      (init_stack l (Pos.to_nat n) α Shr)
| AllocStackIS τ α β t x n :
    instrumented_step τ α β
                      (Some $ AllocEvt x n (UniqB t))
                      (<[x := UniqB t]> τ)
                      (init_stack x (Pos.to_nat n) α (Uniq t))
| ReadFrozenIS τ α β l v bor stack :
    (α !! l = Some stack) →
    is_frozen stack →
    instrumented_step τ α β
                      (Some $ ReadEvt l v bor) τ α
| ReadUnfreeze τ α β l v bor stack stack':
    (α !! l = Some stack) →
    instrumented_step τ α β
                      (Some $ ReadEvt l v bor) τ
                      (<[l := mkBorStack stack' None ]> α).
