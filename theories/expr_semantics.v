From Equations Require Import Equations.
From stdpp Require Export gmap.

(* TODO: remove list of expressions *)
(* TODO: fixing the set of used protectors as a counter *)

From stbor Require Export lang_base notation.

Set Default Proof Using "Type".

(*** EXPRESSION SEMANTICS --------------------------------------------------***)

(** Substitution *)
Fixpoint subst (x : string) (es : expr) (e : expr) : expr :=
  match e with
  | Var y => if bool_decide (y = x) then es else Var y
  | Lit l => Lit l
  (* | Rec f xl e =>
    Rec f xl $ if bool_decide (BNamed x ≠ f ∧ BNamed x ∉ xl) then subst x es e else e *)
  | Call e el => Call (subst x es e) (map (subst x es) el)
  | InitCall e => InitCall (subst x es e)
  | EndCall e => EndCall (subst x es e)
  | Place l tag T => Place l tag T
  (* | App e1 el => App (subst x es e1) (map (subst x es) el) *)
  | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
  | TVal el => TVal (map (subst x es) el)
  | Proj e1 e2 => Proj (subst x es e1) (subst x es e2)
  | Conc e1 e2 => Conc (subst x es e1) (subst x es e2)
  | Copy e => Copy (subst x es e)
  | Write e1 e2 => Write (subst x es e1) (subst x es e2)
  | Alloc T => Alloc T
  | Free e => Free (subst x es e)
  (* | CAS e0 e1 e2 => CAS (subst x es e0) (subst x es e1) (subst x es e2) *)
  (* | AtomWrite e1 e2 => AtomWrite (subst x es e1) (subst x es e2) *)
  (* | AtomRead e => AtomRead (subst x es e) *)
  | Deref e T => Deref (subst x es e) T
  | Ref e => Ref (subst x es e)
  | Field e path => Field (subst x es e) path
  | Retag e kind => Retag (subst x es e) kind
  | Let x1 e1 e2 =>
      Let x1 (subst x es e1)
                 (if bool_decide (BNamed x ≠ x1) then subst x es e2 else e2)
  | Case e el => Case (subst x es e) (map (subst x es) el)
  (* | Fork e => Fork (subst x es e) *)
  (* | SysCall id => SysCall id *)
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
Arguments subst_l _%binder _ _%E.

Definition subst_v (xl : list binder) (vsl : vec val (length xl))
                   (e : expr) : expr :=
  Vector.fold_right2 (λ b, subst' b ∘ of_val) e _ (list_to_vec xl) vsl.
Arguments subst_v _%binder _ _%E.

Lemma subst_v_eq (xl : list binder) (vsl : vec val (length xl)) e :
  Some $ subst_v xl vsl e = subst_l xl (of_val <$> vec_to_list vsl) e.
Proof.
  revert vsl. induction xl=>/= vsl; inv_vec vsl=>//=v vsl. by rewrite -IHxl.
Qed.

(** Evaluation contexts *)
Inductive ectx_item :=
(* | AppLCtx (el : list expr) *)
(* | AppRCtx (v : val) (vl : list val) (el : list expr) *)
| CallLCtx (el: list expr)
| CallRCtx (v : val) (vl : list val) (el : list expr)
| EndCallCtx
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
(* | CasLCtx (e1 e2: expr) *)
(* | CasMCtx (v0 : val) (e2 : expr) *)
(* | CasRCtx (v0 : val) (v1 : val) *)
(* | AtRdCtx *)
(* | AtWrLCtx (e : expr) *)
(* | AtWrRCtx (v : val) *)
| DerefCtx (T: type)
| RefCtx
| FieldCtx (path : list nat)
| RetagCtx (kind: retag_kind)
| LetCtx (x: binder) (e2: expr)
| CaseCtx (el : list expr).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  (* | AppLCtx el => App e el *)
  (* | AppRCtx v vl el => App (of_val v) ((of_val <$> vl) ++ e :: el) *)
  | CallLCtx el => Call e el
  | CallRCtx v vl el => Call (of_val v) ((of_val <$> vl) ++ e :: el)
  | EndCallCtx => EndCall e
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
  (* | CasLCtx e1 e2 => CAS e e1 e2 *)
  (* | CasMCtx v0 e2 => CAS (of_val v0) e e2 *)
  (* | CasRCtx v0 v1 => CAS (of_val v0) (of_val v1) e *)
  (* | AtRdCtx => AtomRead e *)
  (* | AtWrLCtx e2 => AtomWrite e e2 *)
  (* | AtWrRCtx v1 => AtomWrite (of_val v1) e *)
  | DerefCtx T => Deref e T
  | RefCtx => Ref e
  | FieldCtx path => Field e path
  | RetagCtx kind => Retag e kind
  | LetCtx x e2 => Let x e e2
  | CaseCtx el => Case e el
  end.

(** The stepping relation *)
(* Be careful to make sure that poison is always stuck when used for anything
   except for reading from or writing to memory! *)
Definition Z_of_bool (b : bool) : Z :=
  if b then 1 else 0.

Definition lit_of_bool (b : bool) : lit :=
  LitInt $ Z_of_bool b.

Coercion lit_of_bool : bool >-> lit.
Coercion LitInt : Z >-> lit.

Implicit Type (h: mem).

Fixpoint init_mem (l:loc) (n:nat) h : mem :=
  match n with
  | O => h
  | S n => <[l := LitPoison]>(init_mem (l +ₗ 1) n h)
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

(* Compute subtype of `T` and offset to it from `path` *)
Fixpoint field_access (T: type) (path : list nat) :
  option (nat * type) :=
  match path with
  | [] => Some (O, T)
  | i :: path =>
    match T with
    | Scalar sz =>
        if bool_decide (i ≤ sz) then Some (i, Scalar (sz - i)) else None
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

Fixpoint write_mem l (vl: list lit) h: mem :=
  match vl with
  | [] => h
  | v :: vl => write_mem (l +ₗ 1) vl (<[l := v]> h)
  end.

Equations read_mem (l: loc) (n: nat) h: option (list lit) :=
  read_mem l n h := go l n (Some [])
  where go : loc → nat → option (list lit) → option (list lit) :=
        go l O      oacc := oacc;
        go l (S n)  oacc :=
          acc ← oacc ;
          v ← h !! l;
          go (l +ₗ 1) n (Some (acc ++ [v])).

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

Inductive pure_expr_step (FNs: fn_env) (h: mem) : expr → event → expr → Prop :=
| BinOpPS op l1 l2 l' :
    bin_op_eval h op l1 l2 l' →
    pure_expr_step FNs h (BinOp op (#[ #l1]) (#[ #l2])) SilentEvt (#[ #l'])
(* TODO: add more operations for tempvalue lists *)
| ProjBS el (i: Z) vl v
    (DEFINED: 0 ≤ i ∧ vl !! (Z.to_nat i) = Some v)
    (VALUES: to_val (TVal el) = Some (TValV vl)) :
    pure_expr_step FNs h (Proj (TVal el) #i) SilentEvt #v
| ConcBS el1 el2 vl1 vl2
    (VALUES1: to_val (TVal el1) = Some (TValV vl1))
    (VALUES2: to_val (TVal el2) = Some (TValV vl2)) :
    pure_expr_step FNs h (Conc (TVal el1) (TVal el2))
                         SilentEvt (of_val (TValV (vl1 ++ vl2)))
| RefBS l lbor T :
    is_Some (h !! l) →
    pure_expr_step FNs h (Ref (Place l lbor T)) SilentEvt #(LitLoc l lbor)
| DerefBS l lbor T
    (DEFINED: ∀ (i: nat), (i < tsize T)%nat → l +ₗ i ∈ dom (gset loc) h) :
    pure_expr_step FNs h ( *{T} #(LitLoc l lbor)) SilentEvt (Place l lbor T)
| FieldBS l lbor T path off T'
    (FIELD: field_access T path = Some (off, T')) :
    pure_expr_step FNs h (Field (Place l lbor T) path)
                         SilentEvt (Place (l +ₗ off) lbor T')
| LetBS x e1 e2 e' :
    is_Some (to_val e1) →
    subst x e2 e1 = e' →
    pure_expr_step FNs h (let: x := e1 in e2) SilentEvt e'
| CaseBS i el e :
    0 ≤ i →
    el !! (Z.to_nat i) = Some e →
    pure_expr_step FNs h (case: #i of el) SilentEvt e
| CallBS name el xl e HC e':
    FNs !! name = Some (@FunV xl e HC) →
    Forall (λ ei, is_Some (to_val ei)) el →
    subst_l xl el e = Some e' →
    pure_expr_step FNs h (Call #(LitFnPtr name) el)
                         (NewCallEvt name) (InitCall e').


Inductive mem_expr_step (h: mem) : expr → event → mem → expr → Prop :=
| InitCallBS e (c: call_id):
    mem_expr_step
              h (InitCall e)
              (InitCallEvt c)
              h (EndCall e)
| EndCallBS (call: call_id) e v:
    to_val e = Some v →
    mem_expr_step h (EndCall e) (EndCallEvt call) h v
| CopyBS l lbor T (vl: list lit)
    (READ: read_mem l (tsize T) h = Some vl)
    (* (LEN: length vl = tsize T) *)
    (* (VALUES: ∀ (i: nat), (i < length vl)%nat → h !! (l +ₗ i) = vl !! i) *) :
    mem_expr_step
              h (Copy (Place l lbor T))
              (CopyEvt l lbor T vl)
              h (of_val (TValV vl))
| WriteBS l lbor T el vl (LENe: length vl = tsize T)
    (DEFINED: ∀ (i: nat), (i < length vl)%nat → l +ₗ i ∈ dom (gset loc) h)
    (VALUES: to_val (TVal el) = Some (TValV vl)) :
    mem_expr_step
              h (Place l lbor T <- TVal el)
              (WriteEvt l lbor T vl)
              (write_mem l vl h) #☠
| AllocBS lbor T :
    let l := (fresh_block h, 0) in
    mem_expr_step
              h (Alloc T)
              (AllocEvt l lbor T)
              (init_mem l (tsize T) h) (Place l lbor T)
| DeallocBS T l lbor :
    (∀ m, is_Some (h !! (l +ₗ m)) ↔ 0 ≤ m < tsize T) →
    mem_expr_step
              h (Free (Place l lbor T))
              (DeallocEvt l lbor T)
              (free_mem l (tsize T) h) #☠
| RetagBS x xbor T kind :
    mem_expr_step
              h (Retag (Place x xbor T) kind)
              (RetagEvt x T kind)
              h (Lit LitPoison)
(* | ForkBS e h:
    expr_step (Fork e) h SilentEvt (Lit LitPoison) h [e] *)
(* observable behavior *)
(* | SysCallBS id h:
    expr_step (SysCall id) h (SysCallEvt id) (Lit LitPoison) h [] *)
.
