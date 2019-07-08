From Equations Require Import Equations.
From stdpp Require Export gmap.

From stbor.lang Require Export lang_base notation.

Set Default Proof Using "Type".

(*** EXPRESSION SEMANTICS --------------------------------------------------***)

(** Substitution *)
Fixpoint subst (x : string) (es : expr) (e : expr) : expr :=
  match e with
  | Var y => if bool_decide (y = x) then es else Var y
  | Val v => Val v
  (* | Rec f xl e =>
    Rec f xl $ if bool_decide (BNamed x ≠ f ∧ BNamed x ∉ xl) then subst x es e else e *)
  | Call e el => Call (subst x es e) (fmap (subst x es) el)
  | InitCall e => InitCall (subst x es e)
  | EndCall e => EndCall (subst x es e)
  | Place l tag T => Place l tag T
  (* | App e1 el => App (subst x es e1) (fmap (subst x es) el) *)
  | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
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
  (* | Field e path => Field (subst x es e) path *)
  | Retag e kind => Retag (subst x es e) kind
  | Let x1 e1 e2 =>
      Let x1 (subst x es e1)
                 (if bool_decide (BNamed x ≠ x1) then subst x es e2 else e2)
  | Case e el => Case (subst x es e) (fmap (subst x es) el)
  (* | Fork e => Fork (subst x es e) *)
  (* | SysCall id => SysCall id *)
  end.

(* formal argument list substitution *)
Definition subst' (mx : binder) (es : expr) : expr → expr :=
  match mx with BNamed x => subst x es | BAnon => id end.

Fixpoint subst_l (xl : list binder) (esl : list expr) (e : expr) : option expr :=
  match xl, esl with
  | [], [] => Some e
  | x::xl, es::esl => subst_l xl esl (subst' x es e)
  | _, _ => None
  end.
Arguments subst_l _%binder _ _%E.

Lemma subst_l_is_Some xl el e :
  length xl = length el → is_Some (subst_l xl el e).
Proof.
  revert el e. induction xl as [|x xl IH] => el e.
  { destruct el; [by eexists|done]. }
  destruct el as [|e1 el]; [done|].
  rewrite /= /subst'. intros ?.
  eapply IH. congruence.
Qed.

Lemma subst_l_is_Some_length xl el e e' :
  subst_l xl el e = Some e' → length xl = length el.
Proof.
  revert e e' el. induction xl as [|x xl IH] => e e' el; [by destruct el|].
  destruct el as [|e1 el]; [done|].
  rewrite /= /subst'. intros Eq. f_equal.
  eapply IH. done.
Qed.

Lemma subst_l_nil_is_Some el e e' :
  subst_l [] el e = Some e' → e' = e.
Proof.
  intros Eq.
  have EqN: el = [].
  { apply nil_length_inv. by rewrite -(subst_l_is_Some_length _ _ _ _ Eq). }
  subst el. simpl in Eq. by simplify_eq.
Qed.

(** Evaluation contexts *)
Inductive ectx_item :=
(* | AppLCtx (el : list expr) *)
(* | AppRCtx (r : result) (rl : list result) (el : list expr) *)
| CallLCtx (el: list expr)
| CallRCtx (r : result) (rl : list result) (el : list expr)
| EndCallCtx
| BinOpLCtx (op : bin_op) (e2 : expr)
| BinOpRCtx (op : bin_op) (r1 : result)
| ProjLCtx (e : expr)
| ProjRCtx (r : result)
| ConcLCtx (e : expr)
| ConcRCtx (r : result)
| CopyCtx
| WriteLCtx (e : expr)
| WriteRCtx (r : result)
| FreeCtx
(* | CasLCtx (e1 e2: expr) *)
(* | CasMCtx (r0 : result) (e2 : expr) *)
(* | CasRCtx (r0 : result) (r1 : result) *)
(* | AtRdCtx *)
(* | AtWrLCtx (e : expr) *)
(* | AtWrRCtx (r : result) *)
| DerefCtx (T: type)
| RefCtx
(* | FieldCtx (path : list nat) *)
| RetagCtx (kind: retag_kind)
| LetCtx (x: binder) (e2: expr)
| CaseCtx (el : list expr).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  (* | AppLCtx el => App e el *)
  (* | AppRCtx r rl el => App (of_result r) ((of_result <$> rl) ++ e :: el) *)
  | CallLCtx el => Call e el
  | CallRCtx r rl el => Call (of_result r) ((of_result <$> rl) ++ e :: el)
  | EndCallCtx => EndCall e
  | BinOpLCtx op e2 => BinOp op e e2
  | BinOpRCtx op r1 => BinOp op (of_result r1) e
  | ProjLCtx e2 => Proj e e2
  | ProjRCtx r1 => Proj (of_result r1) e
  | ConcLCtx e2 => Conc e e2
  | ConcRCtx r1 => Conc (of_result r1) e
  | CopyCtx => Copy e
  | WriteLCtx e2 => Write e e2
  | WriteRCtx r1 => Write (of_result r1) e
  | FreeCtx => Free e
  (* | CasLCtx e1 e2 => CAS e e1 e2 *)
  (* | CasMCtx v0 e2 => CAS (of_result v0) e e2 *)
  (* | CasRCtx v0 v1 => CAS (of_result v0) (of_result v1) e *)
  (* | AtRdCtx => AtomRead e *)
  (* | AtWrLCtx e2 => AtomWrite e e2 *)
  (* | AtWrRCtx v1 => AtomWrite (of_result v1) e *)
  | DerefCtx T => Deref e T
  | RefCtx => Ref e
  (* | FieldCtx path => Field e path *)
  | RetagCtx kind => Retag e kind
  | LetCtx x e2 => Let x e e2
  | CaseCtx el => Case e el
  end.

(** The stepping relation *)
(* Be careful to make sure that poison is always stuck when used for anything
   except for reading from or writing to memory! *)
Definition Z_of_bool (b : bool) : Z :=
  if b then 1 else 0.

Definition sc_of_bool (b : bool) : scalar :=
  ScInt $ Z_of_bool b.

Coercion sc_of_bool : bool >-> scalar.
Coercion ScInt : Z >-> scalar.
Coercion ScFnPtr : fn_id >-> scalar.

Implicit Type (h: mem).

Fixpoint init_mem (l:loc) (n:nat) h : mem :=
  match n with
  | O => h
  | S n => <[l := ☠%S]>(init_mem (l +ₗ 1) n h)
  end.

Fixpoint free_mem (l:loc) (n:nat) h : mem :=
  match n with
  | O => h
  | S n => delete l (free_mem (l +ₗ 1) n h)
  end.

Inductive scalar_eq h : scalar → scalar → Prop :=
(* No refl case for poison *)
| IntRefl z : scalar_eq h (ScInt z) (ScInt z)
| LocRefl l tag1 tag2 : scalar_eq h (ScPtr l tag1) (ScPtr l tag2)
(* Comparing unallocated pointers can non-deterministically say they are equal
   even if they are not.  Given that our `free` actually makes addresses
   re-usable, this may not be strictly necessary, but it is the most
   conservative choice that avoids UB (and we cannot use UB as this operation is
   possible in safe Rust).  See
   <https://internals.rust-lang.org/t/comparing-dangling-pointers/3019> for some
   more background. *)
| LocUnallocL l1 l2 tag1 tag2 :
    h !! l1 = None →
    scalar_eq h (ScPtr l1 tag1) (ScPtr l2 tag2)
| LocUnallocR l1 l2 tag1 tag2 :
    h !! l2 = None →
    scalar_eq h (ScPtr l1 tag1) (ScPtr l2 tag2).

Inductive scalar_neq : scalar → scalar → Prop :=
| IntNeq z1 z2 :
    z1 ≠ z2 → scalar_neq (ScInt z1) (ScInt z2)
| LocNeq l1 l2 tag1 tag2 :
    l1 ≠ l2 → scalar_neq (ScPtr l1 tag1) (ScPtr l2 tag2)
| LocNeqNullR l tag :
    scalar_neq (ScPtr l tag) (ScInt 0)
| LocNeqNullL l tag :
    scalar_neq (ScInt 0) (ScPtr l tag).

Inductive bin_op_eval h : bin_op → scalar → scalar → scalar → Prop :=
| BinOpPlus z1 z2 :
    bin_op_eval h AddOp (ScInt z1) (ScInt z2) (ScInt (z1 + z2))
| BinOpMinus z1 z2 :
    bin_op_eval h SubOp (ScInt z1) (ScInt z2) (ScInt (z1 - z2))
| BinOpLe z1 z2 :
    bin_op_eval h LeOp (ScInt z1) (ScInt z2) (sc_of_bool $ bool_decide (z1 ≤ z2))
| BinOpLt z1 z2 :
    bin_op_eval h LtOp (ScInt z1) (ScInt z2) (sc_of_bool $ bool_decide (z1 < z2))
| BinOpEqTrue l1 l2 :
    scalar_eq h l1 l2 → bin_op_eval h EqOp l1 l2 (sc_of_bool true)
| BinOpEqFalse l1 l2 :
    scalar_neq l1 l2 → bin_op_eval h EqOp l1 l2 (sc_of_bool false)
| BinOpOffset l z tag :
    bin_op_eval h OffsetOp (ScPtr l tag) (ScInt z) (ScPtr (l +ₗ z) tag).

(* Compute subtype of `T` and offset to it from `path` *)
Fixpoint field_access (T: type) (path : list nat) :
  option (nat * type) :=
  match path with
  | [] => Some (O, T)
  | i :: path =>
    match T with
    | FixedSize sz =>
        if bool_decide (i ≤ sz) then Some (i, FixedSize (sz - i)) else None
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

Fixpoint write_mem l (v: value) h: mem :=
  match v with
  | [] => h
  | s :: v => write_mem (l +ₗ 1) v (<[l := s]> h)
  end.

Equations read_mem (l: loc) (n: nat) h: option value :=
  read_mem l n h := go l n (Some [])
  where go : loc → nat → option value → option value :=
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

Lemma fresh_block_equiv (h1 h2: mem) :
  dom (gset loc) h1 ≡ dom (gset loc) h2 → fresh_block h1 = fresh_block h2.
Proof.
  intros EqD. apply elements_proper in EqD.
  rewrite /fresh_block. apply (fresh_proper (C:= gset _)).
  apply foldr_permutation; [apply _..|set_solver|done].
Qed.

Inductive pure_expr_step (FNs: fn_env) (h: mem) : expr → event → expr → Prop :=
| BinOpPS op (l1 l2 l': scalar) :
    bin_op_eval h op l1 l2 l' →
    pure_expr_step FNs h (BinOp op #[l1] #[l2]) SilentEvt #[l']
(* TODO: add more operations for values *)
| ProjBS (i: Z) (v : value) (s : scalar)
    (DEFINED: 0 ≤ i ∧ v !! (Z.to_nat i) = Some s) :
    pure_expr_step FNs h (Proj (Val v) #[i]) SilentEvt #[s]
| ConcBS v1 v2 :
    pure_expr_step FNs h (Conc (Val v1) (Val v2))
                         SilentEvt (Val (v1 ++ v2))
| RefBS l lbor T :
    is_Some (h !! l) →
    pure_expr_step FNs h (Ref (Place l lbor T)) SilentEvt #[ScPtr l lbor]
| DerefBS l lbor T
    (DEFINED: ∀ (i: nat), (i < tsize T)%nat → l +ₗ i ∈ dom (gset loc) h) :
    pure_expr_step FNs h (Deref #[ScPtr l lbor] T) SilentEvt (Place l lbor T)
(* | FieldBS l lbor T path off T'
    (FIELD: field_access T path = Some (off, T')) :
    pure_expr_step FNs h (Field (Place l lbor T) path)
                         SilentEvt (Place (l +ₗ off) lbor T') *)
| LetBS x e1 e2 e' :
    is_Some (to_result e1) →
    subst' x e1 e2 = e' →
    pure_expr_step FNs h (let: x := e1 in e2) SilentEvt e'
| CaseBS i el e :
    0 ≤ i →
    el !! (Z.to_nat i) = Some e →
    pure_expr_step FNs h (case: #[i] of el) SilentEvt e
| CallBS fid el xl e HC e':
    FNs !! fid = Some (@FunV xl e HC) →
    Forall (λ ei, is_Some (to_value ei)) el →
    subst_l xl el e = Some e' →
    pure_expr_step FNs h (Call #[ScFnPtr fid] el)
                         (NewCallEvt fid) (EndCall (InitCall e')).


Inductive mem_expr_step (h: mem) : expr → event → mem → expr → Prop :=
| InitCallBS e (c: call_id):
    mem_expr_step
              h (InitCall e)
              (InitCallEvt c)
              h e
| EndCallBS (call: call_id) e v :
    to_result e = Some (ValR v) →
    mem_expr_step h (EndCall e) (EndCallEvt call v) h #v
| CopyBS l lbor T (v: value)
    (READ: read_mem l (tsize T) h = Some v)
    (* (LEN: length v = tsize T) : true by read_mem_values *)
    (* (VALUES: ∀ (i: nat), (i < length v)%nat → h !! (l +ₗ i) = v !! i)
        : true by read_mem_values *) :
    mem_expr_step
              h (Copy (Place l lbor T))
              (CopyEvt l lbor T v)
              h (Val v)
| WriteBS l lbor T v (LEN: length v = tsize T)
    (DEFINED: ∀ (i: nat), (i < length v)%nat → l +ₗ i ∈ dom (gset loc) h) :
    mem_expr_step
              h (Place l lbor T <- Val v)
              (WriteEvt l lbor T v)
              (write_mem l v h) #[☠]
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
              (free_mem l (tsize T) h) #[☠]
| RetagBS x xbor T kind :
    mem_expr_step
              h (Retag (Place x xbor T) kind)
              (RetagEvt x T kind)
              h #[☠]
(* | ForkBS e h:
    expr_step (Fork e) h SilentEvt (Lit LitPoison) h [e] *)
(* observable behavior *)
(* | SysCallBS id h:
    expr_step (SysCall id) h (SysCallEvt id) (Lit LitPoison) h [] *)
.
