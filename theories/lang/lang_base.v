From Coq Require Export ssreflect.
From stdpp Require Export countable binders gmap.

Global Open Scope general_if_scope.
Ltac done := stdpp.tactics.done.

From stbor.lang Require Export type.

Set Default Proof Using "Type".

Delimit Scope loc_scope with L.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.
Delimit Scope sc_scope with S.
Delimit Scope result_scope with R.

Open Scope Z_scope.

(** Locations *)
Definition block : Set := positive.
Definition loc : Set := block * Z.

Bind Scope loc_scope with loc.
Open Scope loc_scope.

Definition shift_loc (l : loc) (z : Z) : loc := (l.1, l.2 + z).

Notation "l +ₗ z" := (shift_loc l%L z%Z)
  (at level 50, left associativity) : loc_scope.

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

(** Tags for pointers *)
Notation ptr_id := nat (only parsing).

Inductive tag :=
  | Tagged (t: ptr_id)
  | Untagged
  .

Instance tag_eq_dec : EqDecision tag.
Proof. solve_decision. Defined.
Instance tag_countable : Countable tag.
Proof.
  refine (inj_countable
          (λ tg, match tg with
              | Tagged t => inl t
              | Untagged => inr ()
              end)
          (λ s, match s with
              | inl t => Some $ Tagged t
              | inr _ => Some $ Untagged
              end) _); by intros [].
Qed.

Inductive permission := Unique | SharedReadWrite.
Instance permission_eq_dec : EqDecision permission.
Proof. solve_decision. Defined.
Instance permission_countable : Countable permission.
Proof.
  refine (inj_countable
    (λ p,
      match p with
      | Unique => 0 | SharedReadWrite => 1
      end)
    (λ s,
      match s with
      | 0 => Some Unique | _ => Some SharedReadWrite
      end) _); by intros [].
Qed.

(** Stacks of borrows. *)
Record item := mkItem {
  perm      : permission;
  tg        : tag;
}.
Instance item_eq_dec : EqDecision item.
Proof. solve_decision. Defined.

Definition stack := list item.
Definition stacks := gmap loc stack.

(** Retag kinds *)
Inductive retag_kind := FnEntry | TwoPhase | RawRt | Default.

Definition is_two_phase (kind: retag_kind) : bool :=
  match kind with TwoPhase => true | _ => false end.

(** Language base constructs -------------------------------------------------*)

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
Notation fn_id := string (only parsing).
Inductive scalar :=
  ScPoison | ScInt (n: Z) | ScPtr (l: loc) (tg: tag) | ScFnPtr (fid: fn_id).
Bind Scope sc_scope with scalar.
Definition value := list scalar.
Bind Scope val_scope with value.

(** Expressions *)
Inductive expr :=
(* base values *)
| Val (v: value)
(* variables *)
| Var (x : string)
(* | App (e : expr) (el: list expr) *)
(* | Rec (f : binder) (xl : list binder) (e : expr) *)
(* function calls *)
| Call (e: expr) (el: list expr)  (* Call a function through a FnPtr `e` with
                                     arguments `el` *)
| InitCall (e: expr)              (* Initializing a stack frame for e *)
| EndCall (e: expr)               (* End the current call with value `e` *)
(* operations on value *)
| Proj (e1 e2 : expr)             (* Projection out sub value *)
| Conc (e1 e2: expr)
(* bin op *)
| BinOp (op : bin_op) (e1 e2 : expr)
(* place operation *)
| Place (l: loc) (tg: tag) (T: type)
                                  (* A place is a tagged pointer: every access
                                     to memory revolves around a place. *)
| Deref (e: expr) (T: type)       (* Deference a pointer `e` into a place
                                     presenting the location that `e` points to.
                                     The location has type `T`. *)
| Ref (e: expr)                   (* Turn a place `e` into a pointer value. *)
(* | Field (e: expr) (path: list nat)(* Create a place that points to a component
                                     of the place `e`. `path` defines the path
                                     through the type. *) *)
(* mem op *)
| Copy (e : expr)                 (* Read from the place `e` *)
| Write (e1 e2: expr)             (* Write the value `e2` to the place `e1` *)
| Alloc (T: type)                 (* Allocate a place of type `T` *)
| Free (e : expr)                 (* Free the place `e` *)
(* atomic mem op *)
(* | CAS (e0 e1 e2 : expr) *)     (* CAS the value `e2` for `e1` to the place `e0` *)
(* | AtomWrite (e1 e2: expr) *)
(* | AtomRead (e: expr) *)
(* retag *) (* Retag the memory pointed to by `e` of type (Reference pk T) with
  retag kind `kind`. *)
| Retag (e : expr) (pk: pointer_kind) (T: type) (kind: retag_kind)
(* let binding *)
| Let (x : binder) (e1 e2: expr)
(* case *)
| Case (e : expr) (el: list expr)
(* concurrency *)
(* | Fork (e : expr) *)
(* observable behavior *)
(* | SysCall (id: nat) *)
.

Bind Scope expr_scope with expr.

Arguments Val _%E.
(* Arguments App _%E _%E. *)
Arguments BinOp _ _%E _%E.
Arguments Call _%E _%E.
Arguments InitCall _%E.
Arguments EndCall _%E.
Arguments Proj _%E _%E.
Arguments Conc _%E _%E.
Arguments Deref _%E _%T.
Arguments Ref _%E.
(* Arguments Field _%E _. *)
Arguments Copy _%E.
Arguments Write _%E _%E.
Arguments Alloc _%T.
Arguments Free _%E.
(* Arguments CAS _%E _%E _%E. *)
(* Arguments AtomWrite _%E _%E. *)
(* Arguments AtomRead _%E. *)
Arguments Retag _%E _ _ _.
Arguments Let _%binder _%E _%E.
Arguments Case _%E _%E.
(* Arguments Fork _%E. *)

(** Closedness *)
Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Val _ | Place _ _ _ | Alloc _ (* | SysCall _ *) => true
  | Var x => bool_decide (x ∈ X)
  (* | Rec f xl e => is_closed (f :b: xl +b+ X) e *)
  | BinOp _ e1 e2 | (* AtomWrite e1 e2 | *) Write e1 e2
      | Conc e1 e2 | Proj e1 e2 => is_closed X e1 && is_closed X e2
  | Let x e1 e2 => is_closed X e1 && is_closed (x :b: X) e2
  | Case e el | Call e el (* | App e el  *)
      => is_closed X e && forallb (is_closed X) el
  | Copy e | Retag e _ _ _ | Deref e _ | Ref e (* | Field e _ *)
      | Free e | InitCall e | EndCall e (* | AtomRead e | Fork e *)
      => is_closed X e
  (* | CAS e0 e1 e2 => is_closed X e0 && is_closed X e1 && is_closed X e2 *)
  end.

Class Closed (X : list string) (e : expr) := closed : is_closed X e.
Instance closed_proof_irrel env e : ProofIrrel (Closed env e).
Proof. rewrite /Closed. apply _. Qed.
Instance closed_decision env e : Decision (Closed env e).
Proof. rewrite /Closed. apply _. Qed.

(** Irreducible (language values) *)
Inductive result :=
| ValR (v : value)
| PlaceR (l: loc) (tg: tag) (T: type)
.
Bind Scope result_scope with result.

Definition of_result (v : result) : expr :=
  match v with
  | ValR v => Val v
  | PlaceR l tag T => Place l tag T
  end.

Definition to_result (e : expr) : option result :=
  match e with
  | Val v => Some (ValR v)
  | Place l T tag => Some (PlaceR l T tag)
  | _ => None
  end.

Definition to_value (e: expr) : option value :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Lemma is_Some_to_value_result (e: expr):
  is_Some (to_value e) → is_Some (to_result e).
Proof. destruct e; simpl; intros []; naive_solver. Qed.

Lemma Val_to_value e v : to_value e = Some v → Val v = e.
Proof. destruct e; try discriminate. intros [= ->]. done. Qed.

Lemma list_Forall_to_value (es: list expr):
  Forall (λ ei, is_Some (to_value ei)) es ↔ (∃ vs, es = Val <$> vs).
Proof.
  induction es; split.
  - intros _. exists []. done.
  - intros _. constructor.
  - intros [[v EQv] [vs EQvs]%IHes]%Forall_cons. exists (v::vs).
    simpl. f_equal; last done.
    erewrite Val_to_value; done.
  - intros [[|v vs] EQ]; first discriminate.
    move:EQ=> [= -> EQ]. constructor; first by eauto.
    apply IHes. eexists. done.
Qed.

(** Global static function table *)
Record function := FunV {
  fun_args: list binder;
  fun_body: expr;
  fun_closed: Closed (fun_args +b+ []) fun_body
}.
Arguments FunV _ _ {_}.
Definition fn_env := gmap fn_id function.

(** Main state: a heap of scalars. *)
Definition mem := gmap loc scalar.

(** Internal events *)
Inductive event :=
| AllocEvt (l : loc) (lbor: tag) (T: type)
| DeallocEvt (l: loc) (lbor: tag) (T: type)
| CopyEvt (l: loc) (lbor: tag) (T: type) (v: value)
| WriteEvt (l: loc) (lbor: tag) (T: type) (v: value)
| RetagEvt (l: loc) (otag ntag: tag) (pk: pointer_kind) (T: type) (kind: retag_kind)
(* | SysCallEvt (id: nat) *)
| SilentEvt
.
