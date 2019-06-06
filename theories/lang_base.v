From Coq Require Export ssreflect.
From stdpp Require Export countable binders gmap.

Global Open Scope general_if_scope.

From stbor Require Export type.
Set Default Proof Using "Type".

Delimit Scope loc_scope with L.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

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

(** Protector tracker: track if a call_id is active,
  i.e. the call is still in the call stack *)
Notation call_id := nat (only parsing).
Definition protectors := gmap call_id bool.

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

Inductive permission := Unique | SharedReadWrite | SharedReadOnly | Disabled.
Instance permission_eq_dec : EqDecision permission.
Proof. solve_decision. Defined.
Instance permission_countable : Countable permission.
Proof.
  refine (inj_countable
    (λ p,
      match p with
      | Unique => 0 | SharedReadWrite => 1 | SharedReadOnly => 2 | Disabled => 3
      end)
    (λ s,
      match s with
      | 0 => Some Unique | 1 => Some SharedReadWrite | 2 => Some SharedReadOnly
      | _ => Some Disabled
      end) _); by intros [].
Qed.

(** Stacks of borrows. *)
Record item := mkItem {
  perm      : permission;
  tg        : tag;
  protector : option call_id;
}.
Instance item_eq_dec : EqDecision item.
Proof. solve_decision. Defined.

Definition stack := list item.
Definition stacks := gmap loc stack.

(** Retag kinds *)
Inductive retag_kind := FnEntry (c: call_id) | TwoPhase | RawRt | Default.

Definition is_two_phase (kind: retag_kind) : bool :=
  match kind with TwoPhase => true | _ => false end.
Definition adding_protector (kind: retag_kind) : option call_id :=
  match kind with FnEntry c => Some c | _ => None end.

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
Inductive lit :=
  | LitPoison | LitLoc (l: loc) (tg: tag) | LitInt (n : Z)
  | LitFnPtr (name: string)
  | LitCall (id: call_id).

(** Expressions *)
Inductive expr :=
(* base values *)
| Lit (l: lit)
(* variables *)
| Var (x : string)
(* | App (e : expr) (el: list expr) *)
(* | Rec (f : binder) (xl : list binder) (e : expr) *)
(* function calls *)
| Call (e: expr) (el: list expr) (* Call a function through a FnPtr `e`
                                    with arguments `el` *)
(* function call tracking *)
| EndCall (e: expr)               (* End the call with id `e` *)
(* temp values *)
| TVal (el: list expr)
| Proj (e1 e2 : expr)
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
| Field (e: expr) (path: list nat)(* Create a place that points to a component
                                     of the place `e`. `path` defines the path
                                     through the type. *)
(* mem op *)
| Copy (e : expr)                 (* Read from the place `e` *)
| Write (e1 e2: expr)             (* Write the value `e2` to the place `e1` *)
| Alloc (T: type)                 (* Allocate a place of type `T` *)
| Free (e : expr)                 (* Free the place `e` *)
(* atomic mem op *)
(* | CAS (e0 e1 e2 : expr) *)     (* CAS the value `e2` for `e1` to the place `e0` *)
(* | AtomWrite (e1 e2: expr) *)
(* | AtomRead (e: expr) *)
(* retag *)
| Retag (e : expr) (kind: retag_kind) (call_id: expr)
                                  (* Retag the place `e` with retag kind `kind`. *)
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

(* Arguments App _%E _%E. *)
Arguments BinOp _ _%E _%E.
Arguments Call _%E _%E.
Arguments EndCall _%E.
Arguments TVal _%E.
Arguments Proj _%E _%E.
Arguments Conc _%E _%E.
Arguments Deref _%E _%T.
Arguments Ref _%E.
Arguments Field _%E _.
Arguments Copy _%E.
Arguments Write _%E _%E.
Arguments Alloc _%T.
Arguments Free _%E.
(* Arguments CAS _%E _%E _%E. *)
(* Arguments AtomWrite _%E _%E. *)
(* Arguments AtomRead _%E. *)
Arguments Retag _%E _ _%E.
Arguments Let _%binder _%E _%E.
Arguments Case _%E _%E.
(* Arguments Fork _%E. *)

(** Closedness *)
Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Lit _ | Place _ _ _ | Alloc _ (* | SysCall _ *) => true
  | Var x => bool_decide (x ∈ X)
  (* | Rec f xl e => is_closed (f :b: xl +b+ X) e *)
  | BinOp _ e1 e2 | (* AtomWrite e1 e2 | *) Write e1 e2 | Retag e1 _ e2
      | Conc e1 e2 | Proj e1 e2 => is_closed X e1 && is_closed X e2
  | TVal el => forallb (is_closed X) el
  | Let x e1 e2 => is_closed X e1 && is_closed (x :b: X) e2
  | Case e el | Call e el (* | App e el  *) => is_closed X e && forallb (is_closed X) el
  | Copy e | Deref e _ | Ref e | Field e _
      | Free e | EndCall e (* | AtomRead e | Fork e *) => is_closed X e
  (* | CAS e0 e1 e2 => is_closed X e0 && is_closed X e1 && is_closed X e2 *)
  end.

Class Closed (X : list string) (e : expr) := closed : is_closed X e.
Instance closed_proof_irrel env e : ProofIrrel (Closed env e).
Proof. rewrite /Closed. apply _. Qed.
Instance closed_decision env e : Decision (Closed env e).
Proof. rewrite /Closed. apply _. Qed.

(** Irreducible (language values) *)
Inductive val :=
| LitV (v : lit)
| TValV (vl : list lit)
| PlaceV (l: loc) (tg: tag) (T: type)
.
Bind Scope val_scope with val.

Definition of_val (v : val) : expr :=
  match v with
  | LitV v => Lit v
  | TValV vl => TVal (Lit <$> vl)
  | PlaceV l tag T => Place l tag T
  end.

Definition to_lit (e: expr): option lit :=
  match e with
  | Lit l => Some l
  | _ => None
  end.
Definition to_lits (vl : list lit) (el: list expr) : option (list lit) :=
  foldl (λ acc e, vl ← acc; v ← to_lit e; Some (vl ++ [v])) (Some vl) el.
Definition to_val (e : expr) : option val :=
  match e with
  | Lit v => Some (LitV v)
  | Place l T tag => Some (PlaceV l T tag)
  | TVal el => vl ← to_lits [] el; Some (TValV vl)
  | _ => None
  end.

(** Global static function table *)
Inductive function :=
| FunV (xl : list binder) (e : expr) `{Closed (xl +b+ []) e}.
Definition fn_env := gmap string function.

(** Main state: a heap of literals. *)
Definition mem := gmap loc lit.

(** Internal memory events *)
Inductive mem_event :=
| AllocEvt (l : loc) (lbor: tag) (T: type)
| DeallocEvt (l: loc) (lbor: tag) (T: type)
| CopyEvt (l: loc) (lbor: tag) (T: type) (vl: list lit)
| WriteEvt (l: loc) (lbor: tag) (T: type) (vl: list lit)
| NewCallEvt (name: string) (call: call_id)
| EndCallEvt (call: call_id)
| RetagEvt (x: loc) (T: type) (kind: retag_kind)
(* | SysCallEvt (id: nat) *)
| SilentEvt
.
