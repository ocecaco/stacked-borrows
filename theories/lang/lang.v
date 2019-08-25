From iris.program_logic Require Export language ectx_language ectxi_language.

From stbor.lang Require Export expr_semantics bor_semantics.

Set Default Proof Using "Type".

Module bor_lang.

(** COMBINED SEMANTICS -------------------------------------------------------*)

Record state := mkState {
  (* Heap of scalars *)
  shp : mem;
  (* Stacked borrows for the heap *)
  sst : stacks;
  (* Stack of active call ids *)
  scs : call_id_stack;
  (* Counter for pointer tag generation *)
  snp : ptr_id;
  (* Counter for call id generation *)
  snc : call_id;
}.

Record config := mkConfig {
  (* Static global function table *)
  cfn : fn_env;
  (* Shared state *)
  cst : state;
}.

Implicit Type (σ: state).

(** BASIC LANGUAGE PROPERTIES ------------------------------------------------*)
(** Closed expressions *)

Lemma is_closed_subst X e x es : is_closed X e → x ∉ X → subst x es e = e.
Proof.
  revert e X. fix FIX 1; destruct e=> X /=; rewrite ?bool_decide_spec ?andb_True=> He ?;
    repeat case_bool_decide; simplify_eq/=; f_equal;
    try by intuition eauto with set_solver.
  - case He=> _. clear He. induction el=>//=. rewrite andb_True=>?.
    f_equal; intuition eauto with set_solver.
  - move : He. induction el=>//=. rewrite andb_True=>?.
    f_equal; intuition eauto with set_solver.
Qed.

Lemma is_closed_nil_subst e x es : is_closed [] e → subst x es e = e.
Proof. intros. apply is_closed_subst with []; set_solver. Qed.

Lemma is_closed_of_result X v : is_closed X (of_result v).
Proof. by destruct v as [[]|]. Qed.

Lemma to_of_result v : to_result (of_result v) = Some v.
Proof. by destruct v as [[]|]. Qed.
Lemma of_to_result e v : to_result e = Some v → of_result v = e.
Proof. destruct e=>//=; intros; by simplify_eq. Qed.
Instance of_result_inj : Inj (=) (=) of_result.
Proof. by intros ?? Hv; apply (inj Some); rewrite -2!to_of_result Hv /=. Qed.
Lemma is_closed_to_result X e v : to_result e = Some v → is_closed X e.
Proof. intros <-%of_to_result. apply is_closed_of_result. Qed.

Lemma list_Forall_to_of_result vl :
  Forall (λ ei, is_Some (to_result ei)) (of_result <$> vl).
Proof.
  apply Forall_forall. move => e /elem_of_list_fmap [? [-> ?]].
  rewrite to_of_result. by eexists.
Qed.

Lemma of_result_list_expr (vl: list value) :
  (of_result <$> (ValR <$> vl)) = Val <$> vl.
Proof. induction vl as [|v vl IH]; [done|]. by rewrite 3!fmap_cons IH. Qed.

(* Lemma subst_is_closed X x es e :
  is_closed X es → is_closed (x::X) e → is_closed X (subst x es e).
Proof.
  revert e X. fix FIX 1; destruct e=>X //=; repeat (case_bool_decide=>//=);
    try naive_solver; rewrite ?andb_True; intros.
  - set_solver.
  - split; first naive_solver. induction el; naive_solver.
  - (* eauto using is_closed_weaken with set_solver. *)
  - eapply is_closed_weaken; first done.
    destruct (decide (BNamed x = f)), (decide (BNamed x ∈ xl)); set_solver.
  - induction el; naive_solver.
  - split; first naive_solver. induction el; naive_solver.
Qed.

Lemma subst'_is_closed X b es e :
  is_closed X es → is_closed (b:b:X) e → is_closed X (subst' b es e).
Proof. destruct b; first done. apply subst_is_closed. Qed.
 *)

(** Equality and other typeclass stuff *)

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

Instance scalar_eq_dec : EqDecision scalar.
Proof. solve_decision. Defined.
Instance scalar_countable : Countable scalar.
Proof.
  refine (inj_countable
          (λ v, match v with
              | ScPoison => inl (inl ())
              | ScPtr l bor => inl (inr (l,bor))
              | ScInt n => inr (inl n)
              | ScFnPtr n => inr (inr n)
              end)
          (λ s, match s with
              | inl (inl ()) => Some ScPoison
              | inl (inr (l,bor)) => Some $ ScPtr l bor
              | inr (inl n) => Some $ ScInt n
              | inr (inr n) => Some $ ScFnPtr n
              end) _); by intros [].
Qed.

Instance retag_kind_eq_dec : EqDecision retag_kind.
Proof. solve_decision. Defined.
Instance retag_kind_countable : Countable retag_kind.
Proof.
  refine (inj_countable
          (λ k, match k with
              | FnEntry => inl $ inl ()
              | TwoPhase => inl $ inr ()
              | RawRt => inr $ inl ()
              | Default => inr $ inr ()
              end)
          (λ s, match s with
              | inl (inl _) => Some $ FnEntry
              | inl (inr _) => Some TwoPhase
              | inr (inl _) => Some RawRt
              | inr (inr _) => Some Default
              end) _); by intros [].
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
  | Val v, Val v' => bool_decide (v = v')
  | Var x, Var x' => bool_decide (x = x')
  | Case e el, Case e' el' | Call e el, Call e' el'
    (* | App e el, App e' el' *) => expr_beq e e' && expr_list_beq el el'
  (* | Rec f xl e, Rec f' xl' e' =>
      bool_decide (f = f') && bool_decide (xl = xl') && expr_beq e e' *)
  | BinOp op e1 e2, BinOp op' e1' e2' =>
      bool_decide (op = op') && expr_beq e1 e1' && expr_beq e2 e2'
  | Place l bor T , Place l' bor' T' =>
      bool_decide (l = l') && bool_decide (bor = bor') && bool_decide (T = T')
  | Deref e T, Deref e' T' =>
      bool_decide (T = T') && expr_beq e e'
  | Retag e pk T kind, Retag e' pk' T' kind' =>
     bool_decide (pk = pk') && bool_decide (T = T') &&
     bool_decide (kind = kind') && expr_beq e e'
  | Copy e, Copy e' | Ref e, Ref e' | InitCall e, InitCall e'
  (* | AtomRead e, AtomRead e' *) | EndCall e, EndCall e' => expr_beq e e'
  | Let x e1 e2, Let x' e1' e2' =>
    bool_decide (x = x') && expr_beq e1 e1' && expr_beq e2 e2'
  | Proj e1 e2, Proj e1' e2' | Conc e1 e2, Conc e1' e2'
    | Write e1 e2, Write e1' e2' (* | AtomWrite e1 e2, AtomWrite e1' e2' *) =>
      expr_beq e1 e1' && expr_beq e2 e2'
  (* | Field e path, Field e' path' => expr_beq e e' && bool_decide (path = path') *)
  (* | CAS e0 e1 e2, CAS e0' e1' e2' =>
      expr_beq e0 e0' && expr_beq e1 e1' && expr_beq e2 e2' *)
  (* | Fork e, Fork e' => expr_beq e e' *)
  | Alloc T, Alloc T' => bool_decide (T = T')
  | Free e, Free e' => expr_beq e e'
  (* | SysCall id, SysCall id' => bool_decide (id = id') *)
  | _, _ => false
  end.

Lemma expr_beq_correct (e1 e2 : expr) : expr_beq e1 e2 ↔ e1 = e2.
Proof.
  revert e1 e2; fix FIX 1;
    destruct e1 as [| |? el1| | | | | | | | | | (* | *) | | | | |? el1],
             e2 as [| |? el2| | | | | | | | | | (* | *) | | | | |? el2];
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
      | Val v => GenNode 1 [GenLeaf $ inl $ inl $ inl $ inr v]
      (* | Rec f xl e => GenNode 2 [GenLeaf $ inl $ inl $ inr $ inl f;
                                 GenLeaf $ inl $ inl $ inr $ inr xl; go e]
      | App e el => GenNode 3 (go e :: (go <$> el)) *)
      | Call e el => GenNode 2 (go e :: (go <$> el))
      | InitCall e => GenNode 3 [go e]
      | EndCall e => GenNode 4 [go e]
      | BinOp op e1 e2 => GenNode 5 [GenLeaf $ inl $ inl $ inr $ inl op;
                                     go e1; go e2]
      | Proj e1 e2 => GenNode 6 [go e1; go e2]
      | Conc e1 e2 => GenNode 7 [go e1; go e2]
      | Place l tag T => GenNode 8 [GenLeaf $ inl $ inl $ inr $ inr l;
                                    GenLeaf $ inl $ inr $ inl $ inl tag;
                                    GenLeaf $ inl $ inr $ inl $ inr T]
      | Copy e => GenNode 9 [go e]
      | Write e1 e2 => GenNode 10 [go e1; go e2]
      | Free e => GenNode 11 [go e]
      | Alloc T => GenNode 12 [GenLeaf $ inl $ inr $ inr $ inl T]
      | Deref e T => GenNode 13 [GenLeaf $ inl $ inr $ inr $ inr T; go e]
      | Ref e => GenNode 14 [go e]
      (* | Field e path => GenNode 15 [GenLeaf $ inr $ inl $ inl (* $ inl *) path; go e] *)
      | Retag e pk T kind =>
          GenNode 15 [GenLeaf $ inr $ inl $ inl pk;
                      GenLeaf $ inr $ inl $ inr T;
                      GenLeaf $ inr $ inr $ inl kind; go e]
      | Let x e1 e2 => GenNode 16 [GenLeaf$ inr $ inr $ inr x; go e1; go e2]
      | Case e el => GenNode 17 (go e :: (go <$> el))
      (* | Fork e => GenNode 23 [go e]
      | SysCall id => GenNode 24 [GenLeaf $ inr $ inr id] *)
     end)
    (fix go s := match s with
     | GenNode 0 [GenLeaf (inl (inl (inl (inl x))))] => Var x
     | GenNode 1 [GenLeaf (inl (inl (inl (inr v))))] => Val v
     | GenNode 2 (e :: el) => Call (go e) (go <$> el)
     | GenNode 3 [e] => InitCall (go e)
     | GenNode 4 [e] => EndCall (go e)
     (* | GenNode 2 [GenLeaf (inl (inl (inr (inl f))));
                  GenLeaf (inl (inl (inr (inr xl)))); e] => Rec f xl (go e)
     | GenNode 3 (e :: el) => App (go e) (go <$> el) *)
     | GenNode 5 [GenLeaf (inl (inl (inr (inl op)))); e1; e2] => BinOp op (go e1) (go e2)
     | GenNode 6 [e1; e2] => Proj (go e1) (go e2)
     | GenNode 7 [e1; e2] => Conc (go e1) (go e2)
     | GenNode 8 [GenLeaf (inl (inl (inr (inr l))));
                  GenLeaf (inl (inr (inl (inl tag))));
                  GenLeaf (inl (inr (inl (inr T))))] => Place l tag T
     | GenNode 9 [e] => Copy (go e)
     | GenNode 10 [e1; e2] => Write (go e1) (go e2)
     | GenNode 11 [e] => Free (go e)
     | GenNode 12 [GenLeaf (inl (inr (inr (inl T))))] => Alloc T
     | GenNode 13 [GenLeaf (inl (inr (inr (inr T)))); e] => Deref (go e) T
     | GenNode 14 [e] => Ref (go e)
     (* | GenNode 15 [GenLeaf (inr (inl (inl (*  (inl *) path(* ) *)))); e] => Field (go e) path *)
     | GenNode 15 [GenLeaf (inr (inl (inl pk)));
                   GenLeaf (inr (inl (inr T)));
                   GenLeaf (inr (inr (inl kind))); e] =>
        Retag (go e) pk T kind
     | GenNode 16 [GenLeaf (inr (inr (inr x))); e1; e2] => Let x (go e1) (go e2)
     | GenNode 17 (e :: el) => Case (go e) (go <$> el)
     (* | GenNode 23 [e] => Fork (go e)
     | GenNode 24 [GenLeaf (inr (inr id))] => SysCall id *)
     | _ => (#[☠])%E
     end) _).
  fix FIX 1. intros []; f_equal=>//; revert el; clear -FIX.
  - fix FIX_INNER 1. intros []; [done|]. by simpl; f_equal.
  - fix FIX_INNER 1. intros []; [done|]. by simpl; f_equal.
Qed.

Instance result_dec_eq : EqDecision result.
Proof.
  refine (λ v1 v2, cast_if (decide (of_result v1 = of_result v2))); abstract naive_solver.
Defined.
Instance result_countable : Countable result.
Proof.
  refine (inj_countable
    (λ v, match v with
          | ValR v => inl v
          | PlaceR l bor T => inr (l, bor, T)
          end)
    (λ x, match x with
          | inl v => Some $ ValR $ v
          | inr (l, bor, T) => Some $ PlaceR l bor T
          end) _).
  by intros [].
Qed.

Instance scalar_inhabited : Inhabited scalar := populate ScPoison.
Instance expr_inhabited : Inhabited expr := populate (#[☠])%E.
Instance result_inhabited : Inhabited result := populate (ValR [☠]%S).
Instance state_Inhabited : Inhabited state.
Proof. do 2!econstructor; exact: inhabitant. Qed.

Canonical Structure locO := leibnizO loc.
Canonical Structure scalarO := leibnizO scalar.
Canonical Structure resultO := leibnizO result.
Canonical Structure exprO := leibnizO expr.
Canonical Structure stateO := leibnizO state.

(** Basic properties about the language *)

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_result Ki e :
  is_Some (to_result (fill_item Ki e)) → is_Some (to_result e).
Proof. intros [r ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_result Ki e :
  to_result e = None → to_result (fill_item Ki e) = None.
Proof. intros EqN. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma list_expr_result_eq_inv rl1 rl2 e1 e2 el1 el2 :
  to_result e1 = None → to_result e2 = None →
  fmap of_result rl1 ++ e1 :: el1 = fmap of_result rl2 ++ e2 :: el2 →
  rl1 = rl2 ∧ el1 = el2.
Proof.
  revert rl2; induction rl1; destruct rl2; intros H1 H2; inversion 1.
  - done.
  - subst. by rewrite to_of_result in H1.
  - subst. by rewrite to_of_result in H2.
  - destruct (IHrl1 rl2); auto. split; f_equal; auto. by apply (inj of_result).
Qed.

Lemma fill_item_no_result_inj Ki1 Ki2 e1 e2 :
  to_result e1 = None → to_result e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1 as [|v1 vl1 el1| | | | | | | | | | | (* | *) | | | | |],
           Ki2 as [|v2 vl2 el2| | | | | | | | | | | (* | *) | | | | |];
  intros He1 He2 EQ; try discriminate; simplify_eq/=;
    repeat match goal with
    | H : to_result (of_result _) = None |- _ => by rewrite to_of_result in H
    end; auto;
  destruct (list_expr_result_eq_inv vl1 vl2 e1 e2 el1 el2); auto; congruence.
Qed.

Section head_step.

Variable (fns: fn_env).

Inductive head_step :
  expr → state → list event → expr → state → list expr → Prop :=
  | HeadPureS σ e e' ev
      (ExprStep: pure_expr_step fns σ.(shp) e ev e')
    : head_step e σ [ev] e' σ []
  | HeadImpureS σ e e' ev h' α' cids' nxtp' nxtc'
      (ExprStep : mem_expr_step σ.(shp) e ev h' e')
      (InstrStep: bor_step h' σ.(sst) σ.(scs) σ.(snp) σ.(snc)
                           ev α' cids' nxtp' nxtc')
    : head_step e σ [ev] e' (mkState h' α' cids' nxtp' nxtc') [].

Lemma result_head_stuck e1 σ1 κ e2 σ2 efs :
  head_step e1 σ1 κ e2 σ2 efs → to_result e1 = None.
Proof. destruct 1; inversion ExprStep; naive_solver. Qed.

Lemma head_ctx_step_result Ki e σ1 κ e2 σ2 efs :
  head_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_result e).
Proof.
  destruct Ki; inversion_clear 1; inversion_clear ExprStep;
    simplify_option_eq; eauto.
  eapply (Forall_forall (λ ei, is_Some (to_result ei))).
  - eapply Forall_impl; eauto. by apply is_Some_to_value_result.
  - set_solver.
Qed.

Lemma bor_lang_mixin : EctxiLanguageMixin of_result to_result fill_item head_step.
Proof.
  split; apply _ || eauto using to_of_result, of_to_result, result_head_stuck,
    fill_item_result, fill_item_no_result_inj, head_ctx_step_result.
Qed.
End head_step.

End bor_lang.

(** Language *)
Canonical Structure bor_ectxi_lang fns := EctxiLanguage (bor_lang.bor_lang_mixin fns).
Canonical Structure bor_ectx_lang fns := EctxLanguageOfEctxi (bor_ectxi_lang fns).
Canonical Structure bor_lang fns := LanguageOfEctx (bor_ectx_lang fns).

Export bor_lang.

Lemma fill_result fns K (e : ectx_language.expr (bor_ectx_lang fns)) :
  is_Some (to_result (fill K e)) → is_Some (to_result e) ∧ K = [].
Proof.
  revert e. induction K as [|Ki K IH]; intros e; [done|].
  move => /= /IH [Eq ?]. subst. split.
  - by eapply fill_item_result.
  - destruct Eq. by destruct Ki.
Qed.

Lemma fill_not_result fns K (e : ectx_language.expr (bor_ectx_lang fns))  :
  to_result e = None → to_result (fill K e) = None.
Proof.
  revert e. induction K as [|Ki K IH]; intros; [done|].
  by apply IH, fill_item_no_result.
Qed.

(* Allocate a place of type [T] and initialize it with a value [v] *)
Definition new_place T (v: expr) : expr :=
  let: "x" := Alloc T in "x" <- v ;; "x".

(* Retag a place [p] that is a pointer of kind [pk] to a region of type [T],
  with retag [kind] *)
Definition retag_place
  (p: expr) (pk: pointer_kind) (T: type) (kind: retag_kind) : expr :=
  let: "p" := p in
  (* read the current tag of the place [p] *)
  let: "o" := & "p" in
  (* retag and update with new tag *)
  "p" <- Retag "o" pk T kind.
