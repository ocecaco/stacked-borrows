From iris.program_logic Require Export language ectx_language ectxi_language.

From stbor Require Export expr_semantics bor_semantics.

Set Default Proof Using "Type".

Module bor_lang.

(** COMBINED SEMANTICS -------------------------------------------------------*)

Record state := mkState {
  (* Heap with base values *)
  shp : mem;
  (* Stacked borrows for the heap *)
  sst : stacks;
  (* Active call tracker *)
  spr : protectors;
  (* Counter for pointer tag generation *)
  scn : ptr_id;
}.

Record config := mkConfig {
  (* Static global function table *)
  cfn : fn_env;
  (* Shared state *)
  cst : state;
}.

Implicit Type (σ: config).

Inductive head_step :
  expr → config → list mem_event → expr → config → list expr → Prop :=
  | HeadPureS σ e e'
      (ExprStep: pure_expr_step σ.(cst).(shp) e e')
    : head_step e σ [SilentEvt] e' σ []
  | HeadImpureS σ e e' ev h0 h' α' β' clock'
      (ExprStep : mem_expr_step σ.(cfn) σ.(cst).(shp) e ev h0 e')
      (InstrStep: bor_step h0 σ.(cst).(sst) σ.(cst).(spr) σ.(cst).(scn) ev h' α' β' clock')
    : head_step e σ [ev] e' (mkConfig σ.(cfn) (mkState h' α' β' clock')) [].


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
  - case He=> _. clear He. induction el=>//=. rewrite andb_True=>?.
    f_equal; intuition eauto with set_solver.
Qed.

Lemma is_closed_nil_subst e x es : is_closed [] e → subst x es e = e.
Proof. intros. apply is_closed_subst with []; set_solver. Qed.

Lemma is_closed_of_val X v : is_closed X (of_val v).
Proof.
  destruct v as [[]|vl|]; auto.
  induction vl as [|v vl]; first auto. destruct v; simpl; auto.
Qed.

Lemma to_lits_cons vl e el:
  to_lits vl (e :: el) = v ← to_lit e; to_lits (vl ++ [v]) el.
Proof.
  rewrite /to_lits /=. destruct (to_lit e); simpl; [done|].
  by induction el.
Qed.
Lemma to_lits_app vl el1 el2 :
  to_lits vl (el1 ++ el2) = vl' ← to_lits vl el1; to_lits vl' el2.
Proof.
  revert vl. induction el1 as [|e el1 IH]; intros vl; [done|].
  rewrite /= 2!to_lits_cons option_bind_assoc.
  apply option_bind_ext; [|done]. intros; by apply IH.
Qed.

Lemma to_of_lits vl1 vl2 :
  to_lits vl1 (Lit <$> vl2) = Some (vl1 ++ vl2).
Proof.
  revert vl1. induction vl2 as [|v vl2 IH]; intros vl1; [by rewrite app_nil_r|].
  rewrite fmap_cons to_lits_cons  /= IH. f_equal.
  by rewrite (cons_middle v vl1 vl2) app_assoc.
Qed.

Lemma of_to_lit e v : to_lit e = Some v → Lit v = e.
Proof. destruct e=>//= Eq. by inversion Eq. Qed.
Lemma of_to_lits vl1 el2 vl:
  to_lits vl1 el2 = Some vl →
  of_val (TValV vl) = (TVal ((Lit <$> vl1) ++ el2)).
Proof.
  revert vl1 vl. induction el2 as [|e el2 IH]; intros vl1 vl.
  - by rewrite /to_lits /= app_nil_r => [[->]].
  - rewrite to_lits_cons.
    destruct (to_lit e) as [v|] eqn:Eqv; [|done].
    move => /(IH _ _) ->. f_equal.
    by rewrite fmap_app -(of_to_lit _ _ Eqv) /= -app_assoc cons_middle.
Qed.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. destruct v as [[]|vl|]; auto. by rewrite /= to_of_lits. Qed.
Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  destruct e=>//=; [|destruct (to_lits [] el) as [vl|] eqn:Eq; [|done]
                    |]; intros [= <-]; auto.
  by rewrite (of_to_lits _ _ _ Eq).
Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -2!to_of_val Hv /=. Qed.

Lemma is_closed_to_val X e v : to_val e = Some v → is_closed X e.
Proof. intros <-%of_to_val. apply is_closed_of_val. Qed.

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

Instance lit_eq_dec : EqDecision lit.
Proof. solve_decision. Defined.
Instance lit_countable : Countable lit.
Proof.
  refine (inj_countable
          (λ v, match v with
              | LitPoison => inl (inl (inl ()))
              | LitLoc l bor => inl (inl (inr (l,bor)))
              | LitInt n => inl (inr (inl n))
              | LitFnPtr n => inl (inr (inr n))
              | LitCall n => inr n
              end)
          (λ s, match s with
              | inl (inl (inl ())) => Some LitPoison
              | inl (inl (inr (l,bor))) => Some $ LitLoc l bor
              | inl (inr (inl n)) => Some $ LitInt n
              | inl (inr (inr n)) => Some $ LitFnPtr n
              | inr n => Some $ LitCall n
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
  | Case e el, Case e' el' | Call e el, Call e' el'
    (* | App e el, App e' el' *) => expr_beq e e' && expr_list_beq el el'
  (* | Rec f xl e, Rec f' xl' e' =>
      bool_decide (f = f') && bool_decide (xl = xl') && expr_beq e e' *)
  | BinOp op e1 e2, BinOp op' e1' e2' =>
      bool_decide (op = op') && expr_beq e1 e1' && expr_beq e2 e2'
  | TVal el, TVal el' => expr_list_beq el el'
  | Place l bor T , Place l' bor' T' =>
      bool_decide (l = l') && bool_decide (bor = bor') && bool_decide (T = T')
  | Deref e T, Deref e' T' =>
      bool_decide (T = T') && expr_beq e e'
  | Retag e kind call, Retag e' kind' call' =>
     bool_decide (kind = kind') && expr_beq e e' && expr_beq call call'
  | Copy e, Copy e' | Ref e, Ref e'
  (* | AtomRead e, AtomRead e' *) | EndCall e, EndCall e' => expr_beq e e'
  | Let x e1 e2, Let x' e1' e2' =>
    bool_decide (x = x') && expr_beq e1 e1' && expr_beq e2 e2'
  | Proj e1 e2, Proj e1' e2' | Conc e1 e2, Conc e1' e2'
    | Write e1 e2, Write e1' e2' (* | AtomWrite e1 e2, AtomWrite e1' e2' *) =>
      expr_beq e1 e1' && expr_beq e2 e2'
  | Field e path, Field e' path' => expr_beq e e' && bool_decide (path = path')
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
    destruct e1 as [| |? el1| |el1| | | | | | | | | | | | | |? el1],
             e2 as [| |? el2| |el2| | | | | | | | | | | | | |? el2];
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
      (* | Rec f xl e => GenNode 2 [GenLeaf $ inl $ inl $ inr $ inl f;
                                 GenLeaf $ inl $ inl $ inr $ inr xl; go e]
      | App e el => GenNode 3 (go e :: (go <$> el)) *)
      | Call e el => GenNode 2 (go e :: (go <$> el))
      | EndCall e => GenNode 3 [go e]
      | BinOp op e1 e2 => GenNode 4 [GenLeaf $ inl $ inl $ inr $ inl op;
                                     go e1; go e2]
      | TVal el => GenNode 5 (go <$> el)
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
      | Field e path => GenNode 15 [GenLeaf $ inr $ inl $ inl (* $ inl *) path; go e]
      | Retag e kind call => GenNode 16 [GenLeaf $ inr $ inl (* $ inr *) $ inr kind; go e; go call]
      | Let x e1 e2 => GenNode 17 [GenLeaf $ inr $ inr x; go e1; go e2]
      | Case e el => GenNode 18 (go e :: (go <$> el))
      (* | Fork e => GenNode 23 [go e]
      | SysCall id => GenNode 24 [GenLeaf $ inr $ inr id] *)
     end)
    (fix go s := match s with
     | GenNode 0 [GenLeaf (inl (inl (inl (inl x))))] => Var x
     | GenNode 1 [GenLeaf (inl (inl (inl (inr l))))] => Lit l
     | GenNode 2 (e :: el) => Call (go e) (go <$> el)
     | GenNode 3 [e] => EndCall (go e)
     (* | GenNode 2 [GenLeaf (inl (inl (inr (inl f))));
                  GenLeaf (inl (inl (inr (inr xl)))); e] => Rec f xl (go e)
     | GenNode 3 (e :: el) => App (go e) (go <$> el) *)
     | GenNode 4 [GenLeaf (inl (inl (inr (inl op)))); e1; e2] => BinOp op (go e1) (go e2)
     | GenNode 5 el => TVal (go <$> el)
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
     | GenNode 15 [GenLeaf (inr (inl (inl (*  (inl *) path(* ) *)))); e] => Field (go e) path
     | GenNode 16 [GenLeaf (inr (inl (* (inr *) (inr kind)(* ) *))); e; call] =>
        Retag (go e) kind (go call)
     | GenNode 17 [GenLeaf (inr (inr x)); e1; e2] => Let x (go e1) (go e2)
     | GenNode 18 (e :: el) => Case (go e) (go <$> el)
     (* | GenNode 23 [e] => Fork (go e)
     | GenNode 24 [GenLeaf (inr (inr id))] => SysCall id *)
     | _ => Lit LitPoison
     end) _).
  fix FIX 1. intros []; f_equal=>//; revert el; clear -FIX.
  - fix FIX_INNER 1. intros []; [done|]. by simpl; f_equal.
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
          | LitV v => inl $ inl v
          | TValV vl => inl $ inr vl
          | PlaceV l bor T => inr (l, bor, T)
          end)
    (λ x, match x with
          | inl (inl v) => Some $ LitV $ v
          | inl (inr vl) => Some $ TValV vl
          | inr (l, bor, T) => Some $ PlaceV l bor T
          end) _).
  by intros [].
Qed.

Instance expr_inhabited : Inhabited expr := populate (Lit LitPoison).
Instance val_inhabited : Inhabited val := populate (LitV LitPoison).
Instance state_Inhabited : Inhabited state.
Proof. do 2!econstructor; exact: inhabitant. Qed.

Canonical Structure locC := leibnizC loc.
Canonical Structure valC := leibnizC val.
Canonical Structure exprC := leibnizC expr.
Canonical Structure stateC := leibnizC state.

(** Basic properties about the language *)

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma to_lits_elem_Some vl vl' el e:
  to_lits vl el = Some vl' → e ∈ el → is_Some (to_val e).
Proof.
  revert vl. induction el as [|e' ? IH]; intros vl; [by intros _ ?%elem_of_nil|].
  rewrite to_lits_cons.
  destruct (to_lit e') as [v'|] eqn:Eq'; [|done].
  move => /= /IH In /elem_of_cons [->|/In //]. rewrite -(of_to_lit _ _ Eq').
  by eexists.
Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof.
  intros [v ?]. destruct Ki; simplify_option_eq; eauto.
  eapply to_lits_elem_Some; eauto. set_solver.
Qed.

Lemma to_lits_elem_None vl el e:
  to_val e = None → e ∈ el → to_lits vl el = None.
Proof.
  revert vl. induction el as [|e' ? IH]; intros vl; [by intros _ ?%elem_of_nil|].
  rewrite to_lits_cons.
  destruct (to_lit e') as [v'|] eqn:Eq'; [|done].
  move => /= EqN /elem_of_cons [?|IN].
  - subst. exfalso. move : Eq' EqN. by destruct e'.
  - by apply IH.
Qed.

Lemma fill_item_no_val Ki e :
  to_val e = None → to_val (fill_item Ki e) = None.
Proof.
  intros EqN. destruct Ki; simplify_option_eq; eauto.
  rewrite (to_lits_elem_None _ _ e EqN) // elem_of_app.
  by right; left.
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
  destruct Ki1 as [|v1 vl1 el1| | | |vl1 el1| | | | | | | | | | | | | | |],
           Ki2 as [|v2 vl2 el2| | | |vl2 el2| | | | | | | | | | | | | | |];
  intros He1 He2 EQ; try discriminate; simplify_eq/=;
    repeat match goal with
    | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
    end; auto;
  destruct (list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2); auto; congruence.
Qed.

Lemma val_head_stuck e1 σ1 κ e2 σ2 efs :
  head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; inversion ExprStep; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 efs :
  head_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
Proof.
  destruct Ki; inversion_clear 1; inversion_clear ExprStep;
    simplify_option_eq; eauto.
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
