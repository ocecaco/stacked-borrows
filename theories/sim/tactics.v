From stbor.lang Require Export lang.
From stbor.sim Require Export simple.
From stbor.sim Require Import body.

Ltac reshape_expr e tac :=
  (* [vs] is the accumulator *)
  let rec go_call K v vs es :=
    match es with
    | (Val ?v) :: ?es => go_call K v (v :: vs) es
    | ?e :: ?es => go (CallRCtx v (reverse vs) es :: K) e
    end
  (* [K] accumulates the context *)
  with go K e :=
  match e with
  | _ => tac K e
  | Call (Val ?v) ?el => go_call K (ValR v) (@nil result) el
  | Call (of_result ?r) ?el => go_call K r (@nil result) el
  | Call ?e ?el => go (CallLCtx el :: K) e
  | EndCall ?e => go (EndCallCtx :: K) e
  | BinOp ?op (Val ?v1) ?e2 => go (BinOpRCtx op (ValR v1) :: K) e2
  | BinOp ?op (of_result ?r) ?e2 => go (BinOpRCtx op r :: K) e2
  | BinOp ?op ?e1 ?e2 => go (BinOpLCtx op e2 :: K) e1
  | Proj (Val ?v1) ?e2 => go (ProjRCtx (ValR v1) :: K) e2
  | Proj (of_result ?r1) ?e2 => go (ProjRCtx r1 :: K) e2
  | Proj ?e1 ?e2 => go (ProjLCtx e2 :: K) e1
  | Conc (Val ?v1) ?e2 => go (ConcRCtx (ValR v1) :: K) e2
  | Conc (of_result ?r1) ?e2 => go (ConcRCtx r1 :: K) e2
  | Conc ?e1 ?e2 => go (ConcLCtx e2 :: K) e1
  | Copy ?e => go (CopyCtx :: K) e
  | Write (Place ?l1 ?tg ?ty) ?e2 => go (WriteRCtx (PlaceR l1 tg ty) :: K) e2
  | Write (of_result ?r1) ?e2 => go (WriteRCtx r1 :: K) e2
  | Write ?e1 ?e2 => go (WriteLCtx e2 :: K) e1
  | Free ?e => go (FreeCtx :: K) e
  | Deref ?e ?T => go (DerefCtx T :: K) e
  | Ref ?e => go (RefCtx :: K) e
  | Retag ?e ?k => go (RetagCtx k :: K) e
  | Let ?x ?e1 ?e2 => go (LetCtx x e2 :: K) e1
  | Case ?e ?el => go (CaseCtx el :: K) e
  end
  in go (@nil ectx_item) e.

(** bind if K is not empty. Otherwise do nothing.
Binds cost us steps, so don't waste them! *)
Ltac sim_body_bind_core Ks es Kt et :=
  (* Ltac is SUCH a bad language... *)
  match Ks with
  | [] => match Kt with
          | [] => idtac
          | _ => eapply (sim_body_bind _ _ Ks es Kt et)
          end
  | _ => eapply (sim_body_bind _ _ Ks es Kt et)
  end.
Ltac sim_simple_bind_core Ks es Kt et :=
  (* Ltac is SUCH a bad language... *)
  match Ks with
  | [] => match Kt with
          | [] => idtac
          | _ => eapply (sim_simple_bind _ _ Ks es Kt et)
          end
  | _ => eapply (sim_simple_bind _ _ Ks es Kt et)
  end.

Tactic Notation "sim_bind" open_constr(efocs) open_constr(efoct) :=
  match goal with 
  | |- _ ⊨{_,_,_} (?es, _) ≥ (?et, _) : _ =>
    reshape_expr es ltac:(fun Ks es =>
      unify es efocs;
      reshape_expr et ltac:(fun Kt et =>
        unify et efoct;
        sim_body_bind_core Ks es Kt et
      )
    )
  | |- _ ⊨ˢ{_,_,_} (?es, _) ≥ (?et, _) : _ =>
    reshape_expr es ltac:(fun Ks es =>
      unify es efocs;
      reshape_expr et ltac:(fun Kt et =>
        unify et efoct;
        sim_simple_bind_core Ks es Kt et
      )
    )
  end.

Tactic Notation "sim_apply" open_constr(lem) :=
  match goal with
  | |- _ ⊨{_,_,_} (?es, _) ≥ (?et, _) : _ =>
    reshape_expr es ltac:(fun Ks es =>
      reshape_expr et ltac:(fun Kt et =>
        sim_body_bind_core Ks es Kt et;
        apply: lem
      )
    )
  | |- _ ⊨ˢ{_,_,_} (?es, _) ≥ (?et, _) : _ =>
    reshape_expr es ltac:(fun Ks es =>
      reshape_expr et ltac:(fun Kt et =>
        sim_simple_bind_core Ks es Kt et;
        apply: lem
      )
    )
  end.

(* HACK to avoid a bind-left/right rule. Does not work in general (e.g. when
there is an [Alloc T] in eval position on the left), but works for now. *)
Ltac test_pure_head e :=
  match e with
  | of_result _ => idtac
  | Val _ => idtac
  | Place _ _ _ => idtac
  | _ => fail
  end.

Tactic Notation "sim_bind_r" open_constr(efoc) :=
  match goal with 
  | |- _ ⊨{_,_,_} (?es, _) ≥ (?et, _) : _ =>
    reshape_expr es ltac:(fun Ks es =>
      test_pure_head es;
      reshape_expr et ltac:(fun Kt et =>
        unify et efoc;
        sim_body_bind_core Ks es Kt et
      )
    )
  end.

Tactic Notation "sim_apply_r" open_constr(lem) :=
  match goal with
  | |- _ ⊨{_,_,_} (?es, _) ≥ (?et, _) : _ =>
    reshape_expr es ltac:(fun Ks es =>
      test_pure_head es;
      reshape_expr et ltac:(fun Kt et =>
        sim_body_bind_core Ks es Kt et;
        apply: lem
      )
    )
  end.

Tactic Notation "sim_bind_l" open_constr(efoc) :=
  match goal with 
  | |- _ ⊨{_,_,_} (?es, _) ≥ (?et, _) : _ =>
    reshape_expr es ltac:(fun Ks es =>
      unify es efoc;
      reshape_expr et ltac:(fun Kt et =>
        test_pure_head et;
        sim_body_bind_core Ks es Kt et
      )
    )
  end.

Tactic Notation "sim_apply_l" open_constr(lem) :=
  match goal with
  | |- _ ⊨{_,_,_} (?es, _) ≥ (?et, _) : _ =>
    reshape_expr et ltac:(fun Kt et =>
      test_pure_head et;
      reshape_expr es ltac:(fun Ks es =>
        sim_body_bind_core Ks es Kt et;
        apply: lem
      )
    )
  end.

(** The expectation is that lemmas state their resource requirements as
[r ≡ frame ⋅ what_lemma_needs].  Users eapply the lemma, and [frame]
becomes an evar. [solve_res] solves such goals. *)
Lemma res_search_descend (R W T F L : resUR) :
  T ⋅ L ≡ F ⋅ W →
  T ⋅ L ⋅ R ≡ F ⋅ R ⋅ W.
Proof. intros ->. rewrite - !assoc. f_equiv. exact: comm. Qed.
Lemma res_search_found_left (F W : resUR) :
  W ⋅ F ≡ F ⋅ W.
Proof. exact: comm. Qed.
Lemma res_search_found_unit (F W : resUR) :
  F ≡ F ⋅ ε.
Proof. rewrite right_id //. Qed.
Lemma res_search_singleton (R W : resUR) :
  W ≡ ε ⋅ W.
Proof. rewrite left_id //. Qed.
Lemma res_search_from_incl (r1 r2 r3 : resUR) :
  r2 ≡ r3 ⋅ r1 →
  r1 ≼ r2.
Proof.
  intros EQ. eexists. rewrite EQ [r3 ⋅ _]comm. done.
Qed.
Ltac solve_res :=
  match goal with
  | |- _ ⋅ _ ≡ _ =>
      reflexivity
  | |- _ ≡ _ ⋅ ε =>
      exact: res_search_found_unit
  | |- _ ⋅ _ ≡ _ =>
      exact: res_search_found_left
  | |- _ ≡ _ =>
      exact: res_search_singleton
  | |- _ ⋅ _ ≡ _ =>
    (* The descent lemma makes sure we don't descend below
       the *last* operator. We always want to preserve having
       an operator on the LHS. *)
    simple apply res_search_descend;
    solve_res
  | |- _ ≼ _ =>
    simple eapply res_search_from_incl;
    solve_res
end.

(** For example proofs. *)
Ltac solve_sim := solve [ fast_done | solve_res | done ].
