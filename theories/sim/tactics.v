From stbor.lang Require Export lang.
From stbor.sim Require Export simple.
From stbor.sim Require Import body.

Ltac reshape_expr e tac :=
  (* [vs] is the accumulator *)
  let rec go_list K Ki v vs es :=
    match es with
    | (Val ?v) :: ?es => go_list K v (v :: vs) es
    | ?e :: ?es => go (Ki v (reverse vs) es :: K) e
    end
  (* [K] accumulates the context *)
  with go K e :=
  match e with
  | _ => tac K e
  | Call (Val ?v) ?el => go_list K CallRCtx v (@nil val) el
  | Call ?e ?el => go (CallLCtx el :: K) e
  | EndCall ?e => go (EndCallCtx :: K) e
  | BinOp ?op (Val ?v1) ?e2 => go (BinOpRCtx op v1 :: K) e2
  | BinOp ?op ?e1 ?e2 => go (BinOpLCtx op e2 :: K) e1
  | Proj (Val ?v1) ?e2 => go (ProjRCtx v1 :: K) e2
  | Proj ?e1 ?e2 => go (ProjLCtx op e2 :: K) e1
  | Conc (Val ?v1) ?e2 => go (ConcRCtx v1 :: K) e2
  | Conc ?e1 ?e2 => go (ConcLCtx op e2 :: K) e1
  | Copy ?e => go (CopyCtx :: K) e
  | Write (Val ?v1) ?e2 => go (WriteRCtx v1 :: K) e2
  | Write ?e1 ?e2 => go (WriteLCtx op e2 :: K) e1
  | Free ?e => go (FreeCtx :: K) e
  | Deref ?e ?T => go (DerefCtx T :: K) e
  | Ref ?e => go (RefCtx :: K) e
  | Retag ?e ?k => go (RetagCtx k :: K) e
  | Let ?x ?e1 ?e2 => go (LetCtx x e2 :: K) e1
  | CaseCtx (Val ?v) ?el => go_list K CaseCtx v (@nil val) el
  end
  in go (@nil ectx_item) e.


(** bind if K is not empty. Otherwise do nothing.
Binds cost us steps, so don't waste them! *)
Ltac sim_body_bind_core Ks Kt es et :=
  (* Ltac is SUCH a bad language... *)
  match Ks with
  | [] => match Kt with
          | [] => idtac
          | _ => eapply (sim_body_bind _ _ _ _ Ks Kt es et)
          end
  | _ => eapply (sim_body_bind _ _ _ _ Ks Kt es et)
  end.
Ltac sim_simple_bind_core Ks Kt es et :=
  (* Ltac is SUCH a bad language... *)
  match Ks with
  | [] => match Kt with
          | [] => idtac
          | _ => eapply (sim_simple_bind _ _ Ks Kt es et)
          end
  | _ => eapply (sim_simple_bind _ _ Ks Kt es et)
  end.

Tactic Notation "sim_bind" open_constr(efocs) open_constr(efoct) :=
  match goal with 
  | |- _ ⊨{_,_,_} (?es, _) ≥ (?et, _) : _ =>
    reshape_expr es ltac:(fun Ks es =>
      unify es efocs;
      reshape_expr et ltac:(fun Kt et =>
        unify et efoct;
        sim_body_bind_core Ks Kt es et
      )
    )
  | |- _ ⊨ˢ{_,_,_} (?es, _) ≥ (?et, _) : _ =>
    reshape_expr es ltac:(fun Ks es =>
      unify es efocs;
      reshape_expr et ltac:(fun Kt et =>
        unify et efoct;
        sim_simple_bind_core Ks Kt es et
      )
    )
  end.

Tactic Notation "sim_apply" open_constr(lem) :=
  match goal with
  | |- _ ⊨{_,_,_} (?es, _) ≥ (?et, _) : _ =>
    reshape_expr es ltac:(fun Ks es =>
      reshape_expr et ltac:(fun Kt et =>
        sim_body_bind_core Ks Kt es et;
        eapply lem
      )
    )
  | |- _ ⊨ˢ{_,_,_} (?es, _) ≥ (?et, _) : _ =>
    reshape_expr es ltac:(fun Ks es =>
      reshape_expr et ltac:(fun Kt et =>
        sim_simple_bind_core Ks Kt es et;
        eapply lem
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
end.
