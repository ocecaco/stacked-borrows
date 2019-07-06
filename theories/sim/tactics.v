From stbor.lang Require Export lang.
From stbor.sim Require Import body.

Ltac reshape_expr e tac :=
  (* [vs] is the accumulator *)
  let rec go_fun K f vs es :=
    match es with
    | (Val ?v) :: ?es => go_fun K f (v :: vs) es
    | ?e :: ?es => go (CallRCtx f (reverse vs) es :: K) e
    end
  (* [K] accumulates the context *)
  with go K e :=
  match e with
  | _ => tac K e
  | Let ?x ?e1 ?e2 => go (LetCtx x e2 :: K) e1
  | Call (Val ?v) ?el => go_fun K v (@nil val) el
  | Call ?e ?el => go (CallLCtx el :: K) e
  | BinOp ?op (Val ?v1) ?e2 => go (BinOpRCtx op v1 :: K) e2
  | BinOp ?op ?e1 ?e2 => go (BinOpLCtx op e2 :: K) e1
  (* FIXME: add remaining context items *)
  end
  in go (@nil ectx_item) e.

Tactic Notation "sim_bind" open_constr(efocs) open_constr(efoct) :=
  match goal with 
  | |- _ ⊨{_,_,_} (?es, _) ≥ (?et, _) : _ =>
    reshape_expr es ltac:(fun Ks es =>
      unify es efocs;
      reshape_expr et ltac:(fun Kt et =>
        unify et efoct;
        eapply (sim_body_bind _ _ _ _ Ks Kt es et)
      )
    )
  end.

Tactic Notation "sim_apply" open_constr(lem) :=
  match goal with
  | |- _ ⊨{_,_,_} (?es, _) ≥ (?et, _) : _ =>
    reshape_expr es ltac:(fun Ks es =>
      reshape_expr et ltac:(fun Kt et =>
        eapply (sim_body_bind _ _ _ _ Ks Kt es et);
        eapply lem
      )
    )
  end.
