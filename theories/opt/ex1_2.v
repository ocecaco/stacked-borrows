From stbor.sim Require Import local invariant one_step.

Set Default Proof Using "Type".

Definition ex1_2 : function :=
  fun: ["x"],
  Retag "x"  FnEntry ;;
  *{int} (Copy1 "x") <- #[42] ;;
  Call #[ScFnPtr "f"] [] ;;
  *{int} (Copy1 "x") <- #[13]
  .

Definition ex1_2_opt_1 : function :=
  fun: ["x"],
  Retag "x"  FnEntry ;;
  Call #[ScFnPtr "f"] [] ;;
  *{int} (Copy1 "x") <- #[42] ;;
  *{int} (Copy1 "x") <- #[13]
  .

Definition ex1_2_opt_2 : function :=
  fun: ["x"],
  Retag "x"  FnEntry ;;
  Call #[ScFnPtr "f"] [] ;;
  *{int} (Copy1 "x") <- #[13]
  .

Lemma ex1_2_sim_fun fs ft : ⊨{fs,ft} ex1_2 ≥ᶠ ex1_2_opt_1.
Proof.
  intros [r1 r2] es et els elt σs σt FAs FAt FREL SUBSTs SUBSTt.
  destruct els as [|efs []]; [done| |done].  simpl in SUBSTs.
  destruct elt as [|eft []]; [done| |done].  simpl in SUBSTt. simplify_eq.

  (* InitCall *)
  exists 1%nat.
  apply sim_body_init_call. rewrite pair_op.
Abort.