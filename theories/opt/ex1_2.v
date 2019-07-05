From stbor.sim Require Import local invariant refl_step.

Set Default Proof Using "Type".

(* Assuming x : &mut i32 *)
Definition ex1_2 : function :=
  fun: ["i"],
  let: "x" := new_place (&mut int) &"i" in
  Retag "x"  FnEntry ;;
  *{int} "x" <- #[42] ;;
  Call #[ScFnPtr "f"] [] ;;
  *{int} "x" <- #[13]
  .

Definition ex1_2_opt_1 : function :=
  fun: ["i"],
  let: "x" := new_place (&mut int) &"i" in
  Retag "x"  FnEntry ;;
  Call #[ScFnPtr "f"] [] ;;
  *{int} "x" <- #[42] ;;
  *{int} "x" <- #[13]
  .

Definition ex1_2_opt_2 : function :=
  fun: ["i"],
  let: "x" := new_place (&mut int) &"i" in
  Retag "x"  FnEntry ;;
  Call #[ScFnPtr "f"] [] ;;
  *{int} "x" <- #[13]
  .

Lemma ex1_2_sim_fun fs ft : ⊨{fs,ft} ex1_2 ≥ᶠ ex1_2_opt_1.
Proof.
  intros r es et els elt σs σt FAs FAt FREL SUBSTs SUBSTt.
  destruct els as [|efs []]; [done| |done].  simpl in SUBSTs.
  destruct elt as [|eft []]; [done| |done].  simpl in SUBSTt. simplify_eq.

  (* InitCall *)
  exists 10%nat.
  apply sim_body_init_call. simpl.
Abort.