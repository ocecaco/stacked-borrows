From stbor.sim Require Import local invariant refl_step.

Set Default Proof Using "Type".

(** Moving a write to a mutable reference up across unknown code. *)

(* Assuming x : &mut i32 *)
Definition ex3 : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    Retag "x"  FnEntry ;;
    *{int} "x" <- #[42] ;;
    let: "v" := Call #[ScFnPtr "f"] [] in
    *{int} "x" <- #[13] ;;
    "v"
  .

Definition ex3_opt_1 : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    Retag "x"  FnEntry ;;
    *{int} "x" <- #[42] ;;
    *{int} "x" <- #[13] ;;
    Call #[ScFnPtr "f"] []
  .

Definition ex3_opt_2 : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    Retag "x"  FnEntry ;;
    *{int} "x" <- #[13] ;;
    Call #[ScFnPtr "f"] []
  .

Lemma ex3_sim_fun fs ft : ⊨{fs,ft} ex3 ≥ᶠ ex3_opt_1.
Proof.
  intros r es et els elt σs σt FAs FAt FREL SUBSTs SUBSTt.
  destruct els as [|efs []]; [done| |done].  simpl in SUBSTs.
  destruct elt as [|eft []]; [done| |done].  simpl in SUBSTt. simplify_eq.

  (* InitCall *)
  exists 10%nat.
  apply sim_body_init_call. simpl.
Abort.
