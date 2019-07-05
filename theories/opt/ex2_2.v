From stbor.sim Require Import local invariant refl_step.

Set Default Proof Using "Type".

(* Assuming x : & i32 *)
Definition ex2_2 : function :=
  fun: ["i"],
    let: "x" := new_place (& int) &"i" in
    Retag "x"  FnEntry ;;
    let: "v" := Copy *{int} "x" in
    Call #[ScFnPtr "f"] ["x"] ;;
    "v"
    .

Definition ex2_2_opt : function :=
  fun: ["i"],
    let: "x" := new_place (& int) &"i" in
    Retag "x"  FnEntry ;;
    Call #[ScFnPtr "f"] ["x"] ;;
    Copy *{int} "x"
    .


Lemma ex2_2_sim_fun fs ft : ⊨{fs,ft} ex2_2 ≥ᶠ ex2_2_opt.
Proof.
  intros r es et els elt σs σt FAs FAt FREL SUBSTs SUBSTt.
  destruct els as [|efs []]; [done| |done].  simpl in SUBSTs.
  destruct elt as [|eft []]; [done| |done].  simpl in SUBSTt. simplify_eq.

  (* InitCall *)
  exists 10%nat.
  apply sim_body_init_call. simpl.
Abort.
