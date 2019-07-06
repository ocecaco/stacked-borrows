From stbor.sim Require Import local invariant refl_step.

Set Default Proof Using "Type".

(** Moving a read of a mutable reference down across code that *may* use that ref. *)

(* Assuming x : &mut i32 *)
Definition ex1_down : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in (* put argument into place *)
    Retag "x"  FnEntry ;;
    let: "v" := Copy *{int} "x" in
    Call #[ScFnPtr "f"] [] ;;
    "v"
    .

Definition ex1_down_opt : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    Retag "x"  FnEntry ;;
    Call #[ScFnPtr "f"] [] ;;
    Copy *{int} "x"
    .


Lemma ex1_down_sim_fun fs ft : ⊨ᶠ{fs,ft} ex1_down ≥ ex1_down_opt.
Proof.
  intros r es et vls vlt σs σt FREL SUBSTs SUBSTt.
  destruct vls as [|vs []]; [done| |done].  simpl in SUBSTs.
  destruct vlt as [|vt []]; [done| |done].  simpl in SUBSTt. simplify_eq.

  (* InitCall *)
  exists 10%nat.
  apply sim_body_init_call. simpl.
Abort.
