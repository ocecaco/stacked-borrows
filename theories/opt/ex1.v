From stbor.sim Require Import local invariant refl_step tactics body.

Set Default Proof Using "Type".

(** Moving read of mutable reference up across code not using that ref. *)

(* Assuming x : &mut i32 *)
Definition ex1 : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in (* put argument into place *)
    Retag "x" Default ;;
    Call #[ScFnPtr "f"] [] ;;
    *{int} "x" <- #[42] ;;
    Call #[ScFnPtr "g"] [] ;;
    Copy *{int} "x"
  .

Definition ex1_opt : function :=
  fun: ["i"],
    let: "x" := new_place (&mut int) "i" in
    Retag "x" Default ;;
    Call #[ScFnPtr "f"] [] ;;
    *{int} "x" <- #[42] ;;
    let: "v" := Copy *{int} "x" in
    Call #[ScFnPtr "g"] [] ;;
    "v"
  .

Lemma ex1_sim_body fs ft : ⊨{fs,ft} ex1 ≥ᶠ ex1_opt.
Proof.
  intros rf es et vls vlt σs σt FREL SUBSTs SUBSTt.
  destruct vls as [|vs []]; [done| |done].  simpl in SUBSTs.
  destruct vlt as [|vt []]; [done| |done].  simpl in SUBSTt. simplify_eq.

  (* InitCall *)
  exists 10%nat.
  apply sim_body_init_call. simpl.

  (* Alloc *)
  sim_apply sim_body_alloc_local. simpl.

  (* Let *)
  sim_apply sim_body_let_place. simpl.
Abort.
