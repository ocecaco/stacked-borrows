From stbor.sim Require Import local invariant one_step.

Set Default Proof Using "Type".

Definition foo_s : function :=
  fun: [],
  let: "i" := new_place int #[1] in
  let: "x" := new_place (&mut int) &"i" in
  Retag "x" Default ;;
  let: "j" := new_place int #[1] in
  let: "y" := new_place (&mut int) &"j" in
  Retag "y" Default ;;
  *{int} (Copy1 "y") <- #[5] ;;
  *{int} (Copy1 "x") <- #[3] ;;
  Free "i" ;;
  Free "x" ;;
  Free "j" ;;
  Free "y"
  .

Definition foo_t : function :=
  fun: [],
  let: "i" := new_place int #[1] in
  let: "x" := new_place (&mut int) &"i" in
  Retag "x" Default ;;
  let: "j" := new_place int #[1] in
  let: "y" := new_place (&mut int) &"j" in
  Retag "y" Default ;;
  (* reordering x and y *)
  *{int} (Copy1 "x") <- #[3] ;;
  *{int} (Copy1 "y") <- #[5] ;;
  Free "i" ;;
  Free "x" ;;
  Free "j" ;;
  Free "y"
  .

Lemma foo_sim_fun fs ft : ⊨{fs,ft} foo_s ≥ᶠ foo_t.
Proof.
  move => r es et els elt σs σt _ _ _
          /subst_l_nil_is_Some ? /subst_l_nil_is_Some ?.
  subst es et. clear els elt.

  (* InitCall *)
  exists 1%nat.
Abort.
