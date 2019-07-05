From stbor.sim Require Import local invariant refl_step.

Set Default Proof Using "Type".

(* Assuming x : &mut i32 *)
Definition ex1 : expr :=
  let: "x" := new_place (&mut int) &"i" in
  Retag "x" Default ;;
  Call #[ScFnPtr "f"] [] ;;
  *{int} "x" <- #[42] ;;
  Call #[ScFnPtr "g"] [] ;;
  Copy *{int} "x"
  .

Definition ex1_opt : expr :=
  let: "x" := new_place (&mut int) &"i" in
  Retag "x" Default ;;
  Call #[ScFnPtr "f"] [] ;;
  *{int} "x" <- #[42] ;;
  let: "v" := Copy *{int} "x" in
  Call #[ScFnPtr "g"] [] ;;
  "v"
  .

Lemma ex1_sim_body fs ft r n σs σt :
  (* TODO: what's in r? *)
  r ⊨{n, fs,ft} (ex1, σs) ≥ (ex1_opt, σt) : (λ r' _ vs' σs' vt' σt', vrel_expr r' vs' vt').
Proof.
Abort.
