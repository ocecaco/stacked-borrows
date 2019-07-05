From stbor.sim Require Import local invariant refl_step.

Set Default Proof Using "Type".

(* Assuming x : & i32 *)
Definition ex2 : expr :=
  let: "x" := new_place (& int) &"i" in
  Retag "x" Default ;;
  Copy *{int} "x" ;;
  Call #[ScFnPtr "f"] ["x"] ;;
  Copy *{int} "x"
  .

Definition ex2_opt : expr :=
  let: "x" := new_place (& int) &"i" in
  Retag "x" Default ;;
  Copy *{int} "x" ;;
  let: "v" := Copy *{int} "x" in
  Call #[ScFnPtr "f"] ["x"] ;;
  "v"
  .

Lemma ex2_sim_body fs ft r n σs σt :
  (* TODO: what's in r? *)
  r ⊨{n, fs,ft} (ex2, σs) ≥ (ex2_opt, σt) : (λ r' _ vs' σs' vt' σt', vrel_expr r' vs' vt').
Proof.
Abort.
