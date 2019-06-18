From Paco Require Export paco.

From stbor.sim Require Export invariant local_base.

Set Default Proof Using "Type".

Definition sim_body := sim_local_body wsat vrel_expr.
Definition sim_fun := sim_local_fun wsat vrel_expr.
Definition sim_funs := sim_local_funs wsat vrel_expr.

Definition init_state := (mkState ∅ ∅ [] O O).

(* Program simulation: All functions are related, and so is initialization. *)
Definition sim_prog (prog_src prog_tgt: fn_env) : Prop :=
  sim_funs prog_src prog_tgt ∧
  sim_body prog_src prog_tgt ε (Call #["main"] []) init_state (Call #["main"] []) init_state.
