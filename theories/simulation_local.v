From Paco Require Import paco.
From iris.algebra Require Import cmra.

From stbor Require Import simulation.

Section local.
Context {A: cmraT}.
Variable (wsat: A → state → state → Prop).
Variable (vrel: A → expr → expr → Prop).
Variable (fns_src fns_tgt: fn_env).

Section local_step.
Variable (φ: A → call_id → call_id_stack → state → call_id → call_id_stack → state → Prop).
Variable (c_src: call_id) (cids_entry_src: call_id_stack)
         (c_tgt: call_id) (cids_entry_tgt: call_id_stack).

(* TODO: encode what it means for the context to not contain our private tags! *)
(* TODO: how do we know we're at the top of the stack? *)
Inductive _sim_local
  (sim_local : A → A → expr → state → expr → state → Prop)
  (r_f r: A) : expr → state → expr → state → Prop :=
(* If src is stuck, then anything is related *)
| sim_local_stuck e_src σ_src e_tgt σ_tgt
    (STUCK: stuck e_src (mkConfig fns_src σ_src))
    : _sim_local sim_local r_f r e_src σ_src e_tgt σ_tgt
(* If tgt makes 1 step, src can make some step *)
| sim_local_step e_src σ_src e_tgt σ_tgt
    (STEP: ∀ e_tgt' cfg_tgt',
      ✓ (r ⋅ r_f) →
      (* wsat (r ⋅ r_f) σ_src σ_tgt → *)
      φ r c_src cids_entry_src σ_src c_tgt cids_entry_tgt σ_tgt →
      (* if tgt can makes 1 step *)
      (e_tgt, (mkConfig fns_tgt σ_tgt)) ~t~> (e_tgt', cfg_tgt') →
      (* then we locally can makes some step and still preserve the frame r_f,
        and the simulation continues. *)
      ∃ e_src' cfg_src' r',
        (e_src, (mkConfig fns_src σ_src)) ~t~>* (e_src', cfg_src') ∧
        ✓ (r' ⋅ r_f) ∧
        (* wsat (r' ⋅ r_f) cfg_src'.(cst) cfg_tgt'.(cst) ∧ *)
        φ r' c_src cids_entry_src cfg_src'.(cst) c_tgt cids_entry_tgt cfg_tgt'.(cst) ∧
        sim_local r_f r' e_src' cfg_src'.(cst) e_tgt' cfg_tgt'.(cst))
    : _sim_local sim_local r_f r e_src σ_src e_tgt σ_tgt
(* If tgt prepares to make a call to [name], src should be able to make the same
  call. Here we do not want to step into the call of [name], but to step over
  it. To make the call, we need to re-establish
 `wsat (r ⋅ r_f) cfg_src.(cst) σ_tgt`. Then after the call we can assume that:
  - the context K_src/tgt did not change
  - the call id stack did not change
  - the framed resources r ⋅ r_f did not change
  - the invariant is re-established by [name] for some new frame and new states. *)
| sim_local_step_over_call K_src K_tgt name e_src el_src el_tgt σ_src
    cfg_src σ_tgt
    (STEPS: (e_src, (mkConfig fns_src σ_src)) ~t~>*
            (fill K_src (Call #(LitFnPtr name) el_src), cfg_src))
    (VALS: Forall (λ ei, terminal ei) el_src)
    (VALT: Forall (λ ei, terminal ei) el_tgt)
    (VALEQ: Forall2 (vrel (r ⋅ r_f)) el_src el_tgt)
    (VALID: ✓ (r ⋅ r_f))
    (INV: wsat (r ⋅ r) cfg_src.(cst) σ_tgt)
    (RET: ∀ v_src v_tgt r' cfg_src' cfg_tgt',
      (* For any new resource r' that is compatible with our local resource r and frame r_f *)
      ✓ (r ⋅ r' ⋅ r_f) →
      (* and wsat holds for the composed resource + pair of physical states, *)
      wsat (r ⋅ r' ⋅ r_f) cfg_src'.(cst) cfg_tgt'.(cst) →
      (* and the returned values are related w.r.t. (r ⋅ r' ⋅ r_f) *)
      vrel (r ⋅ r' ⋅ r_f) (of_val v_src) (of_val v_tgt) →
      (* stack unchanged *)
      cfg_src'.(cst).(scs) = cfg_src.(cst).(scs) →
      cfg_tgt'.(cst).(scs) = σ_tgt.(scs) →
      sim_local (r_f) (r ⋅ r')
                (fill K_src (of_val v_src)) cfg_src'.(cst)
                (fill K_tgt (of_val v_tgt)) cfg_tgt'.(cst))
    : _sim_local sim_local r_f r e_src σ_src
        (fill K_tgt (Call #(LitFnPtr name) el_tgt)) σ_tgt
(* If tgt prepares to end, src also prepares to end *)
| sim_local_end_call v_src σ_src v_tgt σ_tgt
    (GUAR: ∀ cfg_tgt',
        ✓ (r ⋅ r_f) →
        (* wsat (r ⋅ r_f) σ_src σ_tgt → *)
        φ r c_src cids_entry_src σ_src c_tgt cids_entry_tgt σ_tgt →
        (* if tgt can end call *)
        (EndCall (of_val v_tgt), (mkConfig fns_tgt σ_tgt)) ~t~> cfg_tgt' →
        (* then src can also end call *)
        ∃ cfg_src' r', (EndCall (of_val v_src), (mkConfig fns_src σ_tgt)) ~t~> cfg_src' ∧
        (* and re-establish wsat *)
        ✓ (r' ⋅ r_f) ∧ wsat (r' ⋅ r_f) cfg_src'.2.(cst) cfg_tgt'.2.(cst) ∧
        (* and the returned values are related *)
        vrel (r' ⋅ r_f) (of_val v_src) (of_val v_tgt) ∧
        (* and call id stacks are restored *)
        cfg_src'.2.(cst).(scs) = cids_entry_src ∧
        cfg_tgt'.2.(cst).(scs) = cids_entry_tgt)
    : _sim_local sim_local r_f r (EndCall (of_val v_src)) σ_src (EndCall (of_val v_tgt)) σ_tgt
.

Lemma sim_local_mono : monotone6 _sim_local.
Proof.
  intros gσ_f gσ es σs et σt r r' SIM LE; inversion SIM; subst.
  - by eapply sim_local_stuck; eauto.
  - eapply sim_local_step. intros et' cfgt' VAL IL STEPT.
    destruct (STEP _ _ VAL IL STEPT) as (es' & cfgs' & gσ' & STEPS & VAL' & IL' & Hr).
    naive_solver.
  - by eapply sim_local_step_over_call; eauto.
  - by eapply sim_local_end_call; eauto.
Qed.

Definition sim_local := paco6 _sim_local bot6.

End local_step.

(* Simulating functions: assuming the calls have been initialized. *)
Definition sim_local_fn
  (φ: _ → _ → _ → _ → _ → _ → _ → Prop) (fn_src fn_tgt : function) : Prop :=
  ∀ (gσ_f gσ : A)
    (c_src: call_id) (cids_entry_src: call_id_stack)
    (c_tgt: call_id) (cids_entry_tgt: call_id_stack)
    el_src el_tgt σ_src σ_tgt e_src e_tgt
    (VALS: Forall (λ ei, terminal ei) el_src)
    (VALT: Forall (λ ei, terminal ei) el_tgt)
    (VALEQ: Forall2 sim_expr_terminal el_src el_tgt)
    (EQS: match fn_src with
          | FunV xl e => subst_l xl el_src e = Some e_src
          end)
    (EQT: match fn_tgt with
          | FunV xl e => subst_l xl el_tgt e = Some e_tgt
          end)
    (VALID: ✓ (gσ ⋅ gσ_f))
    (INVG: wsat (gσ ⋅ gσ_f) σ_src σ_tgt)
    (INVL: φ gσ c_src cids_entry_src σ_src c_tgt cids_entry_tgt σ_tgt),
    sim_local φ c_src cids_entry_src c_tgt cids_entry_tgt
              gσ_f gσ e_src σ_src e_tgt σ_tgt.

Definition sim_local_fns : Prop :=
  ∀ name fn_src, fns_src !! name = Some fn_src → ∃ φ fn_tgt,
    fns_tgt !! name = Some fn_tgt ∧ sim_local_fn φ fn_src fn_tgt.
End local.

Hint Resolve sim_local_mono : paco.

Section invariant.
  Context {A: cmraT}.
  Definition wsat (σGAll: A) (σ_src σ_tgt: state) : Prop := True.

  Definition local_inv (σG: A)
    (c_src: call_id) (cids_entry_src: call_id_stack) (σ_src: state)
    (c_tgt: call_id) (cids_entry_tgt: call_id_stack) (σ_tgt: state) : Prop := True.
End invariant.
