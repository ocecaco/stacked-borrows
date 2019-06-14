From Paco Require Import paco.
From iris.algebra Require Import cmra.

From stbor Require Import simulation.

Section local.
Context {A: ucmraT}.
Variable (wsat: A → state → state → Prop).
Variable (vrel: A → expr → expr → Prop).
Variable (fns_src fns_tgt: fn_env).
Variable (Φinit: A → state → state → Prop).

Section local_step.
(* Variable (c_src: call_id) (cids_entry_src: call_id_stack)
         (c_tgt: call_id) (cids_entry_tgt: call_id_stack). *)

(* TODO: encode what it means for the context to not contain our private tags! *)
(* TODO: how do we know we're at the top of the stack? *)
Inductive _sim_fn_body
  (sim_fn_body : A → A → expr → state → expr → state → Prop)
  (r_f r: A) : expr → state → expr → state → Prop :=
(* If src is stuck, then anything is related *)
| sim_fn_body_stuck e_src σ_src e_tgt σ_tgt
    (STUCK: stuck e_src (mkConfig fns_src σ_src))
    : _sim_fn_body sim_fn_body r_f r e_src σ_src e_tgt σ_tgt
(* If tgt makes 1 step, src can make some step *)
| sim_fn_body_step e_src σ_src e_tgt σ_tgt
    (STEP: ∀ e_tgt' cfg_tgt',
      (* if tgt can locally make 1 step *)
      (e_tgt, (mkConfig fns_tgt σ_tgt)) ~t~> (e_tgt', cfg_tgt') →
      (* then we locally can makes some step *)
      ∃ e_src' cfg_src',
        (e_src, (mkConfig fns_src σ_src)) ~t~>* (e_src', cfg_src') ∧
        sim_fn_body r_f r e_src' cfg_src'.(cst) e_tgt' cfg_tgt'.(cst))
    : _sim_fn_body sim_fn_body r_f r e_src σ_src e_tgt σ_tgt
(* If tgt prepares to make a call to [name], src should be able to make the same
  call. Here we do not want to step into the call of [name], but to step over
  it. To make such a call, we need to re-establish
 `wsat (r ⋅ r_f) cfg_src.(cst) σ_tgt`. Then after the call we can assume that:
  - the context K_src/tgt did not change
  - the call id stack did not change
  - the framed resources r ⋅ r_f did not change
  - wsat is re-established by [name] for some new frame and new states. *)
| sim_fn_body_step_over_call K_src K_tgt name e_src el_src el_tgt σ_src rc rv
    cfg_src σ_tgt
    (STEPS: (e_src, (mkConfig fns_src σ_src)) ~t~>*
            (fill K_src (Call #(LitFnPtr name) el_src), cfg_src))
    (VALS: Forall (λ ei, terminal ei) el_src)
    (VALT: Forall (λ ei, terminal ei) el_tgt)
    (VALEQ: Forall2 (vrel (rv)) el_src el_tgt)
    (VALID: ✓ (r_f ⋅ rc ⋅ rv))
    (INV: wsat (r_f ⋅ rc ⋅ rv) cfg_src.(cst) σ_tgt)
    (RET: ∀ v_src v_tgt r' cfg_src' cfg_tgt',
      (* For any new resource r' that is compatible with our local resource r and frame r_f *)
      ✓ (r_f ⋅ rc ⋅ r') →
      (* and wsat holds for the composed resource + pair of physical states, *)
      wsat (r_f ⋅ rc ⋅ r') cfg_src'.(cst) cfg_tgt'.(cst) →
      (* and the returned values are related w.r.t. (r ⋅ r' ⋅ r_f) *)
      vrel (r_f ⋅ rc ⋅ r') (of_val v_src) (of_val v_tgt) →
      (* (* stack unchanged *)
      cfg_src'.(cst).(scs) = cfg_src.(cst).(scs) →
      cfg_tgt'.(cst).(scs) = σ_tgt.(scs) → *)
      sim_fn_body r_f (rc ⋅ r')
                (fill K_src (of_val v_src)) cfg_src'.(cst)
                (fill K_tgt (of_val v_tgt)) cfg_tgt'.(cst))
    : _sim_fn_body sim_fn_body r_f r e_src σ_src
        (fill K_tgt (Call #(LitFnPtr name) el_tgt)) σ_tgt
(* If tgt prepares to end, src also prepares to end *)
| sim_fn_body_end_call v_src σ_src v_tgt σ_tgt
    (GUAR: ∀ cfg_tgt',
        (* ✓ (r ⋅ r_f) → *)
        (* if tgt can end call *)
        (EndCall (of_val v_tgt), (mkConfig fns_tgt σ_tgt)) ~t~> cfg_tgt' →
        (* then src can also end call *)
        ∃ cfg_src' r',
        (EndCall (of_val v_src), (mkConfig fns_src σ_tgt)) ~t~> cfg_src' ∧
        (* and re-establish wsat *)
        ✓ (r_f ⋅ r') ∧ wsat (r_f ⋅ r') cfg_src'.2.(cst) cfg_tgt'.2.(cst) ∧
        (* and the returned values are related *)
        vrel (r_f ⋅ r') (of_val v_src) (of_val v_tgt)
        (* (* and call id stacks are restored *)
        cfg_src'.2.(cst).(scs) = cids_entry_src ∧
        cfg_tgt'.2.(cst).(scs) = cids_entry_tgt  *))
    : _sim_fn_body sim_fn_body r_f r (EndCall (of_val v_src)) σ_src (EndCall (of_val v_tgt)) σ_tgt
.

Lemma sim_fn_body_mono : monotone6 _sim_fn_body.
Proof.
  intros r_f r es σs et σt R R' SIM LE; inversion SIM; subst.
  - by eapply sim_fn_body_stuck; eauto.
  - eapply sim_fn_body_step. intros et' cfgt' STEPT.
    destruct (STEP _ _ STEPT) as (es' & cfgs' & STEPS & Hr).
    naive_solver.
  - by eapply sim_fn_body_step_over_call; eauto.
  - by eapply sim_fn_body_end_call; eauto.
Qed.

Definition sim_fn_body := paco6 _sim_fn_body bot6.

End local_step.

Definition sim_fn_body_expr (r: A) (e_src e_tgt: expr) : Prop :=
  ∀ (r_f: A) (σ_src σ_tgt: state)
    (VAL: ✓ (r_f ⋅ r)) (INV: wsat (r_f ⋅ r) σ_src σ_tgt),
  sim_fn_body r_f r e_src σ_src e_tgt σ_tgt.

(* Simulating functions: assuming the calls have been initialized. *)
Definition sim_fn_body_fn (r: A) (fn_src fn_tgt : function) : Prop :=
  ∀ e_src e_tgt el_src el_tgt
    (VALS: Forall (λ ei, terminal ei) el_src)
    (VALT: Forall (λ ei, terminal ei) el_tgt)
    (VALEQ: Forall2 (vrel r) el_src el_tgt)
    (EQS: match fn_src with
          | FunV xl e => subst_l xl el_src e = Some e_src
          end)
    (EQT: match fn_tgt with
          | FunV xl e => subst_l xl el_tgt e = Some e_tgt
          end),
    sim_fn_body_expr r (InitCall e_src) (InitCall e_tgt).

Definition sim_fn_body_fns : Prop :=
  ∀ name fn_src, fns_src !! name = Some fn_src → ∃ r fn_tgt,
    fns_tgt !! name = Some fn_tgt ∧ sim_fn_body_fn r fn_src fn_tgt.

Lemma sim_fn_body_resource_mono r_f r1 r2 :
  r1 ≼ r2 → sim_fn_body r_f r1 <4= sim_fn_body r_f r2.
Proof.
  revert r1 r2. pcofix CIH. intros r1 r2 LE es σs et σt SIM.
  pfold. punfold SIM; [|apply sim_fn_body_mono].
  inversion SIM; subst.
  - by eapply sim_fn_body_stuck.
  - eapply sim_fn_body_step.
    intros et' ct' STEP'.
    destruct (STEP _ _ STEP') as (es' & cs' & STEPS' & SIM').
    exists es', cs'. split; [done|].
    right. eapply CIH; eauto. by inversion SIM'.
  - eapply sim_fn_body_step_over_call; eauto.
    intros vs vt r' cs' ct' VAL WSAT VREL.
    specialize (RET _ _ _ _ _ VAL WSAT VREL).
    right. eapply CIH; [eauto|by inversion RET].
  - eapply sim_fn_body_end_call.
    intros ct' STEP'. destruct (GUAR _ STEP') as (es' & r' & STEPS' & VAL & WSAT & VREL).
    naive_solver.
Qed.

End local.

Hint Resolve sim_fn_body_mono : paco.

Section invariant.
  Context {A: cmraT}.
  Definition wsat (σGAll: A) (σ_src σ_tgt: state) : Prop := True.

  Definition local_inv (σG: A)
    (c_src: call_id) (cids_entry_src: call_id_stack) (σ_src: state)
    (c_tgt: call_id) (cids_entry_tgt: call_id_stack) (σ_tgt: state) : Prop := True.
End invariant.
