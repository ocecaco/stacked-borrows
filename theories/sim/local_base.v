From Paco Require Import paco.
From iris.algebra Require Import cmra gmap csum agree excl.

From stbor.lang Require Import defs.

Set Default Proof Using "Type".

Section local.
Context {A: ucmraT}.
Variable (wsat: A → state → state → Prop).
Variable (vrel: A → expr → expr → Prop).
Variable (fns_src fns_tgt: fn_env).

(* TODO: encode what it means for the context to not contain our private tags! *)
(* TODO: how do we know we're at the top of the stack? *)
Inductive _sim_fn_body
  (sim_fn_body : A → expr → state → expr → state → Prop)
  (r: A) : expr → state → expr → state → Prop :=
(* If src is stuck, then anything is related *)
| sim_fn_body_stuck e_src σ_src e_tgt σ_tgt
    (STUCK: stuck e_src (mkConfig fns_src σ_src))
    : _sim_fn_body sim_fn_body r e_src σ_src e_tgt σ_tgt
(* If tgt makes 1 step, src can make some step *)
| sim_fn_body_step e_src σ_src e_tgt σ_tgt
    (STEP: ∀ r_f e_tgt' cfg_tgt',
      (* for any frame r_f that is compatible with our resource r and has world satisfaction *)
      ✓ (r_f ⋅ r) →
      wsat (r_f ⋅ r) σ_src σ_tgt →
      (* if tgt can locally make 1 step *)
      (e_tgt, (mkConfig fns_tgt σ_tgt)) ~t~> (e_tgt', cfg_tgt') →
      (* then we locally can makes some step and pick a new resource r' *)
      ∃ e_src' cfg_src' r',
        (e_src, (mkConfig fns_src σ_src)) ~t~>* (e_src', cfg_src') ∧
        ✓ (r_f ⋅ r') ∧ wsat (r_f ⋅ r') cfg_src'.(cst) cfg_tgt'.(cst) ∧
        sim_fn_body r' e_src' cfg_src'.(cst) e_tgt' cfg_tgt'.(cst))
    : _sim_fn_body sim_fn_body r e_src σ_src e_tgt σ_tgt
(* If tgt prepares to make a call to [name], src should be able to make the same
  call. Here we do not want to step into the call of [name], but to step over it. *)
| sim_fn_body_step_over_call K_src K_tgt name e_src el_tgt σ_src σ_tgt
    (STEPOVER: ∀ r_f,
        (* for any frame r_f that is compatible with our resource r and has world satisfaction *)
        ✓ (r_f ⋅ r) → wsat (r_f ⋅ r) σ_src σ_tgt →
        (* tgt is ready to make a call of [name] *)
        Forall (λ ei, is_Some (to_value ei)) el_tgt →
        (* then src is also ready to make a call of [name] *)
        ∃ el_src cfg_src rc rv,
        (e_src, (mkConfig fns_src σ_src)) ~t~>*
          (fill K_src (Call #[ScFnPtr name] el_src), cfg_src) ∧
        Forall (λ ei, is_Some (to_value ei)) el_src ∧
        (* and we can pick a resource [rv] for the arguments *)
        ✓ (r_f ⋅ (rc ⋅ rv)) ∧ wsat (r_f ⋅ (rc ⋅ rv)) cfg_src.(cst) σ_tgt ∧
        (* [rv] justifies the arguments *)
        Forall2 (vrel rv) el_src el_tgt ∧
        (* and after the call our context can continue *)
        (∀ r_f' r' v_src v_tgt cfg_src' cfg_tgt',
          (* For any new resource r' and frame r_f' that are compatible with
             our local resource r and has world satisfaction *)
          ✓ (r_f' ⋅ (rc ⋅ r')) →
          wsat (r_f ⋅ (rc ⋅ r')) cfg_src'.(cst) cfg_tgt'.(cst) →
          (* and the returned values are related w.r.t. (r ⋅ r' ⋅ r_f) *)
          vrel r' (Val v_src) (Val v_tgt) →
          (* (* stack unchanged *)
          cfg_src'.(cst).(scs) = cfg_src.(cst).(scs) →
          cfg_tgt'.(cst).(scs) = σ_tgt.(scs) → *)
          sim_fn_body (rc ⋅ r')
                      (fill K_src (Val v_src)) cfg_src'.(cst)
                      (fill K_tgt (Val v_tgt)) cfg_tgt'.(cst)))
    : _sim_fn_body sim_fn_body r e_src σ_src
        (fill K_tgt (Call #[ScFnPtr name] el_tgt)) σ_tgt
(* If tgt prepares to end, src also prepares to end *)
| sim_fn_body_end_call v_src σ_src v_tgt σ_tgt
    (GUAR: ∀ r_f cfg_tgt',
        ✓ (r_f ⋅ r) → wsat (r_f ⋅ r) σ_src σ_tgt →
        (* if tgt can end call *)
        (EndCall (Val v_tgt), (mkConfig fns_tgt σ_tgt)) ~t~> cfg_tgt' →
        (* then src can also end call *)
        ∃ cfg_src' r',
        (EndCall (Val v_src), (mkConfig fns_src σ_tgt)) ~t~> cfg_src' ∧
        (* and re-establish wsat *)
        ✓ (r_f ⋅ r') ∧ wsat (r_f ⋅ r') cfg_src'.2.(cst) cfg_tgt'.2.(cst) ∧
        (* and the returned values are related *)
        vrel r' (Val v_src) (Val v_tgt)
        (* (* and call id stacks are restored *)
        cfg_src'.2.(cst).(scs) = cids_entry_src ∧
        cfg_tgt'.2.(cst).(scs) = cids_entry_tgt  *))
    : _sim_fn_body sim_fn_body r (EndCall (Val v_src)) σ_src (EndCall (Val v_tgt)) σ_tgt
.

Lemma sim_fn_body_mono : monotone5 _sim_fn_body.
Proof.
  intros r es σs et σt R R' SIM LE; inversion SIM; subst.
  - by eapply sim_fn_body_stuck; eauto.
  - eapply sim_fn_body_step. naive_solver.
  - eapply sim_fn_body_step_over_call; eauto. naive_solver.
  - by eapply sim_fn_body_end_call; eauto.
Qed.

Definition sim_fn_body := paco5 _sim_fn_body bot5.

Lemma sim_fn_body_resource_mono r1 r2
  (SAT_DOWNWARD: ∀ r1 r2, r1 ≼ r2 → wsat r2 <2= wsat r1) :
  r1 ≼ r2 → sim_fn_body r1 <4= sim_fn_body r2.
Proof.
  revert r1 r2. pcofix CIH. intros r1 r2 LE es σs et σt SIM.
  pfold. punfold SIM; [|apply sim_fn_body_mono].
  inversion SIM; subst.
  - by eapply sim_fn_body_stuck.
  - eapply sim_fn_body_step.
    intros r_f et' ct' VL2 WS2 STEPT.
    have VL1: ✓ (r_f ⋅ r1).
    { eapply cmra_valid_included; [exact VL2|by apply cmra_mono_l]. }
    have WS1: wsat (r_f ⋅ r1) σs σt.
    { eapply SAT_DOWNWARD; [by apply cmra_mono_l|exact WS2]. }
    destruct (STEP _ _ _ VL1 WS1 STEPT) as (es' & cs' & r' & STEPS' & VL' & WS' & SIM').
    exists es', cs', r'. do 3 (split; [done|]).
    right. eapply CIH; eauto. by inversion SIM'.
  - eapply sim_fn_body_step_over_call; eauto.
    intros r_f VL2 WS2 FAT.
    have VL1: ✓ (r_f ⋅ r1).
    { eapply cmra_valid_included; [exact VL2|by apply cmra_mono_l]. }
    have WS1: wsat (r_f ⋅ r1) σs σt.
    { eapply SAT_DOWNWARD; [by apply cmra_mono_l|exact WS2]. }
    destruct (STEPOVER _ VL1 WS1 FAT)
      as (es' & cs & rc & rv & STEPS & FAS & VL & WS & VREL & HK).
    exists es', cs, rc, rv. do 5 (split; [done|]).
    intros r_f' r' vs vt cs' ct' VL' WS' VREL'.
    specialize (HK _ _ _ _ _ _ VL' WS' VREL').
    right. eapply CIH; [eauto|by inversion HK].
  - eapply sim_fn_body_end_call.
    intros r_f ct' VL2 WS2 STEPT.
    have VL1: ✓ (r_f ⋅ r1).
    { eapply cmra_valid_included; [exact VL2|by apply cmra_mono_l]. }
    have WS1: wsat (r_f ⋅ r1) σs σt.
    { eapply SAT_DOWNWARD; [by apply cmra_mono_l|exact WS2]. }
    naive_solver.
Qed.

(* Simulating functions: assuming the calls have been initialized. *)
Definition sim_local_fn (fn_src fn_tgt : function) : Prop :=
  ∀ r e_src e_tgt el_src el_tgt σ_src σ_tgt
    (VALS: Forall (λ ei, is_Some (to_value ei)) el_src)
    (VALT: Forall (λ ei, is_Some (to_value ei)) el_tgt)
    (VALEQ: Forall2 (vrel r) el_src el_tgt)
    (EQS: match fn_src with
          | FunV xl e => subst_l xl el_src e = Some e_src
          end)
    (EQT: match fn_tgt with
          | FunV xl e => subst_l xl el_tgt e = Some e_tgt
          end),
    sim_fn_body r (InitCall e_src) σ_src (InitCall e_tgt) σ_tgt.

Definition sim_local_fns : Prop :=
  ∀ name fn_src, fns_src !! name = Some fn_src → ∃ fn_tgt,
    fns_tgt !! name = Some fn_tgt ∧ sim_local_fn fn_src fn_tgt.

End local.

Hint Resolve sim_fn_body_mono : paco.
