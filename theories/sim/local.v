From Paco Require Export paco.
From iris.algebra Require Import cmra gmap csum agree excl.

From stbor.lang Require Import defs.

Set Default Proof Using "Type".

Section local.
Context {A: ucmraT}.
Variable (wsat: A → state → state → Prop).
Variable (vrel: A → expr → expr → Prop).
Variable (fns fnt: fn_env).

Inductive _sim_local_body
  (sim_local_body : A → nat → expr → state → expr → state → Prop)
  (r: A) (idx: nat) : expr → state → expr → state → Prop :=
(* If src is stuck, then anything is related *)
| sim_local_body_stuck e_src σ_src e_tgt σ_tgt
    (STUCK: stuck (Λ:=bor_lang fns) e_src σ_src)
    : _sim_local_body sim_local_body r idx e_src σ_src e_tgt σ_tgt
(* If tgt makes 1 step, src can make some step *)
| sim_local_body_step e_src σ_src e_tgt σ_tgt
    (STEP: ∀ r_f e_tgt' σ_tgt'
      (* for any frame r_f that is compatible with our resource r *)
      (VALID: ✓ (r_f ⋅ r))
      (* and has world satisfaction *)
      (WSAT: wsat (r_f ⋅ r) σ_src σ_tgt)
      (* if tgt can locally make 1 step *)
      (STEPT: (e_tgt, σ_tgt) ~{fnt}~> (e_tgt', σ_tgt')),
      (* then we locally can makes some step and pick a new resource r' *)
      ∃ e_src' σ_src' r' idx',
        ((e_src, σ_src) ~{fns}~>+ (e_src', σ_src') ∨
         ((idx' < idx)%nat ∧ (e_src', σ_src') = (e_src, σ_src))) ∧
        ✓ (r_f ⋅ r') ∧ wsat (r_f ⋅ r') σ_src' σ_tgt' ∧
        sim_local_body r' idx' e_src' σ_src' e_tgt' σ_tgt')
    : _sim_local_body sim_local_body r idx e_src σ_src e_tgt σ_tgt
(* If tgt prepares to make a call to [name], src should be able to make the same
  call. Here we do not want to step into the call of [name], but to step over it. *)
| sim_local_body_step_over_call
    (K_src: list (ectxi_language.ectx_item (bor_ectxi_lang fns)))
    (K_tgt: list (ectxi_language.ectx_item (bor_ectxi_lang fnt)))
    fid e_src e_tgt el_tgt σ_src σ_tgt
    (CALLTGT: e_tgt = fill K_tgt (Call #[ScFnPtr fid] el_tgt))
    (STEPOVER: ∀ r_f
        (* for any frame r_f that is compatible with our resource r *)
        (VALID: ✓ (r_f ⋅ r))
        (* and has world satisfaction *)
        (WSAT : wsat (r_f ⋅ r) σ_src σ_tgt)
        (* tgt is ready to make a call of [name] *)
        (VTGT : Forall (λ ei, is_Some (to_value ei)) el_tgt),
        (* then src is also ready to make a call of [name] *)
        ∃ el_src σ1_src rc rv,
        (e_src, σ_src) ~{fns}~>*
          (fill K_src (Call #[ScFnPtr fid] el_src), σ1_src) ∧
        Forall (λ ei, is_Some (to_value ei)) el_src ∧
        (* and we can pick a resource [rv] for the arguments *)
        ✓ (r_f ⋅ (rc ⋅ rv)) ∧ wsat (r_f ⋅ (rc ⋅ rv)) σ1_src σ_tgt ∧
        (* [rv] justifies the arguments *)
        Forall2 (vrel rv) el_src el_tgt ∧
        (* and after the call our context can continue *)
        (∀ r_f' r' v_src v_tgt σ_src' σ_tgt'
          (* For any new resource r' and frame r_f' that are compatible with
             our local resource r and have world satisfaction *)
          (VALID': ✓ (r_f' ⋅ (rc ⋅ r')))
          (WSAT' : wsat (r_f ⋅ (rc ⋅ r')) σ_src' σ_tgt')
          (* and the returned values are related w.r.t. (r ⋅ r' ⋅ r_f) *)
          (VRET  : vrel r' (Val v_src) (Val v_tgt)),
          ∃ idx', sim_local_body (rc ⋅ r') idx'
                                  (fill K_src (Val v_src)) σ_src'
                                  (fill K_tgt (Val v_tgt)) σ_tgt'))
    : _sim_local_body sim_local_body r idx e_src σ_src e_tgt σ_tgt
(* If tgt prepares to end, src also prepares to end *)
| sim_local_body_end_call v_src σ_src v_tgt σ_tgt e_src e_tgt
    (ESRC: e_src = EndCall (Val v_src))
    (ETGT: e_tgt = EndCall (Val v_tgt))
    (END: ∀ r_f eσ_tgt'
        (VALID: ✓ (r_f ⋅ r))
        (WSAT : wsat (r_f ⋅ r) σ_src σ_tgt)
        (* if tgt can end call *)
        (ETGT: (EndCall (Val v_tgt), σ_tgt) ~{fnt}~> eσ_tgt'),
        (* then src can also end call *)
        ∃ eσ_src' r',
        (EndCall (Val v_src), σ_src) ~{fns}~> eσ_src' ∧
        (* and re-establish wsat *)
        ✓ (r_f ⋅ r') ∧ wsat (r_f ⋅ r') eσ_src'.2 eσ_tgt'.2 ∧
        (* and the returned values are related *)
        vrel r' (Val v_src) (Val v_tgt))
    : _sim_local_body sim_local_body r idx e_src σ_src e_tgt σ_tgt
.

Lemma sim_local_body_mono : monotone6 _sim_local_body.
Proof.
  intros r idx es σs et σt R R' SIM LE; inversion SIM; subst.
  - by eapply sim_local_body_stuck; eauto.
  - eapply sim_local_body_step. naive_solver.
  - eapply sim_local_body_step_over_call; eauto. naive_solver.
  - by eapply sim_local_body_end_call; eauto.
Qed.

Definition sim_local_body := paco6 _sim_local_body bot6.

Lemma sim_local_body_resource_mono r1 r2
  (SAT_DOWNWARD: ∀ r1 r2, r1 ≼ r2 → wsat r2 <2= wsat r1) :
  r1 ≼ r2 → sim_local_body r1 <5= sim_local_body r2.
Proof.
  revert r1 r2. pcofix CIH. intros r1 r2 LE idx es σs et σt SIM.
  pfold. punfold SIM; [|apply sim_local_body_mono].
  inversion SIM; subst.
  - by eapply sim_local_body_stuck.
  - eapply sim_local_body_step.
    intros r_f et' ct' VL2 WS2 STEPT.
    have VL1: ✓ (r_f ⋅ r1).
    { eapply cmra_valid_included; [exact VL2|by apply cmra_mono_l]. }
    have WS1: wsat (r_f ⋅ r1) σs σt.
    { eapply SAT_DOWNWARD; [by apply cmra_mono_l|exact WS2]. }
    destruct (STEP _ _ _ VL1 WS1 STEPT) as
      (es' & cs' & r' & idx' & STEPS' & VL' & WS' & SIM').
    exists es', cs', r', idx'. do 3 (split; [done|]).
    right. eapply CIH; eauto. by inversion SIM'.
  - eapply sim_local_body_step_over_call; eauto.
    intros r_f VL2 WS2 FAT.
    have VL1: ✓ (r_f ⋅ r1).
    { eapply cmra_valid_included; [exact VL2|by apply cmra_mono_l]. }
    have WS1: wsat (r_f ⋅ r1) σs σt.
    { eapply SAT_DOWNWARD; [by apply cmra_mono_l|exact WS2]. }
    destruct (STEPOVER _ VL1 WS1 FAT)
      as (es' & cs & rc & rv & STEPS & FAS & VL & WS & VREL & HK).
    exists es', cs, rc, rv. do 5 (split; [done|]).
    intros r_f' r' vs vt cs' ct' VL' WS' VREL'.
    destruct (HK _ _ _ _ _ _ VL' WS' VREL') as [idx' HK2].
    exists idx'. right. eapply CIH; [eauto|by inversion HK2].
  - eapply sim_local_body_end_call; [eauto..|].
    intros r_f ct' VL2 WS2 STEPT.
    have VL1: ✓ (r_f ⋅ r1).
    { eapply cmra_valid_included; [exact VL2|by apply cmra_mono_l]. }
    have WS1: wsat (r_f ⋅ r1) σs σt.
    { eapply SAT_DOWNWARD; [by apply cmra_mono_l|exact WS2]. }
    naive_solver.
Qed.

(* Simulating functions: assuming the calls have been initialized. *)
Definition sim_local_fun (fn_src fn_tgt : function) : Prop :=
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
    ∃ idx, sim_local_body r idx (InitCall e_src) σ_src (InitCall e_tgt) σ_tgt.

Definition sim_local_funs : Prop :=
  ∀ name fn_src, fns !! name = Some fn_src → ∃ fn_tgt,
    fnt !! name = Some fn_tgt ∧ sim_local_fun fn_src fn_tgt.

End local.

Hint Resolve sim_local_body_mono : paco.

Definition init_state := (mkState ∅ ∅ [] O O).

Section program.
Context {A: ucmraT}.
Variable (wsat: A → state → state → Prop).
Variable (vrel: A → expr → expr → Prop).

(* Program simulation: All functions are related, and so is initialization. *)
Record sim_prog (prog_src prog_tgt: fn_env) := {
  sim_prog_env: sim_local_funs wsat vrel prog_src prog_tgt;
  sim_prog_main:
    ∃ idx, sim_local_body wsat vrel prog_src prog_tgt ε idx
                          (Call #["main"] []) init_state
                          (Call #["main"] []) init_state;
}.
End program.
