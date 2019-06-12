From Paco Require Import paco.
From iris.algebra Require Import cmra.

From stbor Require Import simulation.

Section local.
Context {A: ucmraT}.
Variable (Φ: A → state → state → Prop).
Variable (fns_src fns_tgt: fn_env).
Variable (cids_entry_src cids_entry_tgt: call_id_stack) (c_src c_tgt: call_id).

(* (* For any frame ghost gσ_f that is compatible with our local ghost gσ *)
      ✓ (gσ ⋅ gσ_f) →
      (* and our invariant Φ holds for the composed ghost + pair of physical states, *)
      Φ (gσ ⋅ gσ_f) σ_src σ_tgt → *)

(* TODO: encode what it means for the context to not contain our private tags! *)
(* TODO: how do we know we're at the top of the stack? *)
Inductive _sim_local
  (sim_local : A → A → expr → state → expr → state → Prop)
  (gσ_f gσ: A) : expr → state → expr → state → Prop :=
(* If src is stuck, then anything is related *)
| sim_local_stuck e_src σ_src e_tgt σ_tgt
    (STUCK: stuck e_src (mkConfig fns_src σ_src))
    : _sim_local sim_local gσ_f gσ e_src σ_src e_tgt σ_tgt
(* If tgt makes 1 step, src can make some step *)
| sim_local_step e_src σ_src e_tgt σ_tgt
    (STEP: ∀ e_tgt' cfg_tgt',
      (* if tgt can makes 1 step *)
      (e_tgt, (mkConfig fns_tgt σ_tgt)) ~t~> (e_tgt', cfg_tgt') →
      (* then we locally can makes some step and still preserve the frame gσ_f
        and the invariant Φ, and the simulation continues. *)
      ∃ e_src' cfg_src' gσ',
        (e_src, (mkConfig fns_src σ_src)) ~t~>* (e_src', cfg_src') ∧
        ✓ (gσ' ⋅ gσ_f) ∧ Φ (gσ' ⋅ gσ_f) cfg_src'.(cst) cfg_tgt'.(cst) ∧
        sim_local gσ_f gσ' e_src' cfg_src'.(cst) e_tgt' cfg_tgt'.(cst))
    : _sim_local sim_local gσ_f gσ e_src σ_src e_tgt σ_tgt
(* If tgt prepares to make a call to [name], src should be able to make the same
  call. Here we do not want to step into the call of [name], but to step over
  it. To make the call, we need to re-establish the invariant
  `Φ (gσ ⋅ gσ_f) cfg_src.(cst) σ_tgt`. Then after the call we can assume that:
  - the context K_src/tgt did not change
  - the call id stack did not change
  - the private ghost gσ did not change
  - the invariant is re-established by [name] for some new frame and new states. *)
| sim_local_step_over_call K_src K_tgt name e_src el_src el_tgt σ_src
    cfg_src σ_tgt
    (STEPS: (e_src, (mkConfig fns_src σ_src)) ~t~>*
            (fill K_src (Call #(LitFnPtr name) el_src), cfg_src))
    (VALS: Forall (λ ei, terminal ei) el_src)
    (VALT: Forall (λ ei, terminal ei) el_tgt)
    (VALEQ: Forall2 sim_expr_terminal el_src el_tgt)
    (VALID: ✓ (gσ ⋅ gσ_f))
    (INV: Φ (gσ ⋅ gσ_f) cfg_src.(cst) σ_tgt)
    (RET: ∀ v gσ_f' cfg_src' cfg_tgt',
      (* For any new frame ghost gσ_f' that is compatible with our local ghost gσ and frame gσ_f *)
      ✓ (gσ ⋅ gσ_f ⋅ gσ_f') →
      (* and our invariant Φ holds for the composed ghost + pair of physical states, *)
      Φ (gσ ⋅ gσ_f ⋅ gσ_f') cfg_src'.(cst) cfg_tgt'.(cst) →
      (* stack unchanged *)
      cfg_src'.(cst).(scs) = cfg_src.(cst).(scs) →
      cfg_tgt'.(cst).(scs) = σ_tgt.(scs) →
      sim_local (gσ_f ⋅ gσ_f') gσ
                (fill K_src (of_val v)) cfg_src'.(cst)
                (fill K_tgt (of_val v)) cfg_tgt'.(cst))
    : _sim_local sim_local gσ_f gσ e_src σ_src
        (fill K_tgt (Call #(LitFnPtr name) el_tgt)) σ_tgt
(* If tgt prepares to return, src also prepares to return *)
| sim_local_end_call e_src σ_src cfg_src v_src v_tgt σ_tgt
    (STEPS: (e_src, (mkConfig fns_src σ_src)) ~t~>* (EndCall v_src, cfg_src))
    (TERMS: terminal v_src)
    (TERMT: terminal v_tgt)
    (VALEQ: sim_expr_terminal v_src v_tgt)
    (CIDS: cfg_src.(cst).(scs) = c_src :: cids_entry_src)
    (CIDT: σ_tgt.(scs) = c_tgt :: cids_entry_src)
    (GUAR: ∀ cfg_src' cfg_tgt',
            (EndCall v_src, cfg_src) ~t~> cfg_src' →
            (EndCall v_tgt, (mkConfig fns_tgt σ_tgt)) ~t~> cfg_tgt' →
            ∃ gσ', ✓ (gσ' ⋅ gσ_f) ∧ Φ (gσ' ⋅ gσ_f) cfg_src'.2.(cst) cfg_tgt'.2.(cst))
    : _sim_local sim_local gσ_f gσ e_src σ_src (EndCall v_tgt) σ_tgt
.

Lemma sim_local_mono : monotone6 _sim_local.
Proof.
  intros gσ_f gσ es σs et σt r r' SIM LE; inversion SIM; subst.
  - by eapply sim_local_stuck.
  - eapply sim_local_step. intros et' cfgt' STEPT.
    destruct (STEP _ _ STEPT) as (es' & cfgs' & gσ' & STEPS & VAL' & INV' & Hr).
    naive_solver.
  - eapply sim_local_step_over_call; eauto.
  - eapply sim_local_end_call; eauto.
Qed.

Definition sim_local := paco6 _sim_local bot6.

End local.

(** Thread simulation *)

(* Target is simulated by source.
  Adequacy should states that any defined behavior by target is also a defined
  behavior by source. In the proof of optimizations, we pick target to be the
  optimized version, and source to be the unoptimized one.
  This simulation is goal-based, ie. it does not have intermediate observation,
  and the simulation finalizes at the simulation `sim_terminal` between the
  non-reducible values.
  The values can contain any observations of the states in between by reading
  the memory. Thus the simulation maintains the relation `sim_state` between
  the states. *)

Definition sim_lit (v1: lit) (v2: lit) :=
  match v1, v2 with
  | LitPoison, LitPoison => True
  | LitInt n1, LitInt n2 => n1 = n2
  | LitLoc l1 bor1, LitLoc l2 bor2 => (* FIXME *) l1 = l2 ∧ bor1 = bor2
  | LitCall c1, LitCall c2 => c1 = c2
  | LitFnPtr fptr1, LitFnPtr fptr2 => (* FIXME *) fptr1 = fptr2
  | _,_ => False
  end.

Section ghost.
Context {A: Type}.

Notation SIM_MEM := (A → state → state → Prop)%type.
Variable (Φ: A → expr * state → expr * state → A → expr * state → expr * state → Prop)
         (sim_mem: SIM_MEM).

Inductive sim_state (σG: A) (σ_src σ_tgt: state) : Prop :=
| SimState
  (MDOM: dom (gset loc) σ_src.(cst).(shp) ≡ dom (gset loc) σ_tgt.(cst).(shp))
  (SMEM: sim_mem σG σ_src σ_tgt)
  (SSTK: σ_src.(cst).(sst) = σ_tgt.(cst).(sst))
  (SPRO: σ_src.(cst).(spr) = σ_tgt.(cst).(spr))
  (SCLK : σ_src.(cst).(scn) = σ_tgt.(cst).(scn))
  (* (SFNS: what? *)
.

Definition _sim
  (sim : SIM_CONFIG) (σG: A) (eσ1_src eσ1_tgt: expr * state) : Prop :=
  Wf eσ1_src.2 → Wf eσ1_tgt.2 → sim_state σG eσ1_src.2 eσ1_tgt.2 →
  (* If [eσ1_src] gets UB, we can have UB in the target, thus any [eσ1_tgt] is
      acceptable. Otherwise ... *)
  ¬ (∀ eσ', eσ1_src ~t~>* eσ' → stuck eσ'.1 eσ'.2) →
  (* (1) If [eσ1_tgt] gets stuck, [eσ1_src] can also get stuck. *)
  (stuck eσ1_tgt.1 eσ1_tgt.2 → ∃ eσ2_src,
    eσ1_src ~t~>* eσ2_src ∧ stuck eσ2_src.1 eσ2_src.2) ∧
  (* (2) If [eσ1_tgt] diverges, then [eσ1_src] diverges. *)
  (diverges tstep eσ1_tgt → diverges tstep eσ1_src) ∧
  (* (3) If [eσ1_tgt] is terminal, then [eσ1_src] terminates with some steps. *)
  (terminal eσ1_tgt.1 → ∃ eσ2_src σG',
    eσ1_src ~t~>* eσ2_src ∧ terminal eσ2_src.1 ∧
    sim_val_expr eσ2_src.1 eσ1_tgt.1 ∧
    sim_state σG' eσ2_src.2 eσ1_tgt.2 ∧ Φ σG eσ1_src eσ1_tgt σG' eσ2_src eσ1_tgt) ∧
  (* (4) If [eσ1_tgt] steps to [eσ2_tgt] with 1 step,
       then exists [eσ2_src] s.t. [eσ1_src] steps to [eσ2_src] with * step. *)
  (∀ eσ2_tgt, eσ1_tgt ~t~> eσ2_tgt → ∃ eσ2_src σG',
      eσ1_src ~t~>* eσ2_src ∧
      sim_state σG' eσ2_src.2 eσ2_tgt.2 ∧ Φ σG eσ1_src eσ1_tgt σG' eσ2_src eσ2_tgt ∧
      sim σG' eσ2_src eσ2_tgt)
  .

Lemma _sim_mono : monotone3 (_sim).
Proof.
  intros σG eσ_src eσ_tgt r r' TS LE WF1 WF2 SS NS.
  destruct (TS WF1 WF2 SS NS) as (SU & DI & TE & ST). repeat split; auto.
  intros eσ2_tgt ONE. destruct (ST _ ONE) as (eσ2_src & σG' & STEP1 & SS1 & HΦ & Hr).
  exists eσ2_src, σG'. do 3 (split; [done|]). by apply LE.
Qed.

(* Actual simulation *)
Definition sim : SIM_CONFIG := paco3 _sim bot3.
End ghost.

Hint Resolve _sim_mono: paco.