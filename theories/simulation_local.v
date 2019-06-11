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