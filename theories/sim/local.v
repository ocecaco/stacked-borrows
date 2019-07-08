From Paco Require Export paco.
From iris.algebra Require Import cmra gmap csum agree excl.

From stbor.lang Require Import defs.
From stbor.sim Require Import sflib.

Set Default Proof Using "Type".

Section local.
Context {A: ucmraT}.
Variable (wsat: A → state → state → Prop).
Variable (vrel: A → value → value → Prop).
Variable (fs ft: fn_env).

Definition rrel (r: A) rs rt: Prop :=
  match rs, rt with
  | ValR vs, ValR vt => vrel r vs vt
  | PlaceR ls ts Ts, PlaceR lt t_t Tt =>
    (* Places are related like pointers, and the types must be equal. *)
    vrel r [ScPtr ls ts] [ScPtr lt t_t] ∧ Ts = Tt
  | _, _ => False
  end.

Notation PRED := (A → nat → result → state → result → state → Prop)%type.
Notation SIM := (A → nat → expr → state → expr → state → PRED → Prop)%type.

Implicit Type (Φ: PRED).

Inductive _sim_local_body_step (r_f : A) (sim_local_body : SIM)
  (r: A) (idx: nat) es σs et σt Φ : Prop :=
(* If tgt makes 1 step, src can make some step *)
| sim_local_body_step_next
    (STEP: ∀ et' σt' (STEPT: (et, σt) ~{ft}~> (et', σt')),
      (* then we locally can makes some step and pick a new resource r' *)
      ∃ es' σs' r' idx',
        ((es, σs) ~{fs}~>+ (es', σs') ∨
         ((idx' < idx)%nat ∧ (es', σs') = (es, σs))) ∧
        wsat (r_f ⋅ r') σs' σt' ∧
        sim_local_body r' idx' es' σs' et' σt' Φ)
(* If tgt prepares to make a call to [name], src should be able to make the same
  call. Here we do not want to step into the call of [name], but to step over it. *)
| sim_local_body_step_over_call
    (Ks: list (ectxi_language.ectx_item (bor_ectxi_lang fs)))
    (Kt: list (ectxi_language.ectx_item (bor_ectxi_lang ft)))
    fid (vl_tgt: list result)
    (vl_src: list result) σ1_src
    rc rv
    (* tgt is ready to make a call of [name] *)
    (CALLTGT: et = fill Kt (Call #[ScFnPtr fid] (of_result <$> vl_tgt)))
    (* src is ready to make a call of [name] *)
    (CALLSRC: (es, σs) ~{fs}~>* (fill Ks (Call #[ScFnPtr fid] (of_result <$> vl_src)), σ1_src))
    (* and we can pick a resource [rv] for the arguments *)
    (WSAT: wsat (r_f ⋅ (rc ⋅ rv)) σ1_src σt)
    (* [rv] justifies the arguments *)
    (VREL: Forall2 (rrel rv) vl_src vl_tgt)
    (* and after the call our context can continue *)
    (CONT: ∀ r' v_src v_tgt σs' σt'
             (* For any new resource r' that supports the returned values are
                related w.r.t. r' *)
             (VRET: vrel r' v_src v_tgt)
             (WSAT: wsat (r_f ⋅ (rc ⋅ r')) σs' σt')
             (STACK: σt.(scs) = σt'.(scs)),
        ∃ idx', sim_local_body (rc ⋅ r') idx'
                               (fill Ks (Val v_src)) σs'
                               (fill Kt (Val v_tgt)) σt' Φ).

Record sim_local_body_base (r_f: A) (sim_local_body : SIM)
  (r: A) (idx: nat) es σs et σt Φ : Prop := {
  sim_local_body_stuck :
    (terminal et ∨ reducible ft et σt) ;
  sim_local_body_terminal :
    (* if tgt is terminal *)
    ∀ vt (TERM: to_result et = Some vt),
      (* then src can get terminal *)
      ∃ vs' σs' r', (es, σs) ~{fs}~>* (of_result vs', σs') ∧
        (* and re-establish wsat *)
        wsat (r_f ⋅ r') σs' σt ∧ Φ r' idx vs' σs' vt σt ;
  sim_local_body_step :
      _sim_local_body_step r_f sim_local_body r idx es σs et σt Φ
}.

Definition _sim_local_body (sim_local_body : SIM)
  (r: A) (idx: nat) es σs et σt Φ : Prop :=
  (* assuming that src cannot get stuck *)
  ∀ (NEVER_STUCK: never_stuck fs es σs)
    (* for any frame r_f that is compatible with our resource r has world satisfaction *)
    r_f (WSAT: wsat (r_f ⋅ r) σs σt),
    sim_local_body_base r_f sim_local_body r idx es σs et σt Φ.

Lemma sim_local_body_mono : monotone7 _sim_local_body.
Proof.
  intros r idx es σs et σt Φ R R' SIM LE NT r_f WSAT.
  destruct (SIM NT _ WSAT) as [NS TM ST]. split; [naive_solver|naive_solver|].
  inversion ST; subst.
  - constructor 1. naive_solver.
  - econstructor 2; eauto. naive_solver.
Qed.

Definition sim_local_body := paco7 _sim_local_body bot7.

Lemma sim_local_body_post_mono r n es σs et σt Φ Φ' :
  Φ <6= Φ' →
  sim_local_body r n es σs et σt Φ → sim_local_body r n es σs et σt Φ'.
Proof.
  revert r n es σs et σt Φ Φ'. pcofix CIH. intros r0 n es σs et σt Φ Φ' LE SIM.
  pfold. punfold SIM; [|apply sim_local_body_mono].
  intros NT r_f WSAT. specialize (SIM NT r_f WSAT) as [NOTS TE SIM].
  constructor; [done|..].
  { intros.
    destruct (TE _ TERM) as (vs' & σs' & r' & STEP' & WSAT' & HΦ).
    naive_solver. }
  inversion SIM.
  - left. intros.
    specialize (STEP _ _ STEPT) as (es' & σs' & r' & idx' & STEP' & WSAT' & SIM').
    exists es', σs', r', idx'. do 2 (split; [done|]).
    pclearbot. right. eapply CIH; eauto.
  - econstructor 2; eauto. intros r' vs vt σs' σt' VRET WSAT1 STACK.
    destruct (CONT _ _ _ σs' σt' VRET WSAT1 STACK) as [idx' SIM'].
    exists idx'. pclearbot. right. eapply CIH; eauto.
Qed.

(** Simulating functions:
  - We start after the substitution.
  - We assume the arguments are results related by [r]
  - The returned result must also be related by [rrel].
This is called "local" because it considers one function at a time.
However, it does assume full knowledge about the GLOBAL function table! *)
Definition fun_post (esat: A → call_id → Prop) initial_call_id_stack
  (r: A) (n: nat) rs (σs: state) rt σt :=
  (∃ c, σt.(scs) = c :: initial_call_id_stack ∧ esat r c) ∧
  rrel r rs rt.
Definition sim_local_fun
  (esat: A → call_id → Prop) (fn_src fn_tgt : function) : Prop :=
  ∀ r es et (vl_src vl_tgt: list value) σs σt
    (VALEQ: Forall2 (vrel r) vl_src vl_tgt)
    (EQS: subst_l fn_src.(fun_args) (Val <$> vl_src) fn_src.(fun_body) = Some es)
    (EQT: subst_l fn_tgt.(fun_args) (Val <$> vl_tgt) fn_tgt.(fun_body) = Some et),
    ∃ idx, sim_local_body r idx
                          (InitCall es) σs (InitCall et) σt
                          (fun_post esat σt.(scs)).

Definition sim_local_funs (esat: A → call_id → Prop) : Prop :=
  ∀ name fn_src, fs !! name = Some fn_src → ∃ fn_tgt,
    ft !! name = Some fn_tgt ∧
    length fn_src.(fun_args) = length fn_tgt.(fun_args) ∧
    sim_local_fun esat fn_src fn_tgt.

Definition sim_local_funs_lookup : Prop :=
  ∀ name fn_src, fs !! name = Some fn_src → ∃ fn_tgt,
    ft !! name = Some fn_tgt ∧
    length fn_src.(fun_args) = length fn_tgt.(fun_args).

Lemma sim_local_funs_to_lookup esat :
  sim_local_funs esat → sim_local_funs_lookup.
Proof.
  intros Hlf name fns Hlk. destruct (Hlf _ _ Hlk) as (fnt & ? & ? & ?).
  eauto.
Qed.

(** Viewshift *)
Definition viewshift (r1 r2: A) : Prop :=
  ∀ r_f σs σt, wsat (r_f ⋅ r1) σs σt → wsat (r_f ⋅ r2) σs σt.

Lemma viewshift_sim_local_body r1 r2 n es σs et σt Φ :
  viewshift r1 r2 →
  sim_local_body r2 n es σs et σt Φ → sim_local_body r1 n es σs et σt Φ.
Proof.
  revert r1 r2 n es σs et σt Φ. pcofix CIH.
  intros r1 r2 n es σs et σt Φ VS SIM.
  pfold. punfold SIM; [|apply sim_local_body_mono].
  intros NT r_f WSAT1. have WSAT2 := VS _ _ _ WSAT1.
  specialize (SIM NT r_f WSAT2) as [NOTS TE SIM].
  constructor; [done|..].
  { intros.
    destruct (TE _ TERM) as (vs' & σs' & r' & STEP' & WSAT' & HΦ).
    naive_solver. }
  inversion SIM.
  - left. intros.
    specialize (STEP _ _ STEPT) as (es' & σs' & r' & idx' & STEP' & WSAT' & SIM').
    exists es', σs', r', idx'. do 2 (split; [done|]).
    pclearbot. right. eapply CIH; eauto. done.
  - econstructor 2; eauto. intros r' vs vt σs' σt' VRET WSAT' STACK.
    destruct (CONT _ _ _ σs' σt' VRET WSAT' STACK) as [idx' SIM'].
    exists idx'. pclearbot. right. eapply CIH; eauto. done.
Qed.

End local.

Hint Resolve sim_local_body_mono : paco.
