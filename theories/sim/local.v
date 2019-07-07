From Paco Require Export paco.
From iris.algebra Require Import cmra gmap csum agree excl.

From stbor.lang Require Import defs.
From stbor.sim Require Import sflib.

Set Default Proof Using "Type".

Section local.
Context {A: ucmraT}.
Variable (wsat: A → state → state → Prop).
Variable (vrel: A → value → value → Prop).
Variable (fns fnt: fn_env).

Notation PRED := (A → nat → result → state → result → state → Prop)%type.
Notation SIM := (A → nat → expr → state → expr → state → PRED → Prop)%type.

Implicit Type (Φ: PRED).

Inductive _sim_local_body_step (r_f : A) (sim_local_body : SIM)
  (r: A) (idx: nat) es σs et σt Φ : Prop :=
(* If tgt makes 1 step, src can make some step *)
| sim_local_body_step_next
    (STEP: ∀ et' σt' (STEPT: (et, σt) ~{fnt}~> (et', σt')),
      (* then we locally can makes some step and pick a new resource r' *)
      ∃ es' σs' r' idx',
        ((es, σs) ~{fns}~>+ (es', σs') ∨
         ((idx' < idx)%nat ∧ (es', σs') = (es, σs))) ∧
        wsat (r_f ⋅ r') σs' σt' ∧
        sim_local_body r' idx' es' σs' et' σt' Φ)
(* If tgt prepares to make a call to [name], src should be able to make the same
  call. Here we do not want to step into the call of [name], but to step over it. *)
| sim_local_body_step_over_call
    (Ks: list (ectxi_language.ectx_item (bor_ectxi_lang fns)))
    (Kt: list (ectxi_language.ectx_item (bor_ectxi_lang fnt)))
    fid (vl_tgt: list value)
    (vl_src: list value) σ1_src
    rc rv
    (* tgt is ready to make a call of [name] *)
    (CALLTGT: et = fill Kt (Call #[ScFnPtr fid] (Val <$> vl_tgt)))
    (* src is ready to make a call of [name] *)
    (CALLSRC: (es, σs) ~{fns}~>* (fill Ks (Call #[ScFnPtr fid] (Val <$> vl_src)), σ1_src))
    (* and we can pick a resource [rv] for the arguments *)
    (WSAT: wsat (r_f ⋅ (rc ⋅ rv)) σ1_src σt)
    (* [rv] justifies the arguments *)
    (VREL: Forall2 (vrel rv) vl_src vl_tgt)
    (* and after the call our context can continue *)
    (CONT: ∀ r' v_src v_tgt σs' σt'
             (* For any new resource r' that supports the returned values are
                related w.r.t. (r ⋅ r' ⋅ r_f) *)
             (VRET: vrel r' v_src v_tgt)
             (WSAT: wsat (r_f ⋅ (rc ⋅ r')) σs' σt')
             (STACK: σt.(scs) = σt'.(scs)),
        ∃ idx', sim_local_body (rc ⋅ r') idx'
                               (fill Ks (Val v_src)) σs'
                               (fill Kt (Val v_tgt)) σt' Φ).

Record sim_local_body_base (r_f: A) (sim_local_body : SIM)
  (r: A) (idx: nat) es σs et σt Φ : Prop := {
  sim_local_body_stuck :
    (terminal et ∨ reducible fnt et σt) ;
  sim_local_body_terminal :
    (* if tgt is terminal *)
    ∀ vt (TERM: to_result et = Some vt),
      (* then src can get terminal *)
      ∃ vs' σs' r' idx',
        sflib.__guard__ ((es, σs) ~{fns}~>+ (of_result vs', σs') ∨
                         ((idx' < idx)%nat ∧ (es, σs) = (of_result vs', σs'))) ∧
        (* and re-establish wsat *)
        wsat (r_f ⋅ r') σs' σt ∧ Φ r' idx' vs' σs' vt σt ;
  sim_local_body_step :
      _sim_local_body_step r_f sim_local_body r idx es σs et σt Φ
}.

Definition _sim_local_body (sim_local_body : SIM)
  (r: A) (idx: nat) es σs et σt Φ : Prop :=
  (* assuming that src cannot get stuck *)
  ∀ (NEVER_STUCK: never_stuck fns es σs)
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
    destruct (TE _ TERM) as (vs' & σs' & r' & idx' & STEP' & WSAT' & HΦ).
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

(* Simulating functions:
  - We start after the substitution.
  - We assume the arguments are values related by [r]
  - The returned result must also be values and related by [vrel]. *)
Definition fun_post (esat: A → call_id → Prop) initial_call_id_stack
  (r: A) (n: nat) rs (σs: state) rt σt :=
  (∃ c, σt.(scs) = c :: initial_call_id_stack ∧ esat r c) ∧
  (∃ vs vt, rs = ValR vs ∧ rt = ValR vt ∧ vrel r vs vt).
Definition sim_local_fun
  (esat: A → call_id → Prop) (fn_src fn_tgt : function) : Prop :=
  ∀ r es et (vl_src vl_tgt: list value) σs σt
    (VALEQ: Forall2 (vrel r) vl_src vl_tgt)
    (EQS: subst_l fn_src.(fun_b) (Val <$> vl_src) fn_src.(fun_e) = Some es)
    (EQT: subst_l fn_tgt.(fun_b) (Val <$> vl_tgt) fn_tgt.(fun_e) = Some et),
    ∃ idx, sim_local_body r idx
                          (InitCall es) σs (InitCall et) σt
                          (fun_post esat σt.(scs)).

Definition sim_local_funs (esat: A → call_id → Prop) : Prop :=
  ∀ name fn_src, fns !! name = Some fn_src → ∃ fn_tgt,
    fnt !! name = Some fn_tgt ∧
    length fn_src.(fun_b) = length fn_tgt.(fun_b) ∧
    sim_local_fun esat fn_src fn_tgt.

End local.

Hint Resolve sim_local_body_mono : paco.
