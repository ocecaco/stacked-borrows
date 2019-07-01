From Paco Require Export paco.
From iris.algebra Require Import cmra gmap csum agree excl.

From stbor.lang Require Import defs.
From stbor.sim Require Import sflib.

Set Default Proof Using "Type".

Section local.
Context {A: ucmraT}.
Variable (wsat: A → state → state → Prop).
Variable (vrel: A → expr → expr → Prop).
Variable (fns fnt: fn_env).

Definition rrel (vrel: A → expr → expr → Prop) (r: A) (es et: expr) : Prop :=
  ∀ vt, to_result et = Some vt → ∃ vs, to_result es = Some vs ∧
    match vs, vt with
    | ValR vs, ValR vt => vrel r (Val vs) (Val vt)
    | PlaceR ls ts Ts, PlaceR lt t_t Tt =>
        vrel r #[ScPtr ls ts]%E #[ScPtr lt t_t]%E ∧ Ts = Tt
    | _, _ => False
    end.

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
    fid el_tgt
    el_src σ1_src
    rc rv
    (* tgt is ready to make a call of [name] *)
    (CALLTGT: et = fill Kt (Call #[ScFnPtr fid] el_tgt))
    (VTGT: Forall (λ ei, is_Some (to_value ei)) el_tgt)
    (* src is ready to make a call of [name] *)
    (CALLSRC: (es, σs) ~{fns}~>* (fill Ks (Call #[ScFnPtr fid] el_src), σ1_src))
    (VSRC: Forall (λ ei, is_Some (to_value ei)) el_src)
    (* and we can pick a resource [rv] for the arguments *)
    (WSAT: wsat (r_f ⋅ (rc ⋅ rv)) σ1_src σt)
    (* [rv] justifies the arguments *)
    (VREL: Forall2 (vrel rv) el_src el_tgt)
    (* and after the call our context can continue *)
    (CONT: ∀ r' v_src v_tgt σs' σt'
             (* For any new resource r' that supports the returned values are
                related w.r.t. (r ⋅ r' ⋅ r_f) *)
             (VRET: vrel r' (Val v_src) (Val v_tgt))
             (* Stack unchanged *)
             (STACK: σt'.(sst) = σt.(sst)),
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
  - econstructor 2; eauto. intros.
    destruct (CONT _ _ _ σs' σt' VRET STACK) as [idx' SIM'].
    exists idx'. pclearbot. right. eapply CIH; eauto.
Qed.

(* Simulating functions:
  - We start after the substitution.
  - We assume the arguments are values related by [r]
  - The returned result must also be values and related by [vrel]. *)
Definition sim_local_fun
  (esat: A → state → state → Prop) (fn_src fn_tgt : function) : Prop :=
  ∀ r es et el_src el_tgt σs σt
    (VALS: Forall (λ ei, is_Some (to_value ei)) el_src)
    (VALT: Forall (λ ei, is_Some (to_value ei)) el_tgt)
    (VALEQ: Forall2 (vrel r) el_src el_tgt)
    (EQS: match fn_src with
          | FunV xl e => subst_l xl el_src e = Some es
          end)
    (EQT: match fn_tgt with
          | FunV xl e => subst_l xl el_tgt e = Some et
          end),
    ∃ idx, sim_local_body r idx
                          (InitCall es) σs (InitCall et) σt
                          (λ r _ vs σs vt σt, esat r σs σt ∧ vrel r (of_result vs) (of_result vt)).

Definition sim_local_funs (esat: A → state → state → Prop) : Prop :=
  ∀ name fn_tgt, fnt !! name = Some fn_tgt → ∃ fn_src,
    fns !! name = Some fn_src ∧
    match fn_src, fn_tgt with
    | FunV xls _, FunV xlt _ => length xls = length xlt
    end ∧
    sim_local_fun esat fn_src fn_tgt.

End local.

Hint Resolve sim_local_body_mono : paco.
