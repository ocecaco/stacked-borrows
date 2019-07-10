From iris.algebra Require Import local_updates.

From stbor.lang Require Import steps_progress steps_inversion steps_retag.
From stbor.sim Require Export instance.

Set Default Proof Using "Type".

Section left.
Implicit Types Φ: resUR → nat → result → state → result → state → Prop.

Lemma sim_body_let_l fs ft r n x et es1 es2 vs1 σs σt Φ :
  IntoResult es1 vs1 →
  r ⊨{n,fs,ft} (subst' x es1 es2, σs) ≥ (et, σt) : Φ →
  r ⊨{n,fs,ft} (let: x := es1 in es2, σs) ≥ (et, σt) : Φ.
Proof.
  intros TS%into_result_terminal CONT. pfold.
  intros NT r_f WSAT.
  have STEPS1: ((let: x := es1 in es2)%E, σs) ~{fs}~> (subst' x es1 es2, σs).
  { eapply (head_step_fill_tstep _ []). econstructor. by econstructor. }
  have STEPS: ((let: x := es1 in es2)%E, σs) ~{fs}~>* (subst' x es1 es2, σs).
  { by apply rtc_once. }
  have NT2 := never_stuck_tstep_rtc _ _ _ _ _ STEPS NT.
  have CONT2 := CONT. punfold CONT. specialize (CONT NT2 r_f WSAT) as [RE TE ST].
  split; [done|..].
  { intros. specialize (TE _ TERM) as (vs' & σs' & r' & STEPS' & ?).
    exists vs', σs', r'. split; [|done]. by etrans. }
  inversion ST.
  - constructor 1. intros.
    specialize (STEP _ _ STEPT) as (es' & σs' & r' & n' & SS' & ?).
    exists es', σs', r', n'. split ; [|done]. left.
    destruct SS' as [SS'|[]].
    + eapply tc_rtc_l; eauto.
    + simplify_eq. by apply tc_once.
  - econstructor 2; eauto. by etrans.
Qed.

Lemma sim_body_deref_l fs ft r n et (rt: result) l t T σs σt Φ :
  IntoResult et rt →
  (Φ r n (PlaceR l t T) σs rt σt) →
  r ⊨{n,fs,ft} (Deref #[ScPtr l t] T, σs) ≥ (et, σt) : Φ.
Proof.
  intros TT POST. pfold.
  intros NT r_f WSAT. split.
  { left. by apply into_result_terminal in TT. }
  { intros. exists (PlaceR l t T), σs, r. split; last split; [|done|].
    - apply rtc_once. eapply (head_step_fill_tstep _ []).
      econstructor. econstructor.
    - rewrite <-into_result in TERM. rewrite to_of_result in TERM.
      by simplify_eq. }
  constructor 1. intros.
  apply result_tstep_stuck in STEPT.
  move : STEPT. rewrite <-into_result. by rewrite to_of_result.
Qed.

Lemma sim_body_copy_unique_l
  fs ft (r r': resUR) (h: heaplet) n (l: loc) tg T (s: scalar) et σs σt Φ :
  tsize T = 1%nat →
  r ≡ r' ⋅ res_tag tg tkUnique h →
  h !! l = Some s →
  (r ⊨{n,fs,ft} (#[s], σs) ≥ (et, σt) : Φ : Prop) →
  r ⊨{n,fs,ft} (Copy (Place l (Tagged tg) T), σs) ≥ (et, σt) : Φ.
Proof.
Admitted.

(* should be a fairly direct consequence of the above *)
Lemma sim_body_copy_local_l fs ft r r' n l tg ty s et σs σt Φ :
  tsize ty = 1%nat →
  r ≡ r' ⋅ res_mapsto l [s] tg →
  (r ⊨{n,fs,ft} (#[s], σs) ≥ (et, σt) : Φ) →
  r ⊨{n,fs,ft}
    (Copy (Place l (Tagged tg) ty), σs) ≥ (et, σt)
  : Φ.
Proof.
Admitted.

End left.
