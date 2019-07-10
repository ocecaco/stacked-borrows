From iris.algebra Require Import local_updates.

From stbor.lang Require Import steps_progress steps_inversion steps_retag.
From stbor.sim Require Export instance body.

Set Default Proof Using "Type".

Section right.
Implicit Types Φ: resUR → nat → result → state → result → state → Prop.

Lemma sim_body_let_r fs ft r n x es et1 et2 vt1 σs σt Φ :
  IntoResult et1 vt1 →
  r ⊨{n,fs,ft} (es, σs) ≥ (subst' x et1 et2, σt) : Φ →
  r ⊨{S n,fs,ft} (es, σs) ≥ (let: x := et1 in et2, σt) : Φ.
Proof.
  intros TT%into_result_terminal CONT. pfold.
  intros NT r_f WSAT. split; [|done|].
  { right. do 2 eexists. eapply (head_step_fill_tstep _ []).
    econstructor 1. eapply LetBS; eauto. }
  constructor 1. intros.
  destruct (tstep_let_inv _ _ _ _ _ _ _ TT STEPT). subst et' σt'.
  exists es, σs, r, n. split; last split.
  - right. split; [lia|done].
  - done.
  - by left.
Qed.

Lemma sim_body_deref_r fs ft r n es (rs: result) l t T σs σt Φ :
  IntoResult es rs →
  (Φ r n rs σs (PlaceR l t T) σt) →
  r ⊨{S n,fs,ft} (es, σs) ≥ (Deref #[ScPtr l t] T, σt) : Φ.
Proof.
  intros TS POST. pfold.
  intros NT r_f WSAT. split; [|done|].
  { right. exists (Place l t T), σt.
    eapply (head_step_fill_tstep _ []). econstructor; econstructor. }
  constructor 1. intros.
  destruct (tstep_deref_inv _ (ValR _) _ _ _ _ STEPT) as (l' & t' & ? & ? & ?).
  simplify_eq.
  exists es, σs, r, n. split; last split.
  - right. split; [lia|done].
  - done.
  - left. apply : sim_body_result.
    intros. by eapply POST.
Qed.

Lemma sim_body_copy_unique_r
  fs ft (r r': resUR) (h: heaplet) n (l: loc) tg T (s: scalar) es σs σt Φ :
  tsize T = 1%nat →
  tag_on_top σt.(sst) l tg →
  r ≡ r' ⋅ res_tag tg tkUnique h →
  h !! l = Some s →
  (r ⊨{n,fs,ft} (es, σs) ≥ (#[s], σt) : Φ : Prop) →
  r ⊨{S n,fs,ft} (es, σs) ≥ (Copy (Place l (Tagged tg) T), σt) : Φ.
Proof.
Admitted.

(* should be a fairly direct consequence of the above. *)
Lemma sim_body_copy_local_r fs ft r r' n l tg ty s es σs σt Φ :
  tsize ty = 1%nat →
  r ≡ r' ⋅ res_mapsto l [s] tg →
  (r ⊨{n,fs,ft} (es, σs) ≥ (#[s], σt) : Φ) →
  r ⊨{S n,fs,ft}
    (es, σs) ≥ (Copy (Place l (Tagged tg) ty), σt)
  : Φ.
Proof.
Admitted.

End right.
