From iris.algebra Require Import local_updates.

From stbor.lang Require Import steps_progress steps_inversion steps_retag.
From stbor.sim Require Export instance.

Set Default Proof Using "Type".

Lemma sim_body_copy_left_1
  fs ft (r: resUR) k (h: heapletR) n l t et σs σt Φ
  (UNIQUE: r.(rtm) !! t ≡ Some (k, h))
  (InD: l ∈ dom (gset loc) h) :
  (∀ s, σs.(shp) !! l = Some s → r ⊨{n,fs,ft} (#[s%S], σs) ≥ (et, σt) : Φ : Prop) →
  r ⊨{n,fs,ft} (Copy (Place l (Tagged t) int), σs) ≥ (et, σt) : Φ.
Proof.
  intros COND. pfold. intros NT r_f WSAT.
  edestruct NT as [[]|[es1 [σs1 STEP1]]]; [constructor 1|done|].
  destruct (tstep_copy_inv _ (PlaceR l (Tagged t) int) _ _ _ STEP1)
    as (l' & t' & T' & vs & α' & EqH & ? & Eqvs & READ & ?).
  symmetry in EqH. simplify_eq.
  rewrite /= read_mem_equation_1 /= in Eqvs.
  destruct (σs.(shp) !! l) as [s|] eqn:Eqs; [|done]. simpl in Eqvs. simplify_eq.
  specialize (COND _ eq_refl).

  (* we need to invoke WSAT to know that α' = σs.(sst) *)
  destruct WSAT as (WFS & WFT & VALID & PINV & CINV & SREL).

  (* once we know that the state did not change, we can use COND. *)
  have NT2 := never_stuck_tstep_once _ _ _ _ _ STEP1 NT.
  punfold COND.

  split.
  { (* this comes from COND *) admit. }
  { (* follows COND *) admit. }
  { (* follows COND *) admit. }
Abort.
