From stbor.lang Require Import lang subst_map.
From stbor.sim Require Import refl_step simple tactics.

Set Default Proof Using "Type".

(** Enable use of [Forall] in recursion. *)
Lemma Forall_id {A: Type} (P: A → Prop) (l: list A) :
  Forall P l ↔ Forall id (map P l).
Proof.
  induction l; simpl; first by eauto using Forall_nil.
  split; intros [??]%Forall_cons_1; apply Forall_cons; simpl; tauto.
Qed.

(** "Well-formed" code doen't contain literal
pointers, places or administrative operations (init_call/end_call).
Defined by recursion to make sure we don't miss a case. *)
Definition scalar_wf (a: scalar) : Prop :=
  match a with
  | ScPoison | ScInt _ | ScFnPtr _ => True
  | ScnPtr => False
  end.
Definition value_wf (v: value) : Prop := Forall scalar_wf v.
Fixpoint expr_wf (e: expr) : Prop :=
  match e with
  (* Structural cases. *)
  | Var _ | Alloc _ => True
  | Val v => value_wf v
  | Call f args => expr_wf f ∧ Forall id (map expr_wf args)
  | Case e branches => expr_wf e ∧ Forall id (map expr_wf branches)
  | Deref e _ | Ref e  | Copy e | Retag e _ =>
    expr_wf e
  | Proj e1 e2 | Conc e1 e2 | BinOp _ e1 e2 | Let _ e1 e2 | Write e1 e2 =>
    expr_wf e1 ∧ expr_wf e2
  (* Forbidden cases. *)
  | InitCall e | EndCall e => False
  | Place _ _ _ => False
  | Free _ => False (* TODO: We'd like to support deallocation! *)
  end.
Definition prog_wf (prog: fn_env) :=
  has_main prog ∧
  map_Forall (λ _ f, expr_wf f.(fun_body)) prog.

Section sem.
Context (fs ft: fn_env) `{!sim_local_funs_lookup fs ft}.
Context (css cst: call_id_stack).

Definition sem_steps := 10%nat.

Definition sem_post (r: resUR) (n: nat) rs css' rt cst': Prop :=
  n = sem_steps ∧ css' = css ∧ cst' = cst ∧ rrel vrel r rs rt.

(** We define a "semantic well-formedness", in some context. *)
Definition sem_wf (r: resUR) es et :=
  ∀ xs : gmap string (result * result),
    map_Forall (λ _ '(rs, rt), rrel vrel r rs rt) xs →
    r ⊨ˢ{sem_steps,fs,ft}
      (subst_map (fst <$> xs) es, css)
    ≥
      (subst_map (snd <$> xs) et, cst)
    : sem_post.

Lemma value_wf_soundness r v :
  value_wf v → vrel r v v.
Proof.
  intros Hwf. induction v.
  - constructor.
  - apply Forall_cons_1 in Hwf as [??]. constructor.
    + destruct a; done.
    + apply IHv. done.
Qed.

Lemma expr_wf_soundness r e :
  expr_wf e → sem_wf r e e.
Proof.
  revert r. induction e using expr_ind; simpl; intros r Hwf.
  - (* Value *)
    move=>_ _ /=.
    apply sim_simple_val.
    split; first done.
    split; first done. split; first done.
    apply value_wf_soundness. done.
  - (* Variable *)
    move=>{Hwf} xs Hxswf /=.
    rewrite !lookup_fmap. specialize (Hxswf x).
    destruct (xs !! x); simplify_eq/=.
    + destruct p as [rs rt].
      intros σs σt ??. eapply sim_body_result=>_.
      split; first done.
      split; first done. split; first done.
      eapply (Hxswf (rs, rt)). done.
    + simpl.
      (* FIXME: need lemma for when both sides are stuck on an unbound var. *)
      admit.
  - (* Call *)
    move=>xs Hxswf /=. sim_bind (subst_map _ e) (subst_map _ e).
    eapply sim_simple_post_mono, IHe; [|by apply Hwf|done].
    intros r' n' rs css' rt cst' (-> & -> & -> & Hrel). simpl.
    admit.
  - (* InitCall *) done.
  - (* EndCall *) done.
  - (* Proj *) admit.
  - (* Conc *) admit.
  - (* BinOp *) admit.
  - (* Place *) admit.
  - (* Deref *) admit.
  - (* Ref *) admit.
  - (* Copy *) admit.
  - (* Write *) admit.
  - (* Alloc *) admit.
  - (* Free *) done.
  - (* Retag *) admit.
  - (* Let *)
    move=>xs Hxs /=. sim_bind (subst_map _ e1) (subst_map _ e1).
    eapply sim_simple_post_mono, IHe1; [|by apply Hwf|done].
    intros r' n' rs css' rt cst' (-> & -> & -> & Hrel). simpl.
    intros σs σt ??. eapply sim_body_let.
    { destruct rs; eauto. } { destruct rt; eauto. }
    rewrite !subst'_subst_map.
    change rs with (fst (rs, rt)). change rt with (snd (rs, rt)) at 2.
    rewrite !binder_insert_map.
    eapply sim_simplify', IHe2; [done..|by apply Hwf|].
    admit. (* resources dont match?? *)
  - (* Case *) admit.
Admitted.

End sem.

Theorem sim_mod_fun_refl f :
  expr_wf f.(fun_body) →
  ⊨ᶠ f ≥ f.
Proof.
  intros Hwf fs ft Hlk r es et.
  intros vs vt σs σt Hrel Hsubst1 Hsubst2. exists sem_steps.
  apply sim_body_init_call=>/=.
  set css := snc σs :: scs σs. set cst := snc σt :: scs σt. move=>Hstacks.
  (* FIXME: viewshift to public call ID, use framing or something to get it to fun_post. *)
  eapply sim_local_body_post_mono with
    (Φ:=(λ r n vs' σs' vt' σt', sem_post css cst r n vs' σs'.(scs) vt' σt'.(scs))).
  { intros r' n' rs css' rt cst' (-> & ? & ? & Hrrel).
    split.
    - eexists. split. subst cst css. rewrite <-Hstacks. congruence.
      admit. (* end_call_sat *)
    - done.
  }
  destruct (subst_l_map _ _ _ _ _ _ _ (rrel vrel r) Hsubst1 Hsubst2) as (map & -> & -> & Hmap).
  { clear -Hrel. induction Hrel; eauto using Forall2. }
  eapply sim_simplify, expr_wf_soundness; [done..|].
  admit. (* resource stuff. *)
Admitted.

Lemma sim_mod_funs_refl prog :
  prog_wf prog →
  sim_mod_funs prog prog.
Proof.
  intros [_ WF]. induction prog using map_ind.
  { intros ??. rewrite lookup_empty. done. }
  apply sim_mod_funs_insert; first done.
  - apply sim_mod_fun_refl. eapply WF. erewrite lookup_insert. done.
  - apply IHprog. eapply map_Forall_insert_12; done.
Qed.
