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
  | Val v => value_wf v
  | Call f args => expr_wf f ∧ Forall id (map expr_wf args)
  | Case e branches => expr_wf e ∧ Forall id (map expr_wf branches)
  | Var _ | Alloc _ => True
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
  n = sem_steps ∧ css' = css ∧ cst' = cst ∧ rrel r rs rt.

(** We define a "semantic well-formedness", in some context. *)
Definition sem_wf (r: resUR) es et :=
  ∀ xs : list (string * (result * result)),
    Forall (λ '(_, (rs, rt)), rrel r rs rt) xs →
    r ⊨ˢ{sem_steps,fs,ft}
      (subst_map (prod_map id fst <$> xs) es, css)
    ≥
      (subst_map (prod_map id snd <$> xs) et, cst)
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

Lemma list_find_var {A B : Type} x (f : A → B) (xs : list (string * A)):
  list_find (is_var x) (prod_map id f <$> xs) =
  prod_map id (prod_map id f) <$> list_find (is_var x) xs.
Proof.
  rewrite list_find_fmap. f_equal. apply list_find_proper. auto.
Qed.

Lemma expr_wf_soundness r e :
  expr_wf e → sem_wf r e e.
Proof.
  intros Hwf. induction e; simpl in Hwf.
  - (* Value *)
    move=>_ _ /=.
    apply sim_simple_val.
    split; first admit.
    split; first done. split; first done.
    apply value_wf_soundness. done.
  - (* Variable *)
    move=>{Hwf} xs Hxswf /=.
    rewrite !list_find_var. destruct (list_find (is_var x) xs) eqn:Hfind; simpl.
    + destruct p as [i [x' [rs rt]]]. simpl.
      destruct (list_find_Some _ _ _ _ Hfind).
      intros σs σt ??. eapply sim_body_result=>_.
      split; first admit.
      split; first done. split; first done.
      eapply (Forall_lookup_1 _ _ _ _ Hxswf H).
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
  - (* Let *) admit.
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
  rewrite (subst_l_map _ _ _ _ Hsubst1).
  rewrite (subst_l_map _ _ _ _ Hsubst2).
  set subst := fn_lists_to_subst (fun_args f) (zip (ValR <$> vs) (ValR <$> vt)).
  (* FIXME: we do 3 very similar inductions here. Not sure how to generalize though. *)
  replace (fn_lists_to_subst (fun_args f) (ValR <$> vs)) with (prod_map id fst <$> subst); last first.
  { rewrite /subst /fn_lists_to_subst. rewrite list_fmap_omap.
    apply omap_ext'. revert Hrel. clear. revert vs vt.
    induction (fun_args f); intros vs vt Hrel; simpl; first constructor.
    inversion Hrel; simplify_eq/=; first constructor.
    constructor. by destruct a. exact: IHl. }
  replace (fn_lists_to_subst (fun_args f) (ValR <$> vt)) with (prod_map id snd <$> subst); last first.
  { rewrite /subst /fn_lists_to_subst. rewrite list_fmap_omap.
    apply omap_ext'. revert Hrel. clear. revert vs vt.
    induction (fun_args f); intros vs vt Hrel; simpl; first constructor.
    inversion Hrel; simplify_eq/=; first constructor.
    constructor. by destruct a. exact: IHl. }
  eapply sim_simplify, expr_wf_soundness; [done..|].
  subst subst. revert Hrel. clear. revert vs vt.
  induction (fun_args f); intros vs vt Hrel; simpl; first constructor.
  inversion Hrel; simplify_eq/=; first constructor.
  destruct a; first exact: IHl. constructor.
  { admit. (* resource stuff. *) }
  exact: IHl.
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
