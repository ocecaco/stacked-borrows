From stbor.lang Require Import lang subst_map.
From stbor.sim Require Import refl_step simple tactics viewshift.

Set Default Proof Using "Type".

(** Enable use of [Forall] in recursion. *)
Lemma Forall_id {A: Type} (P: A → Prop) (l: list A) :
  Forall id (fmap P l) ↔ Forall P l.
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
  | Call f args => expr_wf f ∧ Forall id (fmap expr_wf args)
  | Case e branches => expr_wf e ∧ Forall id (fmap expr_wf branches)
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

(** Well-formed two-substitutions. *)
Definition srel (r: resUR) (xs: gmap string (result * result)) : Prop :=
  map_Forall (λ _ '(rs, rt), rrel r rs rt) xs.

Lemma srel_persistent r xs :
  srel r xs → srel (core r) xs.
Proof.
  intros Hrel x [vs vt] Hlk. apply rrel_persistent.
  eapply (Hrel _ _ Hlk).
Qed.

Lemma srel_mono r1 r2 xs :
  ✓ r2 → r1 ≼ r2 →
  srel r1 xs → srel r2 xs.
Proof.
  intros Hval Hincl Hrel x [vs vt] Hlk. eapply rrel_mono; [done..|].
  eapply (Hrel _ _ Hlk).
Qed.

Lemma srel_core_mono r rf xs:
  srel r xs → ✓ rf → core r ≼ rf → srel rf xs.
Proof.
  intros Hrel%srel_persistent ??. eapply srel_mono; done.
Qed.

Lemma vrel_core_mono r rf v1 v2 :
  vrel r v1 v2 → ✓ rf → core r ≼ rf → vrel rf v1 v2.
Proof.
  intros Hrel%vrel_persistent ??. eapply vrel_mono; done.
Qed.

Lemma rrel_core_mono r rf r1 r2 :
  rrel r r1 r2 → ✓ rf → core r ≼ rf → rrel rf r1 r2.
Proof.
  intros Hrel%rrel_persistent ??. eapply rrel_mono; done.
Qed.

Lemma arel_core_mono r rf a1 a2 :
  arel r a1 a2 → ✓ rf → core r ≼ rf → arel rf a1 a2.
Proof.
  intros Hrel%arel_persistent ??. eapply arel_mono; done.
Qed.

(** Hints. *)
Local Hint Extern 10 (srel _ _) => apply: srel_core_mono; first fast_done : core.
Local Hint Extern 10 (rrel _ _ _) => apply: rrel_core_mono; first fast_done : core.
Local Hint Extern 10 (arel _ _ _) => apply: arel_core_mono; first fast_done : core.
Local Hint Extern 50 (_ ≼ _) => solve_res : core.

(** We define a "semantic well-formedness", in some context. *)
Definition sem_steps := 10%nat.

Definition sem_post (r: resUR) (n: nat) rs css' rt cst': Prop :=
  n = sem_steps ∧ css' = css ∧ cst' = cst ∧ rrel r rs rt.

Definition sem_wf (r: resUR) es et :=
  ∀ xs : gmap string (result * result),
    srel r xs →
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

Lemma sim_simple_call_args' r r' (el1 el2: list expr) (rs rt: result) Φ :
  Forall2 (λ e1 e2, core r ⊨ˢ{sem_steps,fs,ft} (e1, css) ≥ (e2, cst) : sem_post) el1 el2 →
  (∀ r' (vs vt: list result),
    Forall2 (rrel r') vs vt →
    core r ⋅ r' ⊨ˢ{sem_steps,fs,ft}
      (Call rs (of_result <$> vs), css) ≥ (Call rt (of_result <$> vt), cst)
    : Φ ) →
  ∀ vs vt, Forall2 (rrel r') vs vt →
  core r ⋅ r' ⊨ˢ{sem_steps,fs,ft}
    (Call rs ((of_result <$> vs) ++ el1), css) ≥ (Call rt ((of_result <$> vt) ++ el2), cst)
  : Φ.
Proof.
  intros He Hcont. revert r'. induction He; intros r'.
  { intros vs vt ?. rewrite !app_nil_r. eapply (Hcont _ vs vt). done. }
  clear Hcont. intros vs vt Hvst.
  eapply sim_simple_bind_call.
  rewrite cmra_core_dup -assoc.
  eapply sim_simple_frame_r.
  eapply sim_simple_post_mono, H.
  intros r'' n' rs' css' rt' cst' (-> & -> & -> & [Hrel ?]%rrel_with_eq).
  simplify_eq/=.
  rewrite !cons_middle !assoc.
  change [rt']%E with (of_result <$> [rt']).
  rewrite - !fmap_app. rewrite [r'' ⋅ core r]comm -assoc=>Hval.
  eapply IHHe. eapply Forall2_app.
  - eapply Forall2_impl; first done. intros.
    eapply rrel_mono; last done; eauto using cmra_valid_included.
  - constructor; last done.
    eapply rrel_mono; last done; eauto using cmra_valid_included.
Qed.

Lemma sim_simple_call_args r r' (el1 el2: list expr) (rs rt: result) Φ :
  Forall2 (λ e1 e2, core r ⊨ˢ{sem_steps,fs,ft} (e1, css) ≥ (e2, cst) : sem_post) el1 el2 →
  (∀ r' (vs vt: list result),
    Forall2 (rrel r') vs vt →
    core r ⋅ r' ⊨ˢ{sem_steps,fs,ft}
      (Call rs (of_result <$> vs), css) ≥ (Call rt (of_result <$> vt), cst)
    : Φ ) →
  core r ⋅ r' ⊨ˢ{sem_steps,fs,ft} (Call rs el1, css) ≥ (Call rt el2, cst) : Φ.
Proof.
  intros He Hcont.
  eapply sim_simple_call_args' with (vs:=[]) (vt:=[]); auto.
Qed.

Lemma expr_wf_soundness r e :
  expr_wf e → sem_wf r e e.
Proof.
  revert r. induction e using expr_ind; simpl; intros r.
  - (* Value *)
    move=>Hwf _ _ /=.
    apply sim_simple_val.
    do 3 (split; first done).
    apply value_wf_soundness. done.
  - (* Variable *)
    move=>_ xs Hxswf /=.
    rewrite !lookup_fmap. specialize (Hxswf x).
    destruct (xs !! x); simplify_eq/=.
    + destruct p as [rs rt].
      intros σs σt ??. eapply sim_body_result=>_.
      do 3 (split; first done).
      eapply (Hxswf (rs, rt)). done.
    + simpl. apply sim_simple_var.
  - (* Call *)
    move=>[Hwf1 /Forall_id Hwf2] xs Hxswf /=. sim_bind (subst_map _ e) (subst_map _ e).
    eapply sim_simple_frame_core.
    eapply sim_simple_post_mono, IHe; [|by auto..].
    intros r' n' rs css' rt cst' (-> & -> & -> & Hrel) Hval. simpl.
    eapply sim_simple_call_args.
    { induction Hwf2; simpl; first by auto.
      destruct (Forall_cons_1 _ _ _ H) as [IHx IHl]. constructor.
      - eapply IHx; auto. exact: srel_persistent.
      - eapply IHHwf2. done. }
    intros r'' rs' rt' Hrel'.
    admit. (* needs call lemma that works with any result. *)
  - (* InitCall: can't happen *) done.
  - (* EndCall: can't happen *) done.
  - (* Proj *)
    move=>[Hwf1 Hwf2] xs Hxs /=. sim_bind (subst_map _ e1) (subst_map _ e1).
    eapply sim_simple_frame_core.
    eapply sim_simple_post_mono, IHe1; [|by auto..].
    intros r' n' rs css' rt cst' (-> & -> & -> & [Hrel ?]%rrel_with_eq) Hval.
    simplify_eq/=. sim_bind (subst_map _ e2) (subst_map _ e2).
    eapply sim_simple_frame_more_core.
    eapply sim_simple_post_mono, IHe2; [|by auto..].
    intros r'' n' rs' css' rt' cst' (-> & -> & -> & [Hrel' ?]%rrel_with_eq) Hval'.
    simplify_eq/=. eapply sim_simple_proj; [done..|].
    intros vi vv idx ?? Hidx ?. simplify_eq.
    do 3 (split; first done).
    move:Hrel=>/= /Forall2_lookup=>Hrel.
    specialize (Hrel (Z.to_nat idx)).
    rewrite Hidx in Hrel. inversion Hrel. simplify_eq/=.
    constructor; last done. auto.
  - (* Conc *)
    move=>[Hwf1 Hwf2] xs Hxs /=. sim_bind (subst_map _ e1) (subst_map _ e1).
    eapply sim_simple_frame_core.
    eapply sim_simple_post_mono, IHe1; [|by auto..].
    intros r' n' rs css' rt cst' (-> & -> & -> & [Hrel ?]%rrel_with_eq) Hval.
    simplify_eq/=. sim_bind (subst_map _ e2) (subst_map _ e2).
    eapply sim_simple_frame_more_core.
    eapply sim_simple_post_mono, IHe2; [|by auto..].
    intros r'' n' rs' css' rt' cst' (-> & -> & -> & [Hrel' ?]%rrel_with_eq) Hval'.
    simplify_eq/=. eapply sim_simple_conc; [done..|].
    intros v1 v2 ??. simplify_eq/=.
    do 3 (split; first done). simpl.
    apply Forall2_app.
    + eapply vrel_core_mono; first done; auto.
    + eapply vrel_mono; last done; auto.
  - (* BinOp *)
    move=>[Hwf1 Hwf2] xs Hxs /=. sim_bind (subst_map _ e1) (subst_map _ e1).
    eapply sim_simple_frame_core.
    eapply sim_simple_post_mono, IHe1; [|by auto..].
    intros r' n' rs css' rt cst' (-> & -> & -> & [Hrel ?]%rrel_with_eq) Hval.
    simplify_eq/=. sim_bind (subst_map _ e2) (subst_map _ e2).
    eapply sim_simple_frame_more_core.
    eapply sim_simple_post_mono, IHe2; [|by auto..].
    intros r'' n' rs' css' rt' cst' (-> & -> & -> & [Hrel' ?]%rrel_with_eq) Hval'.
    simplify_eq/=. eapply sim_simple_bin_op; [done..|].
    intros v1 v2 s ? ?? Heval. simplify_eq/=.
    do 3 (split; first done). constructor; last done.
    assert (arel (core r ⋅ core r' ⋅ r'') v1 v1) as Hrel_v1.
    { apply Forall2_cons_inv in Hrel as [??]. auto. }
    inversion Heval; simpl; auto; []. do 2 (split; first done).
    simplify_eq/=. apply Hrel_v1.
  - (* Place: can't happen *) done.
  - (* Deref *)
    move=>Hwf xs Hxswf /=. sim_bind (subst_map _ e) (subst_map _ e).
    eapply sim_simple_post_mono, IHe; [|by auto..].
    intros r' n' rs css' rt cst' (-> & -> & -> & [Hrel ?]%rrel_with_eq).
    simplify_eq/=. eapply sim_simple_deref=>l t ?. simplify_eq/=.
    do 3 (split; first done). done.
  - (* Ref *)
    move=>Hwf xs Hxswf /=. sim_bind (subst_map _ e) (subst_map _ e).
    eapply sim_simple_post_mono, IHe; [|by auto..].
    intros r' n' rs css' rt cst' (-> & -> & -> & [Hrel ?]%rrel_with_eq).
    simplify_eq/=. eapply sim_simple_ref=>l t ??. simplify_eq/=.
    do 3 (split; first done). apply Hrel.
  - (* Copy *) admit.
  - (* Write *) admit.
  - (* Alloc *) admit.
  - (* Free: can't happen *) done.
  - (* Retag *) admit.
  - (* Let *)
    move=>[Hwf1 Hwf2] xs Hxs /=. sim_bind (subst_map _ e1) (subst_map _ e1).
    eapply sim_simple_frame_core.
    eapply sim_simple_post_mono, IHe1; [|by auto..].
    intros r' n' rs css' rt cst' (-> & -> & -> & Hrel) Hval. simpl.
    eapply sim_simple_let; [destruct rs, rt; by eauto..|].
    rewrite !subst'_subst_map.
    change rs with (fst (rs, rt)). change rt with (snd (rs, rt)) at 2.
    rewrite !binder_insert_map.
    eapply IHe2; [by auto..|].
    destruct b; first by auto. simpl.
    apply map_Forall_insert_2.
    + eapply rrel_mono; last done; auto.
    + eapply srel_core_mono; eauto.
  - (* Case *)
    move=>[Hwf1 /Forall_id Hwf2] xs Hxs /=. sim_bind (subst_map _ e) (subst_map _ e).
    eapply sim_simple_frame_core.
    eapply sim_simple_post_mono, IHe; [|by auto..].
    intros r' n' rs css' rt cst' (-> & -> & -> & [Hrel ?]%rrel_with_eq) Hval.
    simplify_eq/=. eapply sim_simple_case.
    { rewrite !fmap_length //. }
    intros es et ??. rewrite !list_lookup_fmap.
    destruct (el !! Z.to_nat i) eqn:Hlk; last done.
    intros. simplify_eq/=.
    eapply (Forall_lookup_1  _ _ _ _ H Hlk).
    + eapply (Forall_lookup_1  _ _ _ _ Hwf2 Hlk).
    + eauto.
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
  eapply sim_body_viewshift.
  { eapply viewshift_frame_l. eapply vs_call_empty_public. }
  eapply sim_body_frame_r.
  eapply sim_local_body_post_mono with
    (Φ:=(λ r n vs' σs' vt' σt', sem_post css cst r n vs' σs'.(scs) vt' σt'.(scs))).
  { intros r' n' rs css' rt cst' (-> & Hcss & Hcst & Hrrel) Hval. simplify_eq.
    split.
    - eexists. split; first by rewrite Hcst.
      apply: res_end_call_sat; first done. exact: cmra_included_r.
    - eapply rrel_mono; [done| |done]. exact: cmra_included_l.
  }
  destruct (subst_l_map _ _ _ _ _ _ _ (rrel r) Hsubst1 Hsubst2) as (map & -> & -> & Hmap).
  { clear -Hrel. induction Hrel; eauto using Forall2. }
  eapply sim_simplify, expr_wf_soundness; done.
Qed.

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
