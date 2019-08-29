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
  | ScnPtr => False (* literal pointers *)
  end.
Definition value_wf (v: value) : Prop := Forall scalar_wf v.
Fixpoint expr_wf (e: expr) : Prop :=
  match e with
  (* Structural cases. *)
  | Var _ | Alloc _ => True
  | Val v => value_wf v
  | Call f args => expr_wf f ∧ Forall id (fmap expr_wf args)
  | Case e branches => expr_wf e ∧ Forall id (fmap expr_wf branches)
  | Deref e _ | Ref e | Copy e | Free e | Retag e _ _ _ =>
    expr_wf e
  | Proj e1 e2 | Conc e1 e2 | BinOp _ e1 e2 | Let _ e1 e2 | Write e1 e2 =>
    expr_wf e1 ∧ expr_wf e2
  (* Forbidden cases. *)
  | InitCall e | EndCall e => False (* administrative *)
  | Place _ _ _ => False (* literal pointers *)
  end.
Definition prog_wf (prog: fn_env) :=
  has_main prog ∧
  map_Forall (λ _ f, expr_wf f.(fun_body)) prog.

Section sem.
Context (fs ft: fn_env) `{!sim_local_funs_lookup fs ft}.

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
Local Hint Extern 20 (srel _ _) => apply: srel_mono; last fast_done : core.
Local Hint Extern 10 (rrel _ _ _) => apply: rrel_core_mono; first fast_done : core.
Local Hint Extern 20 (rrel _ _ _) => apply: rrel_mono; last fast_done : core.
Local Hint Extern 10 (vrel _ _ _) => apply: vrel_core_mono; first fast_done : core.
Local Hint Extern 20 (vrel _ _ _) => apply: vrel_mono; last fast_done : core.
Local Hint Extern 10 (Forall2 (arel _) _ _) => apply: vrel_core_mono; first fast_done : core.
Local Hint Extern 20 (Forall2 (arel _) _ _) => apply: vrel_mono; last fast_done : core.
Local Hint Extern 10 (arel _ _ _) => apply: arel_core_mono; first fast_done : core.
Local Hint Extern 20 (arel _ _ _) => apply: arel_mono; last fast_done : core.
Local Hint Extern 50 (_ ≼ _) => solve_res : core.

(** We define a "semantic well-formedness", in some context. *)
Definition sem_steps := 10%nat.

Definition sem_post (r: resUR) (n: nat) rs rt: Prop :=
  n = sem_steps ∧ rrel r rs rt.

Definition sem_wf (r: resUR) es et :=
  ∀ xs : gmap string (result * result),
    srel r xs →
    r ⊨ˢ{sem_steps,fs,ft}
      subst_map (fst <$> xs) es
    ≥
      subst_map (snd <$> xs) et
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
  Forall2 (λ e1 e2, core r ⊨ˢ{sem_steps,fs,ft} e1 ≥ e2 : sem_post) el1 el2 →
  (∀ r' (vs vt: list result),
    Forall2 (rrel r') vs vt →
    core r ⋅ r' ⊨ˢ{sem_steps,fs,ft}
      Call rs (of_result <$> vs) ≥ Call rt (of_result <$> vt)
    : Φ ) →
  ∀ vs vt, Forall2 (rrel r') vs vt →
  core r ⋅ r' ⊨ˢ{sem_steps,fs,ft}
    Call rs ((of_result <$> vs) ++ el1) ≥ Call rt ((of_result <$> vt) ++ el2)
  : Φ.
Proof.
  intros He Hcont. revert r'. induction He; intros r'.
  { intros vs vt ?. rewrite !app_nil_r. eapply (Hcont _ vs vt). done. }
  clear Hcont. intros vs vt Hvst.
  eapply sim_simple_bind_call.
  rewrite cmra_core_dup -assoc.
  eapply sim_simple_frame_r.
  eapply sim_simple_post_mono, H.
  intros r'' n' rs' rt' (-> & [Hrel ?]%rrel_with_eq).
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
  Forall2 (λ e1 e2, core r ⊨ˢ{sem_steps,fs,ft} e1 ≥ e2 : sem_post) el1 el2 →
  (∀ r' (vs vt: list result),
    Forall2 (rrel r') vs vt →
    core r ⋅ r' ⊨ˢ{sem_steps,fs,ft}
      Call rs (of_result <$> vs) ≥ Call rt (of_result <$> vt)
    : Φ ) →
  core r ⋅ r' ⊨ˢ{sem_steps,fs,ft} Call rs el1 ≥ Call rt el2 : Φ.
Proof.
  intros He Hcont.
  eapply sim_simple_call_args' with (vs:=[]) (vt:=[]); auto.
Qed.

Lemma expr_wf_soundness r e :
  expr_wf e → sem_wf r e e.
Proof using Type*.
  revert r. induction e using expr_ind; simpl; intros r.
  - (* Value *)
    move=>Hwf _ _ /=.
    apply: sim_simple_result.
    split; first done.
    apply value_wf_soundness. done.
  - (* Variable *)
    move=>_ xs Hxswf /=.
    rewrite !lookup_fmap. specialize (Hxswf x).
    destruct (xs !! x); simplify_eq/=.
    + destruct p as [rs rt]. apply: sim_simple_result.
      split; first done. eapply (Hxswf (rs, rt)). done.
    + simpl. apply sim_simple_var.
  - (* Call *)
    move=>[Hwf1 /Forall_id Hwf2] xs Hxswf /=. sim_bind (subst_map _ e) (subst_map _ e).
    eapply sim_simple_frame_core.
    eapply sim_simple_post_mono, IHe; [|by auto..].
    intros r' n' rs rt (-> & [Hrel ?]%rrel_with_eq) Hval. simpl.
    eapply sim_simple_call_args.
    { induction Hwf2; simpl; first by auto.
      destruct (Forall_cons_1 _ _ _ H) as [IHx IHl]. constructor.
      - eapply IHx; auto. exact: srel_persistent.
      - eapply IHHwf2. done. }
    intros r'' rs' rt' Hrel'. simplify_eq/=.
    eapply sim_simple_valid_post.
    eapply sim_simple_call; [by auto..|].
    intros rret vs vt vls vlt ? ??? Hrel''. simplify_eq.
    apply: sim_simple_result=>Hval'.
    split; first done. auto.
  - (* InitCall: can't happen *) done.
  - (* EndCall: can't happen *) done.
  - (* Proj *)
    move=>[Hwf1 Hwf2] xs Hxs /=. sim_bind (subst_map _ e1) (subst_map _ e1).
    eapply sim_simple_frame_core.
    eapply sim_simple_post_mono, IHe1; [|by auto..].
    intros r' n' rs rt (-> & [Hrel ?]%rrel_with_eq) Hval.
    simplify_eq/=. sim_bind (subst_map _ e2) (subst_map _ e2).
    eapply sim_simple_frame_more_core.
    eapply sim_simple_post_mono, IHe2; [|by auto..].
    intros r'' n' rs' rt' (-> & [Hrel' ?]%rrel_with_eq) Hval'.
    simplify_eq/=. eapply sim_simple_proj; [done..|].
    intros vi vv idx ?? Hidx ?. simplify_eq.
    split; first done.
    move:Hrel=>/= /Forall2_lookup=>Hrel.
    specialize (Hrel (Z.to_nat idx)).
    rewrite Hidx in Hrel. inversion Hrel. simplify_eq/=.
    constructor; last done. auto.
  - (* Conc *)
    move=>[Hwf1 Hwf2] xs Hxs /=. sim_bind (subst_map _ e1) (subst_map _ e1).
    eapply sim_simple_frame_core.
    eapply sim_simple_post_mono, IHe1; [|by auto..].
    intros r' n' rs rt (-> & [Hrel ?]%rrel_with_eq) Hval.
    simplify_eq/=. sim_bind (subst_map _ e2) (subst_map _ e2).
    eapply sim_simple_frame_more_core.
    eapply sim_simple_post_mono, IHe2; [|by auto..].
    intros r'' n' rs' rt' (-> & [Hrel' ?]%rrel_with_eq) Hval'.
    simplify_eq/=. eapply sim_simple_conc; [done..|].
    intros v1 v2 ??. simplify_eq/=.
    split; first done. simpl.
    apply Forall2_app; auto.
  - (* BinOp *)
    move=>[Hwf1 Hwf2] xs Hxs /=. sim_bind (subst_map _ e1) (subst_map _ e1).
    eapply sim_simple_frame_core.
    eapply sim_simple_post_mono, IHe1; [|by auto..].
    intros r' n' rs rt (-> & [Hrel ?]%rrel_with_eq) Hval.
    simplify_eq/=. sim_bind (subst_map _ e2) (subst_map _ e2).
    eapply sim_simple_frame_more_core.
    eapply sim_simple_post_mono, IHe2; [|by auto..].
    intros r'' n' rs' rt' (-> & [Hrel' ?]%rrel_with_eq) Hval'.
    simplify_eq/=. eapply sim_simple_bin_op; [done..|].
    intros v1 v2 s ? ?? Heval. simplify_eq/=.
    split; first done. constructor; last done.
    assert (arel (core r ⋅ core r' ⋅ r'') v1 v1) as Hrel_v1.
    { apply Forall2_cons_inv in Hrel as [??]. auto. }
    inversion Heval; simpl; auto; []. do 2 (split; first done).
    simplify_eq/=. apply Hrel_v1.
  - (* Place: can't happen *) done.
  - (* Deref *)
    move=>Hwf xs Hxswf /=. sim_bind (subst_map _ e) (subst_map _ e).
    eapply sim_simple_post_mono, IHe; [|by auto..].
    intros r' n' rs rt (-> & [Hrel ?]%rrel_with_eq).
    simplify_eq/=. apply: sim_simple_deref=>l t ?. simplify_eq/=.
    split; first done. done.
  - (* Ref *)
    move=>Hwf xs Hxswf /=. sim_bind (subst_map _ e) (subst_map _ e).
    eapply sim_simple_post_mono, IHe; [|by auto..].
    intros r' n' rs rt (-> & [Hrel ?]%rrel_with_eq).
    simplify_eq/=. eapply sim_simple_ref=>l t ??. simplify_eq/=.
    split; first done. apply Hrel.
  - (* Copy *)
    move=>Hwf xs Hxswf /=. sim_bind (subst_map _ e) (subst_map _ e).
    eapply sim_simple_post_mono, IHe; [|by auto..].
    intros r' n' rs rt (-> & [Hrel ?]%rrel_with_eq).
    eapply sim_simple_valid_post.
    eapply sim_simple_copy_public; [by auto..|].
    intros r'' v1 v2 Hrel'' Hval. simplify_eq/=.
    split; first done. auto.
  - (* Write *)
    move=>[Hwf1 Hwf2] xs Hxs /=. sim_bind (subst_map _ e1) (subst_map _ e1).
    eapply sim_simple_frame_core.
    eapply sim_simple_post_mono, IHe1; [|by auto..].
    intros r' n' rs rt (-> & [Hrel ?]%rrel_with_eq) Hval.
    simplify_eq/=. sim_bind (subst_map _ e2) (subst_map _ e2).
    eapply sim_simple_frame_more_core.
    eapply sim_simple_post_mono, IHe2; [|by auto..].
    intros r'' n' rs' rt' (-> & [Hrel' ?]%rrel_with_eq) Hval'.
    simplify_eq/=. eapply sim_simple_write_public; [auto..|].
    split; first done. constructor; done.
  - (* Alloc *)
    move=>Hwf xs Hxswf /=.
    eapply sim_simple_valid_post.
    eapply sim_simple_alloc_public=>l tg /= Hval.
    split; first done.
    simpl. split; last done. constructor; last done.
    eapply arel_mono, arel_ptr; auto.
  - (* Free *)
    move=>Hwf xs Hxswf /=.
    sim_bind (subst_map _ e) (subst_map _ e).
    eapply sim_simple_post_mono, IHe; [|by auto..].
    intros r' n' rs rt (-> & Hrel). simpl.
    apply: sim_simple_free_public; eauto.
    split; first done. constructor; done.
  - (* Retag *)
    move=>Hwf xs Hxswf /=.
    sim_bind (subst_map _ e) (subst_map _ e).
    eapply sim_simple_post_mono, IHe; [|by auto..].
    intros r' n' rs rt (-> & Hrel). simpl.
    eapply sim_simple_retag_public; eauto.
    split; first done. constructor; done.
  - (* Let *)
    move=>[Hwf1 Hwf2] xs Hxs /=. sim_bind (subst_map _ e1) (subst_map _ e1).
    eapply sim_simple_frame_core.
    eapply sim_simple_post_mono, IHe1; [|by auto..].
    intros r' n' rs rt (-> & Hrel) Hval. simpl.
    eapply sim_simple_let; [destruct rs, rt; by eauto..|].
    rewrite !subst'_subst_map.
    change rs with (fst (rs, rt)). change rt with (snd (rs, rt)) at 2.
    rewrite !binder_insert_map.
    eapply IHe2; [by auto..|].
    destruct b; first by auto. simpl.
    apply map_Forall_insert_2; first by auto.
    eapply srel_core_mono; eauto.
  - (* Case *)
    move=>[Hwf1 /Forall_id Hwf2] xs Hxs /=. sim_bind (subst_map _ e) (subst_map _ e).
    eapply sim_simple_frame_core.
    eapply sim_simple_post_mono, IHe; [|by auto..].
    intros r' n' rs rt (-> & [Hrel ?]%rrel_with_eq) Hval.
    simplify_eq/=. eapply sim_simple_case.
    { rewrite !fmap_length //. }
    intros es et ??. rewrite !list_lookup_fmap.
    destruct (el !! Z.to_nat i) eqn:Hlk; last done.
    intros. simplify_eq/=.
    eapply (Forall_lookup_1  _ _ _ _ H Hlk).
    + eapply (Forall_lookup_1  _ _ _ _ Hwf2 Hlk).
    + eauto.
Qed.

End sem.

Theorem sim_mod_fun_refl f :
  expr_wf f.(fun_body) →
  ⊨ᶠ f ≥ f.
Proof.
  intros Hwf. eapply (sim_fun_simple sem_steps); first done.
  intros fs ft r es et vs vt c Hlk Hrel Hsubst1 Hsubst2.
  (* eapply sim_simple_viewshift.
  { eapply viewshift_frame_l. eapply vs_call_empty_public. } *)
  eapply sim_simple_frame_r.
  destruct (subst_l_map _ _ _ _ _ _ _ (rrel r) Hsubst1 Hsubst2) as (map & -> & -> & Hmap).
  { clear -Hrel. induction Hrel; eauto using Forall2. }
  eapply sim_simple_post_mono; last exact: expr_wf_soundness.
  intros rr n rs rt [??] Hval. split.
  - solve_res.
  - eapply rrel_mono; [done| |done]. solve_res.
Qed.

Print Assumptions sim_mod_fun_refl.

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
