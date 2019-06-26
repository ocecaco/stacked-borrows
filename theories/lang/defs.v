From stbor.lang Require Export lang.

Set Default Proof Using "Type".

(** Wellformedness *)
Class Wellformed A := Wf : A → Prop.
Existing Class Wf.

Definition wf_mem_tag (h: mem) (nxtp: ptr_id) :=
  ∀ l l' pid, h !! l = Some (ScPtr l' (Tagged pid)) → (pid < nxtp)%nat.

Definition stack_item_included (stk: stack) (nxtp: ptr_id) (nxtc: call_id) :=
  ∀ si, si ∈ stk → match si.(tg) with
                    | Tagged t => (t < nxtp)%nat
                    | _ => True
                   end ∧
                   match si.(protector) with
                    | Some c => (c < nxtc)%nat
                    | _ => True
                   end.
Definition stack_item_no_dup (stk : stack) :=
  ∀ it1 it2 t, it1 ∈ stk → it2 ∈ stk →
    it1.(tg) = Tagged t → it2.(tg) = Tagged t → it1 = it2.
Definition wf_stack_item (α: stacks) (nxtp: ptr_id) (nxtc: call_id) :=
  ∀ l stk, α !! l = Some stk → stack_item_included stk nxtp nxtc ∧ stack_item_no_dup stk.
Definition wf_non_empty (α: stacks) :=
  ∀ l stk, α !! l = Some stk → stk ≠ [].
Definition wf_no_dup (α: stacks) :=
  ∀ l stk, α !! l = Some stk → NoDup stk.
Definition wf_cid_incl (cids: call_id_stack) (nxtc: call_id) :=
  ∀ c : call_id, c ∈ cids → (c < nxtc)%nat.

Record state_wf' (s: state) := {
  state_wf_dom : dom (gset loc) s.(shp) ≡ dom (gset loc) s.(sst);
  state_wf_mem_tag : wf_mem_tag s.(shp) s.(snp);
  state_wf_stack_item : wf_stack_item s.(sst) s.(snp) s.(snc);
  state_wf_non_empty : wf_non_empty s.(sst);
  state_wf_cid_no_dup : NoDup s.(scs) ;
  state_wf_cid_agree: wf_cid_incl s.(scs) s.(snc);
  (* state_wf_cid_non_empty : s.(scs) ≠ []; *)
  (* state_wf_no_dup : wf_no_dup σ.(cst).(sst); *)
}.

Instance state_wf : Wellformed state :=  state_wf'.
Instance config_wf : Wellformed config := λ cfg, Wf cfg.(cst).

Fixpoint active_SRO (stk: stack) : gset ptr_id :=
  match stk with
  | [] => ∅
  | it :: stk =>
    match it.(perm) with
    | SharedReadOnly => match it.(tg) with
                        | Tagged t => {[t]} ∪ active_SRO stk
                        | Untagged => active_SRO stk
                        end
    | _ => ∅
    end
  end.

Notation terminal e := (is_Some (to_result e)).
Lemma expr_terminal_False (e: expr) : ¬ terminal e ↔ to_result e = None.
Proof.
  split.
  - destruct (to_result e) eqn:Eqv; [|done].
    intros TERM. exfalso. apply TERM. by eexists.
  - intros Eq1 [? Eq2]. by rewrite Eq1 in Eq2.
Qed.

(** Thread steps *)
Inductive tstep (fns: fn_env) (eσ1 eσ2 : expr * state) : Prop :=
| ThreadStep ev efs
    (PRIM: prim_step (Λ:= bor_ectx_lang fns) eσ1.1 eσ1.2 ev eσ2.1 eσ2.2 efs)
.

Notation "x ~{ fn }~> y" := (tstep fn x y) (at level 70, format "x  ~{ fn }~>  y").
Notation "x ~{ fn }~>* y" := (rtc (tstep fn) x y)
  (at level 70, format "x  ~{ fn }~>*  y").
Notation "x ~{ fn }~>+ y" := (tc (tstep fn) x y)
  (at level 70, format "x  ~{ fn }~>+  y").


(*=================================== UNUSED =================================*)
(* Implicit Type (ρ: cfg bor_lang). *)

(* TODO: this may need strengthening *)
(* Definition cfg_wf' ρ : Prop := Wf ρ.2. *)
(* Instance cfg_wf : Wellformed (cfg bor_lang) :=  cfg_wf'. *)

(* Definition threads_terminal' (el: list expr) := ∀ e, e ∈ el → terminal e. *)
(* Instance threads_terminal : Terminal (list expr) := threads_terminal'. *)
(* Definition cfg_terminal' ρ : Prop := terminal ρ.1. *)
(* Instance cfg_terminal : Terminal (cfg bor_lang) := cfg_terminal'. *)
