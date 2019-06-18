From stbor.lang Require Export lang.

Set Default Proof Using "Type".

(** Wellformedness *)
Class Wellformed A := Wf : A → Prop.
Existing Class Wf.

Definition wf_mem_tag (h: mem) (nxtp: ptr_id) :=
  ∀ l l' bor, h !! l = Some (ScPtr l' bor) → bor <b nxtp.

Definition stack_item_included (stk: stack) (nxtp: ptr_id) (nxtc: call_id) :=
  ∀ si, si ∈ stk → match si.(tg) with
                    | Tagged t => (t < nxtp)%nat
                    | _ => True
                   end ∧
                   match si.(protector) with
                    | Some c => (c < nxtc)%nat
                    | _ => True
                   end.
Definition wf_stack_item (α: stacks) (nxtp: ptr_id) (nxtc: call_id) :=
  ∀ l stk, α !! l = Some stk → stack_item_included stk nxtp nxtc.
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
Notation terminal e := (is_Some (to_val e)).

Lemma expr_terminal_False (e: expr) : ¬ terminal e ↔ to_result e = None.
Proof.
  split.
  - destruct (to_val e) eqn:Eqv; [|done].
    intros TERM. exfalso. apply TERM. by eexists.
  - intros Eq1 [? Eq2]. by rewrite /to_val /= Eq1 in Eq2.
Qed.

(** Thread steps *)
Inductive tstep (eσ1 eσ2 : expr * config) : Prop :=
| ThreadStep ev efs
    (PRIM: prim_step eσ1.1 eσ1.2 ev eσ2.1 eσ2.2 efs)
.

Infix "~t~>" := tstep (at level 70).
Infix "~t~>*" := (rtc tstep) (at level 70).

(*=================================== UNUSED =================================*)
(* Implicit Type (ρ: cfg bor_lang). *)

(* TODO: this may need strengthening *)
(* Definition cfg_wf' ρ : Prop := Wf ρ.2. *)
(* Instance cfg_wf : Wellformed (cfg bor_lang) :=  cfg_wf'. *)

(* Definition threads_terminal' (el: list expr) := ∀ e, e ∈ el → terminal e. *)
(* Instance threads_terminal : Terminal (list expr) := threads_terminal'. *)
(* Definition cfg_terminal' ρ : Prop := terminal ρ.1. *)
(* Instance cfg_terminal : Terminal (cfg bor_lang) := cfg_terminal'. *)