From Coq Require Import Program.Equality Lia.
From Paco Require Import paco.

From stbor.lang Require Import steps_wf.
From stbor.sim Require Import behavior global local invariant sflib global_adequacy.

Set Default Proof Using "Type".

Section local.
Context {A: ucmraT}.
Variable (wsat: A → state → state → Prop).
Variable (vrel: A → expr → expr → Prop).
Variable (fns fnt: fn_env).

Record frame: Type := mk_frame {
  rc: A;
  K_src: list (ectxi_language.ectx_item (bor_ectxi_lang fns));
  K_tgt: list (ectxi_language.ectx_item (bor_ectxi_lang fnt));
}.

Inductive sim_local_frames:
  forall (r_f:A)
    (K_src: list (ectxi_language.ectx_item (bor_ectxi_lang fns)))
    (K_tgt: list (ectxi_language.ectx_item (bor_ectxi_lang fnt)))
    (frames:list frame),
    Prop :=
| sim_local_frames_nil
    r_f
  : sim_local_frames r_f nil nil nil
| sim_local_frames_cons
    r_f K_f_src K_f_tgt
    frame frames
    (FRAMES: sim_local_frames r_f K_f_src K_f_tgt frames)
    (CONTINUATION:
       ∀ r_f' r' v_src v_tgt σ_src' σ_tgt'
         (* For any new resource r' and frame r_f' that are compatible with
             our local resource r and have world satisfaction *)
         (VALID': ✓ (r_f' ⋅ (frame.(rc) ⋅ r')))
         (WSAT' : wsat (r_f ⋅ (frame.(rc) ⋅ r')) σ_src' σ_tgt')
         (* and the returned values are related w.r.t. (r ⋅ r' ⋅ r_f) *)
         (VRET  : vrel r' (Val v_src) (Val v_tgt)),
         ∃ idx', sim_local_body wsat vrel fns fnt
                                (frame.(rc) ⋅ r') idx'
                                (fill frame.(K_src) (Val v_src)) σ_src'
                                (fill frame.(K_tgt) (Val v_tgt)) σ_tgt')
  : sim_local_frames
      (r_f ⋅ frame.(rc))
      (frame.(K_src) ++ K_f_src)
      (frame.(K_tgt) ++ K_f_tgt)
      (frame :: frames)
.

Inductive sim_local_conf:
  forall (idx:nat) (e_src:expr) (σ_src:state) (e_tgt:expr) (σ_tgt:state), Prop :=
| sim_local_conf_intro
    r_f K_src K_tgt frames
    rc idx e_src σ_src e_tgt σ_tgt
    Ke_src Ke_tgt
    (FRAMES: sim_local_frames r_f K_src K_tgt frames)
    (LOCAL: sim_local_body wsat vrel fns fnt rc idx e_src σ_src e_tgt σ_tgt)
    (KE_SRC: Ke_src = fill K_src e_src)
    (KE_TGT: Ke_tgt = fill K_tgt e_tgt)
  : sim_local_conf idx Ke_src σ_src Ke_tgt σ_tgt.

Lemma sim_local_conf_sim
      (FUNS: sim_local_funs wsat vrel fns fnt)
      (idx:nat) (e_src:expr) (σ_src:state) (e_tgt:expr) (σ_tgt:state)
      (SIM: sim_local_conf idx e_src σ_src e_tgt σ_tgt)
  : sim fns fnt idx (e_src, σ_src) (e_tgt, σ_tgt)
.
Proof.
  revert idx e_src σ_src e_tgt σ_tgt SIM. pcofix CIH. i.
  inv SIM. punfold LOCAL. inv LOCAL.
  - admit.
  - admit.
  - admit.
Admitted.

End local.

Section prog.
Context {A: ucmraT}.
Variable (wsat: A → state → state → Prop).
Variable (vrel: A → expr → expr → Prop).
Variable (fns fnt: fn_env).

Lemma sim_prog_sim
      prog_src prog_tgt
      (FUNS: sim_local_funs wsat vrel prog_src prog_tgt)
  : behave_prog prog_tgt <1= behave_prog prog_src.
Proof.
  unfold behave_prog. eapply adequacy. eapply sim_local_conf_sim; eauto.
  econs; eauto; swap 2 4.
  { econs 1. }
  { ss. }
  { ss. }
  admit.
Admitted.

End prog.
