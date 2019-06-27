From Coq Require Import Program.Equality Lia.
From Paco Require Import paco.

From stbor.lang Require Import steps_wf.
From stbor.sim Require Import local global invariant sflib.

Set Default Proof Using "Type".

Section BEHAVIOR.
  Context {Config State Value: Type}
           (step: forall (conf:Config) (s s':State), Prop)
           (term: forall (conf:Config) (s:State) (val:Value), Prop)
  .

  Inductive observation: Type :=
  | obs_term (retval:Value)
  | obs_inftau
  .

  Inductive behmatch
            (conf:Config)
            (behave: forall (s:State) (obs:observation), Prop)
    : forall (s:State) (obs:observation), Prop :=
  | beh_stuck
      s obs
      (NT: forall val, ¬ term conf s val)
      (NS: ∀ s', ¬ step conf s s')
    : behmatch conf behave s obs
  | beh_term
      s v
      (TERM: term conf s v)
    : behmatch conf behave s (obs_term v)
  | beh_inftau
      s s'
      (STEP: step conf s s')
      (INF: behave s' obs_inftau)
    : behmatch conf behave s obs_inftau
  .
  Hint Constructors behmatch.

  Inductive behave_ (conf:Config) behave (s:State) (obs:observation): Prop :=
  | behave_intro
      s'
      (TAU: rtc (step conf) s s')
      (MAT: behmatch conf behave s' obs)
  .
  Hint Constructors behave_.

  Lemma behave_mon conf: monotone2 (behave_ conf).
  Proof.
    repeat intro. destruct IN. destruct MAT; eauto.
  Qed.
  Hint Resolve behave_mon: paco.

  Definition behave (conf:Config): forall (s:State) (obs:observation), Prop := paco2 (behave_ conf) bot2.
End BEHAVIOR.
Hint Constructors behmatch.
Hint Constructors behave_.
Hint Resolve behave_mon: paco.

Definition init_expr := (Call #["main"] []).
Definition init_state := (mkState ∅ ∅ [] O O).
Definition term (prog:fn_env) (s:expr * state) (v:result): Prop :=
  to_result s.1 = Some v.

Definition behave_prog (prog:fn_env) (obs:@observation result): Prop :=
  behave tstep term prog (init_expr, init_state) obs.
