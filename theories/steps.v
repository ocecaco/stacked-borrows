From stbor Require Import lang notation.

Class Wellformed A := Wf : A →  Prop.
Existing Class Wf.

Record state_wf' σ := {
  state_wf_dom : dom (gset loc) σ.(cheap) ≡ dom (gset loc) σ.(cstk);
  state_wf_mem_bor:
    ∀ l l' bor, σ.(cheap) !! l = Some (LitV (LitLoc l' bor)) →
      match bor with
      | UniqB t | AliasB (Some t) => (t < σ.(cclk))%nat
      | _ => True
      end;
  state_wf_stack_frozen:
    ∀ l stack, σ.(cstk) !! l = Some stack →
      match stack.(frozen_since) with Some t => (t < σ.(cclk))%nat | _ => True end;
  state_wf_stack_item:
    ∀ l stack si, σ.(cstk) !! l = Some stack → si ∈ stack.(borrows) →
      match si with
      | Uniq t => (t < σ.(cclk))%nat
      | FnBarrier c => is_Some (σ.(cbar) !! c)
      | _ => True
      end;
}.

Instance state_wf : Wellformed state :=  state_wf'.
