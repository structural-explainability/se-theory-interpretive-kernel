/-
Copyright (c) 2026 Denise M. Case. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denise M. Case
-/
module

public import SE.InterpretiveKernel.Kernel

/-!
# SE.InterpretiveKernel.Signature

Bridges between the Lean definition of `K` and the paper's definition.

The paper defines the kernel as the kernel equivalence of the probe signature

    Σ_{P,ρ} : E → (A/ρ)^P,    Σ(F)(p) = [I(p,F)]_ρ,

over a FIXED finite probe family `P`.  Lean takes an ambient probe type `P` and
a selecting predicate `Q`.  The bridges show the two agree:

* `kernelRel_iff_signature_eq`: `K` is the kernel of the signature map;
* `kernelRel_iff_restrict`: selecting by `Q` is the same as using the
  subtype `{p // Q p}` as the probe family.
-/

@[expose] public section

namespace SE.InterpretiveKernel

universe u v w

variable {E : Type u} {A : Type v} {P : Type w}

/-- The paper's probe signature: each frame goes to the function sending every
selected probe to the `ρ`-class of its output. -/
def probeSignature (I : P → E → A) (Q : P → Prop) (ρ : Setoid A) (e : E) :
    (p : {p : P // Q p}) → Quotient ρ :=
  fun p => Quotient.mk ρ (I p.1 e)

/-- `K_Q(ρ)` is the kernel of the probe signature. -/
theorem kernelRel_iff_signature_eq (I : P → E → A) (Q : P → Prop)
    (ρ : Setoid A) (e e' : E) :
    kernelRel I Q ρ.r e e' ↔ probeSignature I Q ρ e = probeSignature I Q ρ e' := by
  constructor
  · intro h
    funext p
    exact Quotient.sound (h p.1 p.2)
  · intro h p hp
    exact Quotient.exact (congrFun h ⟨p, hp⟩)

/-- Selecting probes by `Q` equals taking the whole subtype of selected
probes as the family (the paper's fixed probe family). -/
theorem kernelRel_iff_restrict (I : P → E → A) (Q : P → Prop)
    (ρ : A → A → Prop) (e e' : E) :
    kernelRel I Q ρ e e' ↔
      kernelRel (fun (p : {p : P // Q p}) => I p.1) (fun _ => True) ρ e e' :=
  ⟨fun h p _ => h p.1 p.2,
   fun h p hp => h ⟨p, hp⟩ True.intro⟩

end SE.InterpretiveKernel
