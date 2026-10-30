/-
Copyright (c) 2026 Denise M. Case. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denise M. Case
-/
module

public import SE.InterpretiveKernel.Adjunction

/-!
# SE.InterpretiveKernel.Witness

Finite incompatibility witnesses and a bounded decision procedure.

A witness is two frames `e e'`, a selected probe `p`, a proof of `φ e e'`,
and a proof that the outputs are not `ρ`-related.

Axioms: everything except `not_coherent_iff_witness` is constructive.
That single converse uses classical logic (`Classical.byContradiction`).
-/

@[expose] public section

namespace SE.InterpretiveKernel

universe u v w

variable {E : Type u} {A : Type v} {P : Type w}

/-- A finite incompatibility witness against coherence of `φ` with `ρ`. -/
structure IncompatibilityWitness (I : P → E → A) (Q : P → Prop)
    (φ : E → E → Prop) (ρ : A → A → Prop) where
  /-- The first frame. -/
  frame₁   : E
  /-- The second frame. -/
  frame₂   : E
  /-- The probe whose outputs separate the two frames. -/
  probe    : P
  /-- The probe is selected by `Q`. -/
  selected : Q probe
  /-- The two frames are related by `φ`. -/
  related  : φ frame₁ frame₂
  /-- The outputs of the probe on the two frames are not related by `ρ`. -/
  separated : ¬ ρ (I probe frame₁) (I probe frame₂)

/-- A valid witness refutes coherence. -/
theorem IncompatibilityWitness.not_coherent
    {I : P → E → A} {Q : P → Prop} {φ : E → E → Prop} {ρ : A → A → Prop}
    (w : IncompatibilityWitness I Q φ ρ) : ¬ Coherent I Q φ ρ :=
  fun h => w.separated (h w.frame₁ w.frame₂ w.related w.probe w.selected)

/-- A valid witness refutes `L_Q(φ) ≤ ρ` when `ρ` is an equivalence relation. -/
theorem IncompatibilityWitness.not_lift_finer
    {I : P → E → A} {Q : P → Prop} {φ : E → E → Prop} {ρ : A → A → Prop}
    (w : IncompatibilityWitness I Q φ ρ) (hρ : Equivalence ρ) :
    ¬ Finer (liftRel I Q φ) ρ :=
  fun h => w.not_coherent ((adjunction I Q hρ).1 h)

/-- Converse (classical): failure of coherence yields a witness. -/
theorem not_coherent_iff_witness
    {I : P → E → A} {Q : P → Prop} {φ : E → E → Prop} {ρ : A → A → Prop} :
    ¬ Coherent I Q φ ρ ↔ Nonempty (IncompatibilityWitness I Q φ ρ) := by
  constructor
  · intro hn
    apply Classical.byContradiction
    intro hne
    apply hn
    intro e e' hφ p hp
    apply Classical.byContradiction
    intro hsep
    exact hne ⟨⟨e, e', p, hp, hφ, hsep⟩⟩
  · intro ⟨w⟩
    exact w.not_coherent

/-! ## Bounded decision procedure

Over explicit enumerations of frames and probes, with decidable `Q`, `φ`, `ρ`,
coherence is decidable and the decision produces either coherence or a witness.
Not an instance; the enumeration is data. -/

section Bounded

variable (I : P → E → A) (Q : P → Prop) (φ : E → E → Prop) (ρ : A → A → Prop)

/-- Search statement over the lists `es` and `ps`. -/
def WitnessOn (es : List E) (ps : List P) : Prop :=
  ∃ e, e ∈ es ∧ ∃ e', e' ∈ es ∧ ∃ p, p ∈ ps ∧ Q p ∧ φ e e' ∧ ¬ ρ (I p e) (I p e')

/-- Decidability of `WitnessOn` given decidable `Q`, `φ`, and `ρ`. -/
instance witnessOnDecidable [DecidablePred Q] [DecidableRel φ] [DecidableRel ρ]
    (es : List E) (ps : List P) : Decidable (WitnessOn I Q φ ρ es ps) := by
  unfold WitnessOn
  infer_instance

/-- With complete enumerations, either `φ` is coherent with `ρ` or a witness
exists; the dichotomy is decided by `WitnessOn`. -/
theorem coherent_or_witness [DecidablePred Q] [DecidableRel φ] [DecidableRel ρ]
    (es : List E) (ps : List P)
    (hes : ∀ e, e ∈ es) (hps : ∀ p, Q p → p ∈ ps) :
    Coherent I Q φ ρ ∨ Nonempty (IncompatibilityWitness I Q φ ρ) := by
  rcases Decidable.em (WitnessOn I Q φ ρ es ps) with h | h
  · obtain ⟨e, _, e', _, p, _, hp, hφ, hsep⟩ := h
    exact Or.inr ⟨⟨e, e', p, hp, hφ, hsep⟩⟩
  · left
    intro e e' hφ p hp
    apply Decidable.byContradiction
    intro hsep
    exact h ⟨e, hes e, e', hes e', p, hps p hp, hp, hφ, hsep⟩

/-- Over complete enumerations, `WitnessOn` decides non-coherence. -/
theorem not_coherent_iff_witnessOn
    (es : List E) (ps : List P)
    (hes : ∀ e, e ∈ es) (hps : ∀ p, Q p → p ∈ ps) :
    ¬ Coherent I Q φ ρ ↔ WitnessOn I Q φ ρ es ps := by
  constructor
  · intro hn
    apply Classical.byContradiction
    intro hno
    apply hn
    intro e e' hφ p hp
    apply Classical.byContradiction
    intro hsep
    exact hno ⟨e, hes e, e', hes e', p, hps p hp, hp, hφ, hsep⟩
  · intro ⟨e, _, e', _, p, _, hp, hφ, hsep⟩ hc
    exact hsep (hc e e' hφ p hp)

end Bounded

end SE.InterpretiveKernel
