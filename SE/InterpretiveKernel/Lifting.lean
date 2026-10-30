/-
Copyright (c) 2026 Denise M. Case. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denise M. Case
-/
module

public import SE.InterpretiveKernel.Kernel

/-!
# SE.InterpretiveKernel.Lifting

The least compatible occurrence relation `L_Q(φ)`: the equivalence closure of
the generating pairs `(I p e, I p e')` for selected `p` and `φ e e'`.
-/

@[expose] public section

namespace SE.InterpretiveKernel

universe u v w

variable {E : Type u} {A : Type v} {P : Type w}

/-- Generating pairs of occurrences: `(I p e, I p e')` with `Q p` and `φ e e'`. -/
def generators (I : P → E → A) (Q : P → Prop) (φ : E → E → Prop) : A → A → Prop :=
  fun a a' => ∃ p e e', Q p ∧ φ e e' ∧ I p e = a ∧ I p e' = a'

/-- `L_Q(φ)`: equivalence closure of the generating pairs. -/
def liftRel (I : P → E → A) (Q : P → Prop) (φ : E → E → Prop) : A → A → Prop :=
  EqvClosure (generators I Q φ)

/-- `L_Q(φ)` is an equivalence relation (for any `φ`). -/
theorem liftRel_equivalence (I : P → E → A) (Q : P → Prop) (φ : E → E → Prop) :
    Equivalence (liftRel I Q φ) :=
  EqvClosure.equivalence _

/-- Each generating pair is related by `L_Q(φ)`. -/
theorem liftRel_of_pair (I : P → E → A) (Q : P → Prop) {φ : E → E → Prop}
    {p : P} {e e' : E} (hp : Q p) (h : φ e e') :
    liftRel I Q φ (I p e) (I p e') :=
  EqvClosure.of ⟨p, e, e', hp, h, rfl, rfl⟩

/-- Generating pairs are contained in `L_Q(φ)`. -/
theorem generators_finer_liftRel (I : P → E → A) (Q : P → Prop) (φ : E → E → Prop) :
    Finer (generators I Q φ) (liftRel I Q φ) :=
  EqvClosure.subset _

/-- Minimality, core form: an equivalence relation `ρ` on `A` that relates
every generating pair contains `L_Q(φ)`. -/
theorem liftRel_le_of_generators (I : P → E → A) (Q : P → Prop) {φ : E → E → Prop}
    {ρ : A → A → Prop} (hρ : Equivalence ρ)
    (h : ∀ p e e', Q p → φ e e' → ρ (I p e) (I p e')) :
    Finer (liftRel I Q φ) ρ := by
  apply EqvClosure.le_of_equivalence hρ
  intro a a' ⟨p, e, e', hp, hφ, ha, ha'⟩
  subst ha
  subst ha'
  exact h p e e' hp hφ

/-- `ρ` is a compatible occurrence relation for `φ`: an equivalence relation
with which `φ` is coherent. -/
def Compatible (I : P → E → A) (Q : P → Prop)
    (φ : E → E → Prop) (ρ : A → A → Prop) : Prop :=
  Equivalence ρ ∧ Coherent I Q φ ρ

/-- `L_Q(φ)` is itself compatible with `φ`. -/
theorem liftRel_compatible (I : P → E → A) (Q : P → Prop) (φ : E → E → Prop) :
    Compatible I Q φ (liftRel I Q φ) :=
  ⟨liftRel_equivalence I Q φ,
   fun _ _ h _ hp => liftRel_of_pair I Q hp h⟩

/-- Minimality: `L_Q(φ)` is below every compatible occurrence relation. -/
theorem liftRel_le_of_compatible (I : P → E → A) (Q : P → Prop)
    {φ : E → E → Prop} {ρ : A → A → Prop}
    (h : Compatible I Q φ ρ) : Finer (liftRel I Q φ) ρ :=
  liftRel_le_of_generators I Q h.1 (fun p e e' hp hφ => h.2 e e' hφ p hp)

/-- `L_Q(φ)` is the least compatible occurrence relation. -/
theorem liftRel_isLeast (I : P → E → A) (Q : P → Prop) (φ : E → E → Prop) :
    Compatible I Q φ (liftRel I Q φ) ∧
      ∀ ρ, Compatible I Q φ ρ → Finer (liftRel I Q φ) ρ :=
  ⟨liftRel_compatible I Q φ, fun _ h => liftRel_le_of_compatible I Q h⟩

/-- Uniqueness of the least compatible relation. -/
theorem liftRel_unique (I : P → E → A) (Q : P → Prop) {φ : E → E → Prop}
    {σ : A → A → Prop} (hσ : Compatible I Q φ σ)
    (hmin : ∀ ρ, Compatible I Q φ ρ → Finer σ ρ) :
    σ = liftRel I Q φ :=
  Finer.antisymm (hmin _ (liftRel_compatible I Q φ)) (liftRel_le_of_compatible I Q hσ)

/-- `L` is monotone in `φ`: finer frame relation gives finer lifted relation. -/
theorem liftRel_monotone (I : P → E → A) (Q : P → Prop)
    {φ φ' : E → E → Prop} (h : Finer φ φ') :
    Finer (liftRel I Q φ) (liftRel I Q φ') := by
  apply EqvClosure.monotone
  intro a a' ⟨p, e, e', hp, hφ, ha, ha'⟩
  exact ⟨p, e, e', hp, h e e' hφ, ha, ha'⟩

/-- More probes, larger lifted relation: if `Q ⊆ Q'` then `L_Q(φ) ≤ L_{Q'}(φ)`. -/
theorem liftRel_monotone_probes (I : P → E → A) {Q Q' : P → Prop}
    (hQ : ∀ p, Q p → Q' p) (φ : E → E → Prop) :
    Finer (liftRel I Q φ) (liftRel I Q' φ) := by
  apply EqvClosure.monotone
  intro a a' ⟨p, e, e', hp, hφ, ha, ha'⟩
  exact ⟨p, e, e', hQ p hp, hφ, ha, ha'⟩

/-- Bundled form of the lifted relation. -/
def liftSetoid (I : P → E → A) (Q : P → Prop) (φ : E → E → Prop) : Setoid A where
  r     := liftRel I Q φ
  iseqv := liftRel_equivalence I Q φ

end SE.InterpretiveKernel
