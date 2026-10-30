/-
Copyright (c) 2026 Denise M. Case. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denise M. Case
-/
module

public import SE.InterpretiveKernel.Core

/-!
# SE.InterpretiveKernel.Kernel

The interpretation-induced kernel `K_Q(ρ)` on frames and the coherence condition.

Data (all explicit; no empirical meaning is assumed):
* `E` frames/environments, `A` interpreted outputs/occurrences, `P` probes;
* `I : P → E → A` interpretation (not assumed injective, surjective, or correct);
* `Q : P → Prop` the selected probe family (a predicate on probes);
* `ρ` a relation on `A`.

Probe-family inclusion (stipulation): `Q ⊆ Q'` is `∀ p, Q p → Q' p`.
Probe families are NOT ordered by `Finer`; they are ordered by inclusion only.
-/

@[expose] public section

namespace SE.InterpretiveKernel

universe u v w

variable {E : Type u} {A : Type v} {P : Type w}

/-- `kernelRel I Q ρ e e'` : every selected probe sends `e` and `e'`
to `ρ`-related outputs. -/
def kernelRel (I : P → E → A) (Q : P → Prop) (ρ : A → A → Prop) : E → E → Prop :=
  fun e e' => ∀ p, Q p → ρ (I p e) (I p e')

/-- Coherence of a frame relation `φ` with an occurrence relation `ρ` through
`I` and `Q`:  `φ ≤ K_Q(ρ)`, i.e. `Finer φ (kernelRel I Q ρ)`.
A mathematical compatibility condition only. -/
def Coherent (I : P → E → A) (Q : P → Prop)
    (φ : E → E → Prop) (ρ : A → A → Prop) : Prop :=
  Finer φ (kernelRel I Q ρ)

/-- Unfolded form of coherence. -/
theorem coherent_iff (I : P → E → A) (Q : P → Prop)
    (φ : E → E → Prop) (ρ : A → A → Prop) :
    Coherent I Q φ ρ ↔ ∀ e e', φ e e' → ∀ p, Q p → ρ (I p e) (I p e') :=
  Iff.rfl

/-- `K_Q(ρ)` is an equivalence relation whenever `ρ` is. -/
theorem kernelRel_equivalence (I : P → E → A) (Q : P → Prop)
    {ρ : A → A → Prop} (hρ : Equivalence ρ) :
    Equivalence (kernelRel I Q ρ) where
  refl  := fun e p _ => hρ.refl (I p e)
  symm  := fun h p hp => hρ.symm (h p hp)
  trans := fun h1 h2 p hp => hρ.trans (h1 p hp) (h2 p hp)

/-- `K` is monotone in `ρ`: finer occurrence relation gives finer kernel. -/
theorem kernelRel_monotone (I : P → E → A) (Q : P → Prop)
    {ρ ρ' : A → A → Prop} (h : Finer ρ ρ') :
    Finer (kernelRel I Q ρ) (kernelRel I Q ρ') :=
  fun _ _ hee' p hp => h _ _ (hee' p hp)

/-- More probes, finer kernel: if `Q ⊆ Q'` then `K_{Q'}(ρ) ≤ K_Q(ρ)`.
(Relation inclusion, not partition-direction confusion: a larger probe family
imposes more conditions, so fewer frame pairs are related.) -/
theorem kernelRel_antitone_probes (I : P → E → A) {Q Q' : P → Prop}
    (hQ : ∀ p, Q p → Q' p) (ρ : A → A → Prop) :
    Finer (kernelRel I Q' ρ) (kernelRel I Q ρ) :=
  fun _ _ h p hp => h p (hQ p hp)

/-- Coherence is monotone in the probe family in the stronger direction:
coherence at a larger family gives coherence at a smaller one. -/
theorem coherent_of_probes_subset (I : P → E → A) {Q Q' : P → Prop}
    (hQ : ∀ p, Q p → Q' p) {φ : E → E → Prop} {ρ : A → A → Prop}
    (h : Coherent I Q' φ ρ) : Coherent I Q φ ρ :=
  Finer.trans h (kernelRel_antitone_probes I hQ ρ)

/-- Coherence is preserved by refining the frame relation. -/
theorem coherent_of_finer_frames (I : P → E → A) (Q : P → Prop)
    {φ φ' : E → E → Prop} {ρ : A → A → Prop}
    (hφ : Finer φ φ') (h : Coherent I Q φ' ρ) : Coherent I Q φ ρ :=
  Finer.trans hφ h

/-- Coherence is preserved by coarsening the occurrence relation. -/
theorem coherent_of_coarser_occurrences (I : P → E → A) (Q : P → Prop)
    {φ : E → E → Prop} {ρ ρ' : A → A → Prop}
    (hρ : Finer ρ ρ') (h : Coherent I Q φ ρ) : Coherent I Q φ ρ' :=
  Finer.trans h (kernelRel_monotone I Q hρ)

/-- Degenerate satisfier 1: against the total occurrence relation, every frame
relation is coherent.  Coherence alone can be vacuous. -/
theorem coherent_total_occurrence (I : P → E → A) (Q : P → Prop)
    (φ : E → E → Prop) : Coherent I Q φ (fun _ _ => True) :=
  fun _ _ _ _ _ => True.intro

/-- Degenerate satisfier 2: with no selected probes, every pair is coherent. -/
theorem coherent_no_probes (I : P → E → A) {Q : P → Prop}
    (hQ : ∀ p, ¬ Q p) (φ : E → E → Prop) (ρ : A → A → Prop) :
    Coherent I Q φ ρ :=
  fun _ _ _ p hp => absurd hp (hQ p)

/-- Bundled form of the kernel. -/
def kernelSetoid (I : P → E → A) (Q : P → Prop) (ρ : Setoid A) : Setoid E where
  r     := kernelRel I Q ρ.r
  iseqv := kernelRel_equivalence I Q ρ.iseqv

end SE.InterpretiveKernel
