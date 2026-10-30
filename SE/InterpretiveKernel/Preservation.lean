/-
Copyright (c) 2026 Denise M. Case. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denise M. Case
-/
module

public import SE.InterpretiveKernel.Lattice
public import SE.InterpretiveKernel.Adjunction

/-!
# SE.InterpretiveKernel.Preservation

Consequences of the adjunction, stated for relations.

* `K` preserves meets (including the empty meet, hence `K ⊤ = ⊤`).
* `L` preserves joins (including the empty join, hence `L ⊥ = ⊥`).
* Probe-family duality: a union of probe families gives a meet of kernels and
  a join of generated regimes; the empty family gives `⊤` and `⊥`.

Directionality: these are the laws the adjunction forces.  The converses
(`K` preserving joins, `L` preserving meets) are false in general; finite
counterexamples are in `SETest/InterpretiveKernel/ExamplesPaper.lean`.
-/

@[expose] public section

namespace SE.InterpretiveKernel

universe u v w x

variable {E : Type u} {A : Type v} {P : Type w}

/-! ## Meet preservation by K -/

/-- `K` preserves meets, pointwise form. No hypothesis on the family. -/
theorem kernelRel_meet_iff (I : P → E → A) (Q : P → Prop)
    {ι : Sort x} (ρs : ι → A → A → Prop) (e e' : E) :
    kernelRel I Q (meetRel ρs) e e' ↔ meetRel (fun i => kernelRel I Q (ρs i)) e e' :=
  ⟨fun h i p hp => h p hp i,
   fun h p hp i => h i p hp⟩

/-- `K` preserves meets, as an equality of relations. -/
theorem kernelRel_meet (I : P → E → A) (Q : P → Prop)
    {ι : Sort x} (ρs : ι → A → A → Prop) :
    kernelRel I Q (meetRel ρs) = meetRel (fun i => kernelRel I Q (ρs i)) := by
  funext e e'
  exact propext (kernelRel_meet_iff I Q ρs e e')

/-- `K ⊤ = ⊤` (empty meet). -/
theorem kernelRel_total (I : P → E → A) (Q : P → Prop) :
    kernelRel I Q (totalRel A) = totalRel E := by
  funext e e'
  exact propext ⟨fun _ => True.intro, fun _ _ _ => True.intro⟩

/-! ## Join preservation by L -/

/-- `L ⊥ = ⊥`: the generated regime of equality on frames is equality on outputs. -/
theorem liftRel_diagonal (I : P → E → A) (Q : P → Prop) :
    liftRel I Q (diagonalRel E) = diagonalRel A := by
  apply Finer.antisymm
  · apply liftRel_le_of_generators I Q (diagonalRel_equivalence A)
    intro p e e' _ h
    cases h
    exact rfl
  · exact finer_diagonalRel (liftRel_equivalence I Q (diagonalRel E)).refl

/-- Upper bounds of `L(⋁ φᵢ)` and `⋁ L(φᵢ)` among equivalences coincide. -/
theorem liftRel_joinRel_upper (I : P → E → A) (Q : P → Prop)
    {ι : Sort x} (φs : ι → E → E → Prop)
    {ρ : A → A → Prop} (hρ : Equivalence ρ) :
    Finer (liftRel I Q (joinRel φs)) ρ ↔
      Finer (joinRel (fun i => liftRel I Q (φs i))) ρ := by
  have hK : Equivalence (kernelRel I Q ρ) := kernelRel_equivalence I Q hρ
  rw [adjunction I Q hρ, joinRel_finer_iff hK, joinRel_finer_iff hρ]
  constructor
  · intro h i
    exact (adjunction I Q hρ).2 (h i)
  · intro h i
    exact (adjunction I Q hρ).1 (h i)

/-- `L` preserves joins of arbitrary families. -/
theorem liftRel_joinRel (I : P → E → A) (Q : P → Prop)
    {ι : Sort x} (φs : ι → E → E → Prop) :
    liftRel I Q (joinRel φs) = joinRel (fun i => liftRel I Q (φs i)) :=
  eq_of_same_upper_bounds
    (liftRel_equivalence I Q _)
    (joinRel_equivalence _)
    (fun _ hT => liftRel_joinRel_upper I Q φs hT)

/-! ## Probe-family duality -/

/-- Union of two probe families. -/
def probeUnion (Q Q' : P → Prop) : P → Prop :=
  fun p => Q p ∨ Q' p

/-- `K_{Q ∪ Q'}(ρ) = K_Q(ρ) ∧ K_{Q'}(ρ)`, pointwise. -/
theorem kernelRel_probeUnion_iff (I : P → E → A) (Q Q' : P → Prop)
    (ρ : A → A → Prop) (e e' : E) :
    kernelRel I (probeUnion Q Q') ρ e e' ↔
      meetRel2 (kernelRel I Q ρ) (kernelRel I Q' ρ) e e' :=
  ⟨fun h => ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩,
   fun h p hp => hp.elim (fun hq => h.1 p hq) (fun hq => h.2 p hq)⟩

/-- `K_{Q ∪ Q'}(ρ) = K_Q(ρ) ∧ K_{Q'}(ρ)`. -/
theorem kernelRel_probeUnion (I : P → E → A) (Q Q' : P → Prop)
    (ρ : A → A → Prop) :
    kernelRel I (probeUnion Q Q') ρ = meetRel2 (kernelRel I Q ρ) (kernelRel I Q' ρ) := by
  funext e e'
  exact propext (kernelRel_probeUnion_iff I Q Q' ρ e e')

/-- `L_{Q ∪ Q'}(φ) = L_Q(φ) ∨ L_{Q'}(φ)`. -/
theorem liftRel_probeUnion (I : P → E → A) (Q Q' : P → Prop) (φ : E → E → Prop) :
    liftRel I (probeUnion Q Q') φ = joinRel2 (liftRel I Q φ) (liftRel I Q' φ) := by
  apply eq_of_same_upper_bounds
    (liftRel_equivalence I _ φ) (joinRel2_equivalence _ _)
  intro ρ hρ
  rw [joinRel2_finer_iff hρ, adjunction I _ hρ, adjunction I Q hρ, adjunction I Q' hρ]
  constructor
  · intro h
    exact ⟨fun e e' hφ p hp => h e e' hφ p (Or.inl hp),
           fun e e' hφ p hp => h e e' hφ p (Or.inr hp)⟩
  · intro ⟨h1, h2⟩ e e' hφ p hp
    exact hp.elim (fun hq => h1 e e' hφ p hq) (fun hq => h2 e e' hφ p hq)

/-- Indexed union of probe families. -/
def probeUnionFamily {ι : Sort x} (Qs : ι → P → Prop) : P → Prop :=
  fun p => ∃ i, Qs i p

/-- `K_{⋃ Qᵢ}(ρ) = ⋀ K_{Qᵢ}(ρ)`, pointwise. -/
theorem kernelRel_probeUnionFamily_iff (I : P → E → A)
    {ι : Sort x} (Qs : ι → P → Prop) (ρ : A → A → Prop) (e e' : E) :
    kernelRel I (probeUnionFamily Qs) ρ e e' ↔
      meetRel (fun i => kernelRel I (Qs i) ρ) e e' :=
  ⟨fun h i p hp => h p ⟨i, hp⟩,
   fun h p ⟨i, hp⟩ => h i p hp⟩

/-- `K_{⋃ Qᵢ}(ρ) = ⋀ K_{Qᵢ}(ρ)`. -/
theorem kernelRel_probeUnionFamily (I : P → E → A)
    {ι : Sort x} (Qs : ι → P → Prop) (ρ : A → A → Prop) :
    kernelRel I (probeUnionFamily Qs) ρ = meetRel (fun i => kernelRel I (Qs i) ρ) := by
  funext e e'
  exact propext (kernelRel_probeUnionFamily_iff I Qs ρ e e')

/-- `L_{⋃ Qᵢ}(φ) = ⋁ L_{Qᵢ}(φ)`. -/
theorem liftRel_probeUnionFamily (I : P → E → A)
    {ι : Sort x} (Qs : ι → P → Prop) (φ : E → E → Prop) :
    liftRel I (probeUnionFamily Qs) φ = joinRel (fun i => liftRel I (Qs i) φ) := by
  apply eq_of_same_upper_bounds
    (liftRel_equivalence I _ φ) (joinRel_equivalence _)
  intro ρ hρ
  rw [joinRel_finer_iff hρ, adjunction I _ hρ]
  constructor
  · intro h i
    rw [adjunction I (Qs i) hρ]
    exact fun e e' hφ p hp => h e e' hφ p ⟨i, hp⟩
  · intro h e e' hφ p ⟨i, hp⟩
    exact ((adjunction I (Qs i) hρ).1 (h i)) e e' hφ p hp

/-- Empty probe family: `K_∅(ρ) = ⊤`. -/
theorem kernelRel_noProbes (I : P → E → A) {Q : P → Prop}
    (hQ : ∀ p, ¬ Q p) (ρ : A → A → Prop) :
    kernelRel I Q ρ = totalRel E := by
  funext e e'
  exact propext ⟨fun _ => True.intro, fun _ p hp => absurd hp (hQ p)⟩

/-- Empty probe family: `L_∅(φ) = ⊥`. -/
theorem liftRel_noProbes (I : P → E → A) {Q : P → Prop}
    (hQ : ∀ p, ¬ Q p) (φ : E → E → Prop) :
    liftRel I Q φ = diagonalRel A := by
  apply Finer.antisymm
  · apply liftRel_le_of_generators I Q (diagonalRel_equivalence A)
    intro p _ _ hp _
    exact absurd hp (hQ p)
  · exact finer_diagonalRel (liftRel_equivalence I Q φ).refl

/-- A kernel is the meet of single-probe kernels. -/
theorem kernelRel_singletons_iff (I : P → E → A) (Q : P → Prop)
    (ρ : A → A → Prop) (e e' : E) :
    kernelRel I Q ρ e e' ↔
      ∀ p : P, Q p → kernelRel I (fun q => q = p) ρ e e' :=
  ⟨fun h p hp q hq => by subst hq; exact h q hp,
   fun h p hp => h p hp p rfl⟩

end SE.InterpretiveKernel
