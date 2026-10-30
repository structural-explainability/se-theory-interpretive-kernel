/-
Copyright (c) 2026 Denise M. Case. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denise M. Case
-/
module

public import SE.InterpretiveKernel.Generating

/-!
# SE.InterpretiveKernel.Threshold

Admissible occurrence regimes and the interpretive threshold.

`Admissible` is `Compatible` under the paper's name: an occurrence regime
`ρ` is admissible for a frame regime `φ` under the selected probes when
`ρ` is an equivalence relation and `φ ≤ K_Q(ρ)`.  The threshold `Θ_Q(φ)` is
`L_Q(φ)`.  Everything here is a restatement or direct consequence of the
adjunction; nothing new is assumed.

Scope: admissibility is mathematical compatibility with a declaration. It is
not correctness of the declaration.
-/

@[expose] public section

namespace SE.InterpretiveKernel

universe u v w x

variable {E : Type u} {A : Type v} {P : Type w}

/-- `ρ ∈ Adm_Q(φ)`: `ρ` is an equivalence relation and `φ ≤ K_Q(ρ)`. -/
def Admissible (I : P → E → A) (Q : P → Prop)
    (φ : E → E → Prop) (ρ : A → A → Prop) : Prop :=
  Equivalence ρ ∧ Finer φ (kernelRel I Q ρ)

/-- The interpretive threshold `Θ_Q(φ) = L_Q(φ)`. -/
def threshold (I : P → E → A) (Q : P → Prop) (φ : E → E → Prop) : A → A → Prop :=
  liftRel I Q φ

/-- Admissibility is exactly `Compatible`. -/
theorem admissible_iff_compatible (I : P → E → A) (Q : P → Prop)
    (φ : E → E → Prop) (ρ : A → A → Prop) :
    Admissible I Q φ ρ ↔ Compatible I Q φ ρ :=
  Iff.rfl

/-- Exact threshold characterization: `ρ` is admissible iff `Θ ≤ ρ`
(for `ρ` an equivalence relation). -/
theorem admissible_iff_threshold_finer (I : P → E → A) (Q : P → Prop)
    {φ : E → E → Prop} {ρ : A → A → Prop} (hρ : Equivalence ρ) :
    Admissible I Q φ ρ ↔ Finer (threshold I Q φ) ρ :=
  ⟨fun h => (adjunction I Q hρ).2 h.2,
   fun h => ⟨hρ, (adjunction I Q hρ).1 h⟩⟩

/-- The threshold is admissible. -/
theorem threshold_admissible (I : P → E → A) (Q : P → Prop) (φ : E → E → Prop) :
    Admissible I Q φ (threshold I Q φ) :=
  liftRel_compatible I Q φ

/-- The threshold is the finest admissible regime. -/
theorem threshold_finest (I : P → E → A) (Q : P → Prop) {φ : E → E → Prop}
    {ρ : A → A → Prop} (h : Admissible I Q φ ρ) :
    Finer (threshold I Q φ) ρ :=
  liftRel_le_of_compatible I Q h

/-- Upward closure: coarsening an admissible regime keeps it admissible. -/
theorem admissible_upward (I : P → E → A) (Q : P → Prop) {φ : E → E → Prop}
    {ρ σ : A → A → Prop} (h : Admissible I Q φ ρ)
    (hσ : Equivalence σ) (hρσ : Finer ρ σ) : Admissible I Q φ σ :=
  ⟨hσ, coherent_of_coarser_occurrences I Q hρσ h.2⟩

/-- Thresholds are monotone in the frame regime. -/
theorem threshold_monotone (I : P → E → A) (Q : P → Prop) {φ ψ : E → E → Prop}
    (h : Finer φ ψ) : Finer (threshold I Q φ) (threshold I Q ψ) :=
  liftRel_monotone I Q h

/-- Probe extension raises the threshold. -/
theorem threshold_probes (I : P → E → A) {Q Q' : P → Prop}
    (hQ : ∀ p, Q p → Q' p) (φ : E → E → Prop) :
    Finer (threshold I Q φ) (threshold I Q' φ) :=
  liftRel_monotone_probes I hQ φ

/-- The threshold of a join of frame regimes is the join of the thresholds. -/
theorem threshold_joinRel (I : P → E → A) (Q : P → Prop)
    {ι : Sort x} (φs : ι → E → E → Prop) :
    threshold I Q (joinRel φs) = joinRel (fun i => threshold I Q (φs i)) :=
  liftRel_joinRel I Q φs

/-- Simultaneous admissibility: `ρ` is admissible for every `φᵢ` iff it lies
above the join of the thresholds. -/
theorem simultaneous_admissible (I : P → E → A) (Q : P → Prop)
    {ι : Sort x} (φs : ι → E → E → Prop) {ρ : A → A → Prop} (hρ : Equivalence ρ) :
    (∀ i, Admissible I Q (φs i) ρ) ↔
      Finer (joinRel (fun i => threshold I Q (φs i))) ρ := by
  rw [joinRel_finer_iff hρ]
  constructor
  · intro h i
    exact (admissible_iff_threshold_finer I Q hρ).1 (h i)
  · intro h i
    exact (admissible_iff_threshold_finer I Q hρ).2 (h i)

/-- The total relation is admissible for every frame regime. -/
theorem total_admissible (I : P → E → A) (Q : P → Prop) (φ : E → E → Prop) :
    Admissible I Q φ (totalRel A) :=
  ⟨totalRel_equivalence A, coherent_total_occurrence I Q φ⟩

/-- Extremal admissible regimes: the threshold is least, the total relation
is greatest. -/
theorem admissible_extremal (I : P → E → A) (Q : P → Prop) (φ : E → E → Prop) :
    (Admissible I Q φ (threshold I Q φ) ∧
      ∀ ρ, Admissible I Q φ ρ → Finer (threshold I Q φ) ρ) ∧
    (Admissible I Q φ (totalRel A) ∧
      ∀ ρ, Admissible I Q φ ρ → Finer ρ (totalRel A)) :=
  ⟨⟨threshold_admissible I Q φ, fun _ h => threshold_finest I Q h⟩,
   ⟨total_admissible I Q φ, fun ρ _ => finer_totalRel ρ⟩⟩

/-- Meet closure of admissibility, for any family (including the empty one). -/
theorem admissible_meetRel (I : P → E → A) (Q : P → Prop) {φ : E → E → Prop}
    {ι : Sort x} {ρs : ι → A → A → Prop} (h : ∀ i, Admissible I Q φ (ρs i)) :
    Admissible I Q φ (meetRel ρs) := by
  refine ⟨meetRel_equivalence (fun i => (h i).1), ?_⟩
  intro e e' hφ p hp i
  exact (h i).2 e e' hφ p hp

/-- The threshold is the meet of all admissible regimes, pointwise form. -/
theorem threshold_iff_forall_admissible (I : P → E → A) (Q : P → Prop)
    (φ : E → E → Prop) (a a' : A) :
    threshold I Q φ a a' ↔ ∀ ρ, Admissible I Q φ ρ → ρ a a' :=
  ⟨fun h _ hρ => threshold_finest I Q hρ a a' h,
   fun h => h _ (threshold_admissible I Q φ)⟩

/-- The threshold is the meet of all admissible regimes. -/
theorem threshold_eq_meet_admissible (I : P → E → A) (Q : P → Prop)
    (φ : E → E → Prop) :
    threshold I Q φ =
      meetRel (fun r : {ρ : A → A → Prop // Admissible I Q φ ρ} => r.val) := by
  funext a a'
  apply propext
  rw [threshold_iff_forall_admissible]
  exact ⟨fun h r => h r.val r.property, fun h ρ hρ => h ⟨ρ, hρ⟩⟩

end SE.InterpretiveKernel
