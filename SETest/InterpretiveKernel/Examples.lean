/-
Copyright (c) 2026 Denise M. Case. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denise M. Case
-/
module

import SE.InterpretiveKernel

/-!
# SETest.InterpretiveKernel.Examples

Finite, machine-checked examples and counterexamples for SE.InterpretiveKernel.
Carriers are `Bool`, `Fin n`, `Unit`.

Each example states a mathematical fact about the definitions only. None of
them says anything about whether a particular interpretation is scientifically
correct.
-/

open SE.InterpretiveKernel

/-- Equality on a type is an equivalence relation (local helper). -/
theorem eq_equivalence (α : Type) : Equivalence (fun a b : α => a = b) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-! ## Example 0: direction of `Finer` (guards against accidental reversal) -/

namespace Example0

/-- Equality is finer than the total relation on `Bool`. -/
theorem eq_finer_total :
    Finer (fun a b : Bool => a = b) (fun _ _ => True) :=
  finer_total _

/-- The total relation is NOT finer than equality on `Bool`. -/
theorem total_not_finer_eq :
    ¬ Finer (fun _ _ : Bool => True) (fun a b : Bool => a = b) := by
  intro h
  have := h false true True.intro
  exact Bool.noConfusion this

end Example0

/-! ## Example A: coherent interpretation

Frames `Fin 4`, frame relation "same parity", outputs `Bool`, probes `Bool`,
all probes selected, occurrence relation equality. The interpretation is
neither injective nor surjective on frames. -/

namespace ExampleA

abbrev φ : Fin 4 → Fin 4 → Prop := fun e e' => e.val % 2 = e'.val % 2
abbrev I : Bool → Fin 4 → Bool := fun p e => xor p (decide (e.val % 2 = 1))
abbrev ρ : Bool → Bool → Prop := fun a b => a = b
abbrev Q : Bool → Prop := fun _ => True

theorem φ_equivalence : Equivalence φ :=
  ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- `φ ≤ K_Q(ρ)`. -/
theorem coherent : Coherent I Q φ ρ := by
  unfold Coherent Finer kernelRel
  decide

/-- Consequence via the adjunction: `L_Q(φ) ≤ ρ`. -/
theorem lift_finer : Finer (liftRel I Q φ) ρ :=
  (adjunction I Q (eq_equivalence Bool)).2 coherent

/-- Second proof through the bounded decision procedure: no witness exists. -/
theorem coherent_by_search : Coherent I Q φ ρ := by
  have hes : ∀ e : Fin 4, e ∈ [0, 1, 2, 3] := by decide
  have hps : ∀ p : Bool, Q p → p ∈ [true, false] := by decide
  have hno : ¬ WitnessOn I Q φ ρ [0, 1, 2, 3] [true, false] := by
    unfold WitnessOn
    decide
  exact Classical.byContradiction fun hn =>
    hno ((not_coherent_iff_witnessOn I Q φ ρ [0, 1, 2, 3] [true, false] hes hps).1 hn)

end ExampleA

/-! ## Example B: incompatible interpretation (finite witness)

Frames and outputs `Bool`, one probe, identity interpretation. `φ` is total,
so `false` and `true` are `φ`-equivalent, but `ρ = Eq` separates their outputs. -/

namespace ExampleB

abbrev φ : Bool → Bool → Prop := fun _ _ => True
abbrev I : Unit → Bool → Bool := fun _ e => e
abbrev ρ : Bool → Bool → Prop := fun a b => a = b
abbrev Q : Unit → Prop := fun _ => True

/-- The explicit witness: frames `false`, `true`, probe `()`. -/
def witness : IncompatibilityWitness I Q φ ρ where
  frame₁    := false
  frame₂    := true
  probe     := ()
  selected  := True.intro
  related   := True.intro
  separated := by decide

theorem not_coherent : ¬ Coherent I Q φ ρ :=
  witness.not_coherent

/-- By the adjunction the least compatible relation is not below `ρ`. -/
theorem not_lift_finer : ¬ Finer (liftRel I Q φ) ρ :=
  witness.not_lift_finer (eq_equivalence Bool)

/-- `L_Q(φ)` relates `false` and `true`, so it is not discrete. -/
theorem lift_relates : liftRel I Q φ false true :=
  liftRel_of_pair I Q (p := ()) (e := false) (e' := true) True.intro True.intro

/-- The bounded search finds the witness. -/
theorem search_finds :
    WitnessOn I Q φ ρ [false, true] [()] := by
  unfold WitnessOn
  decide

end ExampleB

/-! ## Example C: interpretation collapses distinctions

Frames `Fin 3`; the interpretation ignores the probe and only records whether
the frame is `0`. Frames `1` and `2` are distinct but indistinguishable. -/

namespace ExampleC

abbrev I : Bool → Fin 3 → Bool := fun _ e => decide (e.val = 0)
abbrev ρ : Bool → Bool → Prop := fun a b => a = b
abbrev Q : Bool → Prop := fun _ => True

theorem distinct : (1 : Fin 3) ≠ 2 := by decide

/-- `1` and `2` are related by `K_Q(Eq)`. -/
theorem kernel_relates : kernelRel I Q ρ 1 2 := by
  unfold kernelRel
  decide

/-- `0` and `1` are not related by `K_Q(Eq)`. -/
theorem kernel_separates : ¬ kernelRel I Q ρ 0 1 := by
  unfold kernelRel
  decide

/-- Hence `K_Q(Eq)` is strictly coarser than identity of frames. -/
theorem kernel_not_finer_than_identity :
    ¬ Finer (kernelRel I Q ρ) (fun a b : Fin 3 => a = b) := by
  intro h
  exact distinct (h 1 2 kernel_relates)

/-- The unit inequality `φ ≤ K_Q(L_Q(φ))` can be strict: with `φ` equality of
frames, `K_Q(L_Q(φ))` still relates the distinct frames `1` and `2`. -/
theorem unit_strict :
    ¬ Finer (kernelRel I Q (liftRel I Q (fun a b : Fin 3 => a = b)))
            (fun a b : Fin 3 => a = b) := by
  intro h
  -- `L_Q(Eq)` is reflexive, hence `Eq ≤ L_Q(Eq)`, hence `K_Q(Eq) ≤ K_Q(L_Q(Eq))`
  have hrefl : Finer (fun a b : Bool => a = b) (liftRel I Q (fun a b : Fin 3 => a = b)) :=
    finer_eq_of_refl (liftRel_equivalence I Q _).refl
  have h12 : kernelRel I Q (liftRel I Q (fun a b : Fin 3 => a = b)) 1 2 :=
    kernelRel_monotone I Q hrefl 1 2 kernel_relates
  exact distinct (h 1 2 h12)

end ExampleC

/-! ## Example D: probe selection matters

Frames, probes and outputs `Bool`; `I p e = p && e`. The probe `false` erases
the frame; the probe `true` reads it. `Q₀ = {false} ⊆ Q₁ = all probes`. -/

namespace ExampleD

abbrev I : Bool → Bool → Bool := fun p e => p && e
abbrev ρ : Bool → Bool → Prop := fun a b => a = b
abbrev Q₀ : Bool → Prop := fun p => p = false
abbrev Q₁ : Bool → Prop := fun _ => True
abbrev φ : Bool → Bool → Prop := fun _ _ => True

theorem Q₀_subset_Q₁ : ∀ p, Q₀ p → Q₁ p := fun _ _ => True.intro

/-- Under `Q₀` the frames `false` and `true` are not distinguished. -/
theorem kernel_Q₀_relates : kernelRel I Q₀ ρ false true := by
  unfold kernelRel
  decide

/-- Under `Q₁` they are distinguished. -/
theorem kernel_Q₁_separates : ¬ kernelRel I Q₁ ρ false true := by
  unfold kernelRel
  decide

/-- More probes refine the kernel (general theorem, instance). -/
theorem kernel_refines : Finer (kernelRel I Q₁ ρ) (kernelRel I Q₀ ρ) :=
  kernelRel_antitone_probes I Q₀_subset_Q₁ ρ

/-- The refinement is strict: the reverse inclusion fails. -/
theorem kernel_strict : ¬ Finer (kernelRel I Q₀ ρ) (kernelRel I Q₁ ρ) :=
  fun h => kernel_Q₁_separates (h false true kernel_Q₀_relates)

/-- `φ` is coherent with `ρ` at `Q₀`... -/
theorem coherent_Q₀ : Coherent I Q₀ φ ρ := by
  unfold Coherent Finer kernelRel
  decide

/-- ...but not at `Q₁`; the witness uses the probe `true`. -/
def witness_Q₁ : IncompatibilityWitness I Q₁ φ ρ where
  frame₁    := false
  frame₂    := true
  probe     := true
  selected  := True.intro
  related   := True.intro
  separated := by decide

/-- More probes enlarge the required occurrence relation (general theorem). -/
theorem lift_grows : Finer (liftRel I Q₀ φ) (liftRel I Q₁ φ) :=
  liftRel_monotone_probes I Q₀_subset_Q₁ φ

/-- `L_{Q₀}(φ)` stays below equality. -/
theorem lift_Q₀_finer_eq : Finer (liftRel I Q₀ φ) ρ :=
  (adjunction I Q₀ (eq_equivalence Bool)).2 coherent_Q₀

/-- The growth is strict: `L_{Q₁}(φ)` relates `false` and `true`, `L_{Q₀}(φ)` does not. -/
theorem lift_strict : ¬ Finer (liftRel I Q₁ φ) (liftRel I Q₀ φ) := by
  intro h
  have h1 : liftRel I Q₁ φ (I true false) (I true true) :=
    liftRel_of_pair I Q₁ (p := true) (e := false) (e' := true) True.intro True.intro
  have h2 := lift_Q₀_finer_eq _ _ (h _ _ h1)
  exact Bool.noConfusion h2

end ExampleD

/-! ## Example E: the equivalence closure in `L` is necessary

Two probes, outputs `Fin 3`. Probe `false` sends frames to `{0, 1}`; probe
`true` sends frames to `{1, 2}`. The generating pairs relate `0 ~ 1` and
`1 ~ 2` but never `0 ~ 2`, yet every compatible equivalence `ρ` must relate
`0` and `2`. So the generating relation alone is not transitive and `L`
must take the closure across probes. -/

namespace ExampleE

abbrev φ : Bool → Bool → Prop := fun _ _ => True
abbrev I : Bool → Bool → Fin 3 :=
  fun p e => if p then (if e then 2 else 1) else (if e then 1 else 0)
abbrev Q : Bool → Prop := fun _ => True

/-- The generating pairs do not relate `0` and `2` directly. -/
theorem generators_not_transitive : ¬ generators I Q φ 0 2 := by
  unfold generators
  decide

/-- `0 ~ 1` is generated (probe `false`). -/
theorem generators_zero_one : generators I Q φ 0 1 :=
  ⟨false, false, true, True.intro, True.intro, rfl, rfl⟩

/-- `1 ~ 2` is generated (probe `true`). -/
theorem generators_one_two : generators I Q φ 1 2 :=
  ⟨true, false, true, True.intro, True.intro, rfl, rfl⟩

/-- The closure relates `0` and `2`. -/
theorem lift_zero_two : liftRel I Q φ 0 2 :=
  EqvClosure.trans (EqvClosure.of generators_zero_one) (EqvClosure.of generators_one_two)

/-- Every compatible occurrence relation relates `0` and `2` (minimality, instance). -/
theorem compatible_relates_zero_two {ρ : Fin 3 → Fin 3 → Prop}
    (h : Compatible I Q φ ρ) : ρ 0 2 :=
  liftRel_le_of_compatible I Q h 0 2 lift_zero_two

end ExampleE
