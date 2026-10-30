/-
Copyright (c) 2026 Denise M. Case. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denise M. Case
-/
module

import SE.InterpretiveKernel

/-!
# SETest.InterpretiveKernel.ExamplesPaper

Finite counterexamples that delimit the preservation and threshold results.
All carriers are `Unit`, `Bool`, `Fin n`.  Each statement is a mathematical fact
about the definitions only.

* `ExampleF`: the counit inequality can be strict.
* `ExampleG`: `K` need not preserve joins.
* `ExampleH`: `L` need not preserve meets.
* `ExampleI`: thresholds of two frame regimes can be incomparable.
* `ExampleJ`: the adjunction fails if `ρ` is not an equivalence relation.
-/

open SE.InterpretiveKernel

/-- Merge only `0` and `1` on `Fin 3`. -/
abbrev mergeZeroOne : Fin 3 → Fin 3 → Prop :=
  fun a b => a = b ∨ (a.val ≤ 1 ∧ b.val ≤ 1)

/-- Merge only `1` and `2` on `Fin 3`. -/
abbrev mergeOneTwo : Fin 3 → Fin 3 → Prop :=
  fun a b => a = b ∨ (a.val ≥ 1 ∧ b.val ≥ 1)

theorem mergeZeroOne_equivalence : Equivalence mergeZeroOne where
  refl  := by decide
  symm  := by
    intro x y
    revert x y
    decide
  trans := by
    intro x y z
    revert x y z
    decide

theorem mergeOneTwo_equivalence : Equivalence mergeOneTwo where
  refl  := by decide
  symm  := by
    intro x y
    revert x y
    decide
  trans := by
    intro x y z
    revert x y z
    decide

/-! ## Example F: the counit can be strict

One frame, outputs `Bool`, the interpretation always outputs `false`.
`ρ` is total, but `L(K(ρ))` is equality: it is strictly finer than `ρ`. -/

namespace ExampleF

abbrev I : Unit → Unit → Bool := fun _ _ => false
abbrev Q : Unit → Prop := fun _ => True

theorem counit_strict :
    ¬ Finer (totalRel Bool) (liftRel I Q (kernelRel I Q (totalRel Bool))) := by
  intro h
  have hdiag : Finer (liftRel I Q (kernelRel I Q (totalRel Bool))) (diagonalRel Bool) := by
    apply liftRel_le_of_generators I Q (diagonalRel_equivalence Bool)
    intro p e e' _ _
    exact rfl
  have htf : diagonalRel Bool true false := hdiag true false (h true false True.intro)
  exact Bool.noConfusion htf

end ExampleF

/-! ## Example G: `K` need not preserve joins

Two frames `0, 1` interpreted to outputs `0, 2` of `Fin 3`.  The regimes
`mergeZeroOne` and `mergeOneTwo` are equivalences whose join identifies `0`
and `2`, so `K(ρ ∨ σ)` identifies the two frames; each of `K(ρ)`, `K(σ)` is
equality, and so is their join. -/

namespace ExampleG

abbrev I : Unit → Fin 2 → Fin 3 := fun _ e => if e.val = 0 then 0 else 2
abbrev Q : Unit → Prop := fun _ => True

theorem kernel_zeroOne_diag :
    Finer (kernelRel I Q mergeZeroOne) (diagonalRel (Fin 2)) := by
  intro x y h
  have h' : mergeZeroOne (I () x) (I () y) := h () True.intro
  clear h
  show x = y
  revert x y
  decide

theorem kernel_oneTwo_diag :
    Finer (kernelRel I Q mergeOneTwo) (diagonalRel (Fin 2)) := by
  intro x y h
  have h' : mergeOneTwo (I () x) (I () y) := h () True.intro
  clear h
  show x = y
  revert x y
  decide

/-- `ρ ∨ σ` relates `0` and `2`. -/
theorem join_relates : joinRel2 mergeZeroOne mergeOneTwo 0 2 :=
  EqvClosure.trans (b := 1)
    (EqvClosure.of (Or.inl (show mergeZeroOne 0 1 by decide)))
    (EqvClosure.of (Or.inr (show mergeOneTwo 1 2 by decide)))

/-- `K(ρ ∨ σ)` relates the two distinct frames. -/
theorem kernel_join_relates :
    kernelRel I Q (joinRel2 mergeZeroOne mergeOneTwo) 0 1 := by
  intro p _
  exact join_relates

/-- `K(ρ) ∨ K(σ)` does not. -/
theorem join_of_kernels_separates :
    ¬ joinRel2 (kernelRel I Q mergeZeroOne) (kernelRel I Q mergeOneTwo) 0 1 := by
  intro h
  have hle : Finer (joinRel2 (kernelRel I Q mergeZeroOne) (kernelRel I Q mergeOneTwo))
      (diagonalRel (Fin 2)) :=
    (joinRel2_finer_iff (diagonalRel_equivalence (Fin 2))).2
      ⟨kernel_zeroOne_diag, kernel_oneTwo_diag⟩
  have h01 : (0 : Fin 2) = 1 := hle 0 1 h
  exact absurd h01 (by decide)

/-- `K` does not preserve joins of equivalence relations. -/
theorem kernel_not_join_preserving :
    ¬ Finer (kernelRel I Q (joinRel2 mergeZeroOne mergeOneTwo))
            (joinRel2 (kernelRel I Q mergeZeroOne) (kernelRel I Q mergeOneTwo)) :=
  fun h => join_of_kernels_separates (h 0 1 kernel_join_relates)

end ExampleG

/-! ## Example H: `L` need not preserve meets

Three frames, outputs `Bool`, `0 ↦ false`, `1, 2 ↦ true`.  The frame regimes
merging `{0,1}` and `{0,2}` have equality as their meet, so `L` of the meet is
equality, but each of the two generated regimes identifies `false` and `true`. -/

namespace ExampleH

abbrev I : Unit → Fin 3 → Bool := fun _ e => decide (e.val ≠ 0)
abbrev Q : Unit → Prop := fun _ => True

abbrev mergeZeroTwo : Fin 3 → Fin 3 → Prop :=
  fun a b => a = b ∨ (a.val ≠ 1 ∧ b.val ≠ 1)

theorem meet_is_diagonal :
    Finer (meetRel2 mergeZeroOne mergeZeroTwo) (diagonalRel (Fin 3)) := by
  unfold meetRel2 Finer diagonalRel
  decide

theorem lift_meet_diagonal :
    Finer (liftRel I Q (meetRel2 mergeZeroOne mergeZeroTwo)) (diagonalRel Bool) := by
  have h := liftRel_monotone I Q meet_is_diagonal
  rw [liftRel_diagonal I Q] at h
  exact h

theorem meet_of_lifts_relates :
    meetRel2 (liftRel I Q mergeZeroOne) (liftRel I Q mergeZeroTwo) false true :=
  ⟨liftRel_of_pair I Q (p := ()) (e := 0) (e' := 1) True.intro (by decide),
   liftRel_of_pair I Q (p := ()) (e := 0) (e' := 2) True.intro (by decide)⟩

/-- `L` does not preserve meets of equivalence relations. -/
theorem lift_not_meet_preserving :
    ¬ Finer (meetRel2 (liftRel I Q mergeZeroOne) (liftRel I Q mergeZeroTwo))
            (liftRel I Q (meetRel2 mergeZeroOne mergeZeroTwo)) := by
  intro h
  have htf : diagonalRel Bool false true :=
    lift_meet_diagonal false true (h false true meet_of_lifts_relates)
  exact Bool.noConfusion htf

end ExampleH

/-! ## Example I: incomparable thresholds

Frames and outputs `Fin 3`, one probe, identity interpretation.  The thresholds
of `mergeZeroOne` and `mergeOneTwo` are incomparable under `Finer`. -/

namespace ExampleI

abbrev I : Unit → Fin 3 → Fin 3 := fun _ e => e
abbrev Q : Unit → Prop := fun _ => True

theorem threshold_zeroOne_le : Finer (threshold I Q mergeZeroOne) mergeZeroOne := by
  exact threshold_finest I Q ⟨mergeZeroOne_equivalence, fun _ _ h _ _ => h⟩

theorem threshold_oneTwo_le : Finer (threshold I Q mergeOneTwo) mergeOneTwo := by
  exact threshold_finest I Q ⟨mergeOneTwo_equivalence, fun _ _ h _ _ => h⟩

theorem threshold_zeroOne_relates : threshold I Q mergeZeroOne 0 1 :=
  liftRel_of_pair I Q (p := ()) (e := 0) (e' := 1) True.intro (by decide)

theorem threshold_oneTwo_relates : threshold I Q mergeOneTwo 1 2 :=
  liftRel_of_pair I Q (p := ()) (e := 1) (e' := 2) True.intro (by decide)

theorem not_finer_one :
    ¬ Finer (threshold I Q mergeZeroOne) (threshold I Q mergeOneTwo) := by
  intro h
  have h01 : mergeOneTwo 0 1 := threshold_oneTwo_le 0 1 (h 0 1 threshold_zeroOne_relates)
  revert h01
  decide

theorem not_finer_two :
    ¬ Finer (threshold I Q mergeOneTwo) (threshold I Q mergeZeroOne) := by
  intro h
  have h12 : mergeZeroOne 1 2 := threshold_zeroOne_le 1 2 (h 1 2 threshold_oneTwo_relates)
  revert h12
  decide

/-- The thresholds are incomparable. -/
theorem thresholds_incomparable :
    ¬ Finer (threshold I Q mergeZeroOne) (threshold I Q mergeOneTwo) ∧
    ¬ Finer (threshold I Q mergeOneTwo) (threshold I Q mergeZeroOne) :=
  ⟨not_finer_one, not_finer_two⟩

end ExampleI

/-! ## Example J: the adjunction needs `Equivalence ρ`

One frame, one output, no selected probes, and `ρ` the empty (non-reflexive)
relation.  `φ ≤ K(ρ)` holds, but `L(φ) ≤ ρ` fails, since `L(φ)` is reflexive.
So the `←` direction of the adjunction is false without the hypothesis. -/

namespace ExampleJ

abbrev I : Unit → Unit → Unit := fun _ _ => ()
abbrev Q : Unit → Prop := fun _ => False
abbrev ρ : Unit → Unit → Prop := fun _ _ => False

theorem coherent_without_equivalence :
    Finer (diagonalRel Unit) (kernelRel I Q ρ) :=
  fun _ _ _ _ hp => hp.elim

theorem lift_not_finer_without_equivalence :
    ¬ Finer (liftRel I Q (diagonalRel Unit)) ρ :=
  fun h => h () () ((liftRel_equivalence I Q (diagonalRel Unit)).refl ())

theorem rho_not_equivalence : ¬ Equivalence ρ :=
  fun h => h.refl ()

end ExampleJ
