/-
Copyright (c) 2026 Denise M. Case. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denise M. Case
-/
module

public import SE.InterpretiveKernel.Core

/-!
# SE.InterpretiveKernel.Lattice

Lattice operations on relations, stated for relations (no bundling).

Conventions (as in Core): `Finer R S` is `R ⊆ S`, finer is lower.

* `totalRel α`    is the top element (the paper's `⊤`).
* `diagonalRel α` is the bottom element (the paper's `⊥`), i.e. equality.
* `meetRel`  of a family is intersection.
* `joinRel`  of a family is the equivalence closure of the union.

Meet and join of equivalence relations are equivalence relations; the
universal properties below are stated with explicit `Equivalence` hypotheses
where they are needed.
-/

@[expose] public section

namespace SE.InterpretiveKernel

universe u v w

/-- Top: the total relation. -/
def totalRel (α : Type u) : α → α → Prop :=
  fun _ _ => True

/-- Bottom: the diagonal, i.e. equality. -/
def diagonalRel (α : Type u) : α → α → Prop :=
  fun a b => a = b

/-- Meet of an indexed family: intersection. The empty family gives `totalRel`. -/
def meetRel {α : Type u} {ι : Sort v} (R : ι → α → α → Prop) : α → α → Prop :=
  fun a b => ∀ i, R i a b

/-- Binary meet: intersection. -/
def meetRel2 {α : Type u} (R S : α → α → Prop) : α → α → Prop :=
  fun a b => R a b ∧ S a b

/-- Join of an indexed family: equivalence closure of the union.
The empty family gives the equivalence closure of the empty relation,
which is equality. -/
def joinRel {α : Type u} {ι : Sort v} (R : ι → α → α → Prop) : α → α → Prop :=
  EqvClosure (fun a b => ∃ i, R i a b)

/-- Binary join: equivalence closure of the union. -/
def joinRel2 {α : Type u} (R S : α → α → Prop) : α → α → Prop :=
  EqvClosure (fun a b => R a b ∨ S a b)

/-- Equivalence of the total relation. -/
theorem totalRel_equivalence (α : Type u) : Equivalence (totalRel α) where
  refl  := fun _ => True.intro
  symm  := fun _ => True.intro
  trans := fun _ _ => True.intro

/-- Equivalence of the diagonal relation (equality). -/
theorem diagonalRel_equivalence (α : Type u) : Equivalence (diagonalRel α) where
  refl  := fun _ => rfl
  symm  := fun h => h.symm
  trans := fun h1 h2 => h1.trans h2

/-- The diagonal is finer than every reflexive relation. -/
theorem finer_diagonalRel {α : Type u} {R : α → α → Prop}
    (hR : ∀ x, R x x) : Finer (diagonalRel α) R :=
  finer_eq_of_refl hR

/-- Every relation is finer than the total relation. -/
theorem finer_totalRel {α : Type u} (R : α → α → Prop) : Finer R (totalRel α) :=
  finer_total R

/-! ### Meets -/

/-- Equivalence of the meet of an indexed family of equivalence relations. -/
theorem meetRel_equivalence {α : Type u} {ι : Sort v} {R : ι → α → α → Prop}
    (h : ∀ i, Equivalence (R i)) : Equivalence (meetRel R) where
  refl  := fun a i => (h i).refl a
  symm  := fun hab i => (h i).symm (hab i)
  trans := fun hab hbc i => (h i).trans (hab i) (hbc i)

/-- Equivalence of the meet of two equivalence relations. -/
theorem meetRel2_equivalence {α : Type u} {R S : α → α → Prop}
    (hR : Equivalence R) (hS : Equivalence S) : Equivalence (meetRel2 R S) where
  refl  := fun a => ⟨hR.refl a, hS.refl a⟩
  symm  := fun h => ⟨hR.symm h.1, hS.symm h.2⟩
  trans := fun h1 h2 => ⟨hR.trans h1.1 h2.1, hS.trans h1.2 h2.2⟩

/-- The meet is below each member (indexed family). -/
theorem meetRel_finer {α : Type u} {ι : Sort v} (R : ι → α → α → Prop) (i : ι) :
    Finer (meetRel R) (R i) :=
  fun _ _ h => h i

/-- Universal property of the meet (greatest lower bound). -/
theorem finer_meetRel_iff {α : Type u} {ι : Sort v} {S : α → α → Prop}
    {R : ι → α → α → Prop} :
    Finer S (meetRel R) ↔ ∀ i, Finer S (R i) :=
  ⟨fun h i x y hxy => h x y hxy i, fun h x y hxy i => h i x y hxy⟩

/-! ### Joins -/

/-- Equivalence of the join of an indexed family of equivalence relations. -/
theorem joinRel_equivalence {α : Type u} {ι : Sort v} (R : ι → α → α → Prop) :
    Equivalence (joinRel R) :=
  EqvClosure.equivalence _

/-- Equivalence of the join of two equivalence relations. -/
theorem joinRel2_equivalence {α : Type u} (R S : α → α → Prop) :
    Equivalence (joinRel2 R S) :=
  EqvClosure.equivalence _

/-- Each member is below the join (indexed family). -/
theorem finer_joinRel {α : Type u} {ι : Sort v} (R : ι → α → α → Prop) (i : ι) :
    Finer (R i) (joinRel R) :=
  fun _ _ h => EqvClosure.of ⟨i, h⟩

/-- The left member is below the join of two equivalence relations. -/
theorem finer_joinRel2_left {α : Type u} (R S : α → α → Prop) :
    Finer R (joinRel2 R S) :=
  fun _ _ h => EqvClosure.of (Or.inl h)

/-- The right member is below the join of two equivalence relations. -/
theorem finer_joinRel2_right {α : Type u} (R S : α → α → Prop) :
    Finer S (joinRel2 R S) :=
  fun _ _ h => EqvClosure.of (Or.inr h)

/-- Universal property of the join (least upper bound among equivalences, indexed family). -/
theorem joinRel_finer_iff {α : Type u} {ι : Sort v} {T : α → α → Prop}
    {R : ι → α → α → Prop} (hT : Equivalence T) :
    Finer (joinRel R) T ↔ ∀ i, Finer (R i) T := by
  constructor
  · intro h i
    exact Finer.trans (finer_joinRel R i) h
  · intro h
    apply EqvClosure.le_of_equivalence hT
    intro x y ⟨i, hi⟩
    exact h i x y hi

/-- Universal property of the join (least upper bound among equivalences, two members). -/
theorem joinRel2_finer_iff {α : Type u} {R S T : α → α → Prop}
    (hT : Equivalence T) :
    Finer (joinRel2 R S) T ↔ Finer R T ∧ Finer S T := by
  constructor
  · intro h
    exact ⟨Finer.trans (finer_joinRel2_left R S) h,
           Finer.trans (finer_joinRel2_right R S) h⟩
  · intro ⟨hR, hS⟩
    apply EqvClosure.le_of_equivalence hT
    intro x y hxy
    cases hxy with
    | inl h => exact hR x y h
    | inr h => exact hS x y h

/-- Two equivalence relations with the same equivalence upper bounds are equal. -/
theorem eq_of_same_upper_bounds {α : Type u} {R S : α → α → Prop}
    (hR : Equivalence R) (hS : Equivalence S)
    (h : ∀ T, Equivalence T → (Finer R T ↔ Finer S T)) : R = S :=
  Finer.antisymm
    ((h S hS).2 (Finer.refl S))
    ((h R hR).1 (Finer.refl R))

end SE.InterpretiveKernel
