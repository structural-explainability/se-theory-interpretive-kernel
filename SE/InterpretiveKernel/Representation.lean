/-
Copyright (c) 2026 Denise M. Case. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denise M. Case
-/
module

public import SE.InterpretiveKernel.Threshold

/-!
# SE.InterpretiveKernel.Representation

Pairwise interpretive demand and the generalized-ultrametric representation.

## Contents

1. Pairwise demand `δ(x,y) = L_Q(γ_{x,y})`, with `γ_{x,y}` the principal pair
   regime, its explicit form, and the threshold characterization
   `K_Q(ρ) x y ↔ δ(x,y) ≤ ρ`.
2. `GeneralizedUltrametric`: a family of equivalence relations on `A` indexed by
   pairs of `X`, with zero on the diagonal, symmetry, and the strong triangle
   inequality `δ(x,z) ≤ δ(x,y) ∨ δ(y,z)`.  The laws are stated with `Finer`
   (inequalities); the paper's equalities follow (see `refl_zero_eq`,
   `symm_eq`).  No separation axiom is imposed: this is the paper's
   pseudo-ultrametric, and distinct points may have zero demand.
3. The interpretive demand is a generalized ultrametric.
4. Abstract representation: a map `K` on equivalence relations preserves all
   meets (including the empty meet) iff it is represented by a generalized
   ultrametric; the representing ultrametric is unique.
5. Consequence: the representing ultrametric of `K_Q` is the pairwise demand.

## Prior work

The correspondence between meet-preserving families of equivalence relations
and lattice-valued ultrametrics is prior work.  This file verifies the paper's
finite-interpretive specialization of it, not a new correspondence.

## Universes

Meets over arbitrary index types `ι : Type v` (the universe of the occurrence
carrier `A`) are the meets available inside the lattice of relations on `A`.
-/

@[expose] public section

namespace SE.InterpretiveKernel

universe u v w

variable {E : Type u} {A : Type v} {P : Type w}

/-! ## 1. Pairwise demand -/

/-- The principal pair regime `γ_{x,y}`: the least equivalence relation on
frames identifying `x` and `y`. -/
def principalPair {X : Type u} (x y : X) : X → X → Prop :=
  EqvClosure (fun a b => a = x ∧ b = y)

/-- `γ_{x,y}` is below an equivalence relation `τ` iff `τ` identifies `x` and `y`. -/
theorem principalPair_finer_iff {X : Type u} {τ : X → X → Prop}
    (hτ : Equivalence τ) (x y : X) :
    Finer (principalPair x y) τ ↔ τ x y := by
  constructor
  · intro h
    exact h x y (EqvClosure.of ⟨rfl, rfl⟩)
  · intro h
    apply EqvClosure.le_of_equivalence hτ
    intro a b ⟨ha, hb⟩
    subst ha
    subst hb
    exact h

/-- Pairwise interpretive demand `δ_Q(x,y) = L_Q(γ_{x,y})`. -/
def demand (I : P → E → A) (Q : P → Prop) (x y : E) : A → A → Prop :=
  liftRel I Q (principalPair x y)

/-- Demand is an equivalence relation. -/
theorem demand_equivalence (I : P → E → A) (Q : P → Prop) (x y : E) :
    Equivalence (demand I Q x y) :=
  liftRel_equivalence I Q _

/-- Pairwise threshold characterization: `K_Q(ρ) x y ↔ δ(x,y) ≤ ρ`. -/
theorem kernelRel_iff_demand_finer (I : P → E → A) (Q : P → Prop)
    {ρ : A → A → Prop} (hρ : Equivalence ρ) (x y : E) :
    kernelRel I Q ρ x y ↔ Finer (demand I Q x y) ρ := by
  unfold demand
  rw [adjunction I Q hρ]
  exact (principalPair_finer_iff (kernelRel_equivalence I Q hρ) x y).symm

/-- Explicit form: `δ(x,y)` is the equivalence closure of
`{(I p x, I p y) | p selected}`. -/
theorem demand_explicit (I : P → E → A) (Q : P → Prop) (x y : E) :
    demand I Q x y =
      EqvClosure (fun a b => ∃ p, Q p ∧ a = I p x ∧ b = I p y) := by
  apply Finer.antisymm
  · have hE : Equivalence
        (EqvClosure (fun a b => ∃ p, Q p ∧ a = I p x ∧ b = I p y)) :=
      EqvClosure.equivalence _
    rw [← kernelRel_iff_demand_finer I Q hE x y]
    intro p hp
    exact EqvClosure.of ⟨p, hp, rfl, rfl⟩
  · apply EqvClosure.le_of_equivalence (demand_equivalence I Q x y)
    intro a b ⟨p, hp, ha, hb⟩
    subst ha
    subst hb
    exact liftRel_of_pair I Q hp (EqvClosure.of ⟨rfl, rfl⟩)

/-! ## 2. Generalized ultrametrics -/

/-- An `Eq(A)`-valued generalized (pseudo-)ultrametric on `X`.
The three laws are the paper's (U1)-(U3) in inequality form. -/
structure GeneralizedUltrametric (X : Type u) (A : Type v) where
  /-- The value at a pair of points: an equivalence relation on `A`. -/
  dist        : X → X → A → A → Prop
  /-- Each value `dist x y` is an equivalence relation on `A`. -/
  equivalence : ∀ x y, Equivalence (dist x y)
  /-- (U1) `δ(x,x) ≤ ⊥`; with reflexivity this is `δ(x,x) = ⊥`. -/
  refl_zero   : ∀ x, Finer (dist x x) (diagonalRel A)
  /-- (U2) symmetry (one direction suffices). -/
  symm        : ∀ x y, Finer (dist x y) (dist y x)
  /-- (U3) strong triangle inequality. -/
  triangle    : ∀ x y z, Finer (dist x z) (joinRel2 (dist x y) (dist y z))

namespace GeneralizedUltrametric

variable {X : Type u} (U : GeneralizedUltrametric X A)

/-- The paper's (U1) as an equality. -/
theorem refl_zero_eq (x : X) : U.dist x x = diagonalRel A :=
  Finer.antisymm (U.refl_zero x) (finer_diagonalRel (U.equivalence x x).refl)

/-- The paper's (U2) as an equality. -/
theorem symm_eq (x y : X) : U.dist x y = U.dist y x :=
  Finer.antisymm (U.symm x y) (U.symm y x)

end GeneralizedUltrametric

/-! ## 3. Interpretive demand is a generalized ultrametric -/

/-- The pairwise interpretive demand is an equivalence relation on frames. -/
theorem demand_refl_zero (I : P → E → A) (Q : P → Prop) (x : E) :
    Finer (demand I Q x x) (diagonalRel A) := by
  have hk : kernelRel I Q (diagonalRel A) x x :=
    (kernelRel_equivalence I Q (diagonalRel_equivalence A)).refl x
  exact (kernelRel_iff_demand_finer I Q (diagonalRel_equivalence A) x x).1 hk

/-- The pairwise interpretive demand is symmetric. -/
theorem demand_symm (I : P → E → A) (Q : P → Prop) (x y : E) :
    Finer (demand I Q x y) (demand I Q y x) := by
  have hρ := demand_equivalence I Q y x
  have hyx : kernelRel I Q (demand I Q y x) y x :=
    (kernelRel_iff_demand_finer I Q hρ y x).2 (Finer.refl _)
  have hxy : kernelRel I Q (demand I Q y x) x y :=
    (kernelRel_equivalence I Q hρ).symm hyx
  exact (kernelRel_iff_demand_finer I Q hρ x y).1 hxy

/-- The pairwise interpretive demand satisfies the triangle inequality. -/
theorem demand_triangle (I : P → E → A) (Q : P → Prop) (x y z : E) :
    Finer (demand I Q x z) (joinRel2 (demand I Q x y) (demand I Q y z)) := by
  have hρ := joinRel2_equivalence (demand I Q x y) (demand I Q y z)
  have hxy : kernelRel I Q (joinRel2 (demand I Q x y) (demand I Q y z)) x y :=
    (kernelRel_iff_demand_finer I Q hρ x y).2
      (finer_joinRel2_left (demand I Q x y) (demand I Q y z))
  have hyz : kernelRel I Q (joinRel2 (demand I Q x y) (demand I Q y z)) y z :=
    (kernelRel_iff_demand_finer I Q hρ y z).2
      (finer_joinRel2_right (demand I Q x y) (demand I Q y z))
  have hxz := (kernelRel_equivalence I Q hρ).trans hxy hyz
  exact (kernelRel_iff_demand_finer I Q hρ x z).1 hxz

/-- The pairwise interpretive demand as a generalized ultrametric on frames. -/
def demandUltrametric (I : P → E → A) (Q : P → Prop) : GeneralizedUltrametric E A where
  dist        := demand I Q
  equivalence := demand_equivalence I Q
  refl_zero   := demand_refl_zero I Q
  symm        := demand_symm I Q
  triangle    := demand_triangle I Q

/-! ## 4. Abstract representation of meet-preserving maps -/

/-- A map `K` on relations is a complete meet homomorphism on equivalence
relations: it sends equivalences to equivalences and preserves meets of every
family of equivalences, including the empty family (so `K ⊤ = ⊤`). -/
def PreservesMeets {X : Type u} {A : Type v}
    (K : (A → A → Prop) → X → X → Prop) : Prop :=
  (∀ ρ, Equivalence ρ → Equivalence (K ρ)) ∧
  ∀ (ι : Type v) (ρs : ι → A → A → Prop), (∀ i, Equivalence (ρs i)) →
    K (meetRel ρs) = meetRel (fun i => K (ρs i))

/-- Meet-preserving maps are monotone on equivalence relations. -/
theorem PreservesMeets.monotone {X : Type u} {A : Type v}
    {K : (A → A → Prop) → X → X → Prop} (hK : PreservesMeets K)
    {α β : A → A → Prop} (hα : Equivalence α) (hβ : Equivalence β)
    (h : Finer α β) : Finer (K α) (K β) := by
  let pair : ULift.{v} Bool → A → A → Prop := fun b => if b.down then α else β
  have hpair : ∀ b, Equivalence (pair b) := by
    intro b
    cases b with
    | up b =>
      cases b
      · exact hβ
      · exact hα
  have hmeet : meetRel pair = α := by
    apply Finer.antisymm
    · exact meetRel_finer pair (ULift.up true)
    · refine finer_meetRel_iff.2 ?_
      intro b
      cases b with
      | up b =>
        cases b
        · exact h
        · exact Finer.refl α
  have key := hK.2 (ULift.{v} Bool) pair hpair
  rw [hmeet] at key
  intro x y hxy
  have := congrFun (congrFun key x) y
  have hx : meetRel (fun b => K (pair b)) x y := by
    rw [← this]
    exact hxy
  exact hx (ULift.up false)

/-- The representing value `δ_K(x,y) = ⋀ {ρ equivalence | K ρ x y}`. -/
def representingDist {X : Type u} {A : Type v}
    (K : (A → A → Prop) → X → X → Prop) (x y : X) : A → A → Prop :=
  meetRel (fun r : {ρ : A → A → Prop // Equivalence ρ ∧ K ρ x y} => r.val)

/-- Key equivalence for the representing value. -/
theorem representingDist_key {X : Type u} {A : Type v}
    {K : (A → A → Prop) → X → X → Prop} (hK : PreservesMeets K)
    {ρ : A → A → Prop} (hρ : Equivalence ρ) (x y : X) :
    K ρ x y ↔ Finer (representingDist K x y) ρ := by
  have hS : Equivalence (representingDist K x y) :=
    meetRel_equivalence (fun r => r.property.1)
  constructor
  · intro h
    intro a b hab
    exact hab ⟨ρ, hρ, h⟩
  · intro h
    have hKS : K (representingDist K x y) x y := by
      have := congrFun (congrFun
        (hK.2 {ρ : A → A → Prop // Equivalence ρ ∧ K ρ x y}
          (fun r => r.val) (fun r => r.property.1)) x) y
      unfold representingDist
      rw [this]
      intro r
      exact r.property.2
    exact PreservesMeets.monotone hK hS hρ h x y hKS

/-- Representation theorem, forward direction: a complete meet homomorphism
on equivalence relations is represented by a generalized ultrametric. -/
theorem representation_of_preservesMeets {X : Type u} {A : Type v}
    {K : (A → A → Prop) → X → X → Prop} (hK : PreservesMeets K) :
    ∃ U : GeneralizedUltrametric X A,
      ∀ ρ, Equivalence ρ → ∀ x y, K ρ x y ↔ Finer (U.dist x y) ρ := by
  refine ⟨
    { dist := representingDist K
      equivalence := fun x y => meetRel_equivalence (fun r => r.property.1)
      refl_zero := ?_
      symm := ?_
      triangle := ?_ },
    fun ρ hρ x y => representingDist_key hK hρ x y⟩
  · intro x
    have hk : K (diagonalRel A) x x :=
      (hK.1 _ (diagonalRel_equivalence A)).refl x
    exact (representingDist_key hK (diagonalRel_equivalence A) x x).1 hk
  · intro x y
    have hS : Equivalence (representingDist K y x) :=
      meetRel_equivalence (fun r => r.property.1)
    have hyx : K (representingDist K y x) y x :=
      (representingDist_key hK hS y x).2 (Finer.refl _)
    have hxy : K (representingDist K y x) x y := (hK.1 _ hS).symm hyx
    exact (representingDist_key hK hS x y).1 hxy
  · intro x y z
    have hρ := joinRel2_equivalence (representingDist K x y) (representingDist K y z)
    have hxy : K (joinRel2 (representingDist K x y) (representingDist K y z)) x y :=
      (representingDist_key hK hρ x y).2
        (finer_joinRel2_left (representingDist K x y) (representingDist K y z))
    have hyz : K (joinRel2 (representingDist K x y) (representingDist K y z)) y z :=
      (representingDist_key hK hρ y z).2
        (finer_joinRel2_right (representingDist K x y) (representingDist K y z))
    exact (representingDist_key hK hρ x z).1 ((hK.1 _ hρ).trans hxy hyz)

/-- The map `ρ ↦ {(x,y) | δ(x,y) ≤ ρ}` determined by a generalized ultrametric. -/
def ultrametricKernel {X : Type u} {A : Type v} (U : GeneralizedUltrametric X A)
    (ρ : A → A → Prop) : X → X → Prop :=
  fun x y => Finer (U.dist x y) ρ

/-- Representation theorem, converse: the map determined by a generalized
ultrametric is a complete meet homomorphism on equivalence relations. -/
theorem preservesMeets_ultrametricKernel {X : Type u} {A : Type v}
    (U : GeneralizedUltrametric X A) : PreservesMeets (ultrametricKernel U) := by
  constructor
  · intro ρ hρ
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact Finer.trans (U.refl_zero x) (finer_diagonalRel hρ.refl)
    · intro x y hxy
      exact Finer.trans (U.symm y x) hxy
    · intro x y z hxy hyz
      exact Finer.trans (U.triangle x y z)
        ((joinRel2_finer_iff hρ).2 ⟨hxy, hyz⟩)
  · intro ι ρs _
    funext x y
    apply propext
    exact finer_meetRel_iff

/-- Uniqueness: two generalized ultrametrics representing the same map on
equivalence relations have equal values. -/
theorem ultrametric_unique {X : Type u} {A : Type v}
    {K : (A → A → Prop) → X → X → Prop}
    (U U' : GeneralizedUltrametric X A)
    (hU : ∀ ρ, Equivalence ρ → ∀ x y, K ρ x y ↔ Finer (U.dist x y) ρ)
    (hU' : ∀ ρ, Equivalence ρ → ∀ x y, K ρ x y ↔ Finer (U'.dist x y) ρ)
    (x y : X) : U.dist x y = U'.dist x y := by
  apply Finer.antisymm
  · have h : K (U'.dist x y) x y :=
      (hU' _ (U'.equivalence x y) x y).2 (Finer.refl _)
    exact (hU _ (U'.equivalence x y) x y).1 h
  · have h : K (U.dist x y) x y :=
      (hU _ (U.equivalence x y) x y).2 (Finer.refl _)
    exact (hU' _ (U.equivalence x y) x y).1 h

/-! ## 5. The interpretive kernel family is represented by the demand -/

/-- `K_Q` is a complete meet homomorphism on equivalence relations. -/
theorem preservesMeets_kernelRel (I : P → E → A) (Q : P → Prop) :
    PreservesMeets (kernelRel I Q) := by
  constructor
  · intro ρ hρ
    exact kernelRel_equivalence I Q hρ
  · intro ι ρs _
    exact kernelRel_meet I Q ρs

/-- The pairwise demand is the unique generalized ultrametric representing `K_Q`. -/
theorem demand_unique (I : P → E → A) (Q : P → Prop)
    (U : GeneralizedUltrametric E A)
    (hU : ∀ ρ, Equivalence ρ → ∀ x y, kernelRel I Q ρ x y ↔ Finer (U.dist x y) ρ)
    (x y : E) : U.dist x y = demand I Q x y :=
  ultrametric_unique U (demandUltrametric I Q) hU
    (fun _ hρ a b => kernelRel_iff_demand_finer I Q hρ a b) x y

end SE.InterpretiveKernel
