/-
Copyright (c) 2026 Denise M. Case. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denise M. Case
-/
module

public import SE.InterpretiveKernel.Preservation

/-!
# SE.InterpretiveKernel.Generating

Generating-set reduction.

`generators I Q G` is defined for any relation `G` on frames, so
`liftRel I Q G` is the equivalence closure of the probe image of `G`.
If `G` generates `φ` (its equivalence closure is `φ`), then `G` generates the
same occurrence regime as `φ`.

Not formalized here: the spanning-forest corollary's count
`|E| - |E/φ|`, which needs cardinality of finite quotients.
-/

@[expose] public section

namespace SE.InterpretiveKernel

universe u v w

variable {E : Type u} {A : Type v} {P : Type w}

/-- If frames `e`, `e'` are joined by a chain of `G`-steps, then for every
selected probe their outputs are related by `L_Q(G)`. -/
theorem liftRel_of_eqvClosure (I : P → E → A) (Q : P → Prop) {G : E → E → Prop}
    {e e' : E} (h : EqvClosure G e e') {p : P} (hp : Q p) :
    liftRel I Q G (I p e) (I p e') := by
  induction h with
  | of hab        => exact liftRel_of_pair I Q hp hab
  | refl a        => exact (liftRel_equivalence I Q G).refl (I p a)
  | symm _ ih     => exact (liftRel_equivalence I Q G).symm ih
  | trans _ _ ih1 ih2 => exact (liftRel_equivalence I Q G).trans ih1 ih2

/-- Generating-set reduction, inclusion form: if `G ⊆ φ ⊆ EqCl(G)` then
`L_Q(G) = L_Q(φ)`. -/
theorem liftRel_eq_of_generates (I : P → E → A) (Q : P → Prop)
    {G φ : E → E → Prop} (hG : Finer G φ) (hφ : Finer φ (EqvClosure G)) :
    liftRel I Q G = liftRel I Q φ := by
  apply Finer.antisymm
  · exact liftRel_monotone I Q hG
  · apply liftRel_le_of_generators I Q (liftRel_equivalence I Q G)
    intro p e e' hp hφe
    exact liftRel_of_eqvClosure I Q (hφ e e' hφe) hp

/-- Generating-set reduction, equality form (the paper's statement):
if `EqCl(G) = φ` then `EqCl(R_{Q,G}) = L_Q(φ)`. -/
theorem liftRel_eq_of_eqvClosure_eq (I : P → E → A) (Q : P → Prop)
    {G φ : E → E → Prop} (h : EqvClosure G = φ) :
    liftRel I Q G = liftRel I Q φ := by
  subst h
  exact liftRel_eq_of_generates I Q (EqvClosure.subset G) (Finer.refl _)

end SE.InterpretiveKernel
