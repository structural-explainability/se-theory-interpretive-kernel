# SE Theory: Interpretive Kernel

> Lean 4 formalization of Interpretive Kernel theory
> for Structural Explainability.

This repository investigates relationships between identity
criteria on distinct carriers connected by interpretation.

Lean source files under `SE/` are authoritative for formal definitions,
predicates, assumptions, theorems, and proof obligations.

- [GitHub Repository](https://github.com/structural-explainability/se-theory-interpretive-kernel)
- [Paper](https://github.com/structural-explainability/paper-220-interpretive-kernel)
- [Python implementation](https://github.com/structural-explainability/se-interpretive-kernel)
- [Research Doubts and Open Questions](https://github.com/structural-explainability/se-theory-interpretive-kernel/blob/main/DOUBTS.md)
- [Research Decisions](https://github.com/structural-explainability/se-theory-interpretive-kernel/blob/main/DECISIONS.md)

## Interpretive Kernel

Interpretive Kernel theory studies how equivalence requirements
relate across carriers connected by an interpretation function.

It investigates which distinctions and identifications are
preserved, induced, or required when information is interpreted
through another representation.

The formal constructions are relative to supplied carriers,
interpretation functions, and equivalence relations.

They do not independently establish that an interpretation
correctly represents its intended domain or that the supplied
equivalence relations express scientifically justified identity.

## Scope

Repository scope is defined in `SE_MANIFEST.toml`.

## Exclusions

Repository exclusions are defined in `SE_MANIFEST.toml`.

## Import

Downstream Lean projects should import the public surface:

`import SE.InterpretiveKernel`
