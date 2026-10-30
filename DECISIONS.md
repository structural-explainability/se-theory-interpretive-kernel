# Research Decisions

This document records substantive mathematical, architectural,
and interpretive decisions for the Interpretive Kernel theory.

Decisions explain why particular approaches were selected.
They do not replace the authoritative Lean definitions and proofs.

- Formal definitions and theorems: `SE/InterpretiveKernel/`
- Public Lean surface: `SE.InterpretiveKernel`
- Formal declaration registries: `reference/`
- Active research questions and limitations: [DOUBTS.md](DOUBTS.md)
- Repository scope and dependencies: `SE_MANIFEST.toml`

Decisions are recorded with stable identifiers.
Resolved research doubts need not remain in `DOUBTS.md`
when their conclusions are preserved here or in the formal theory.

---

## DEC-001. Use Relation Inclusion as Refinement Order

**Decision:** Accepted.

For relations `R` and `S`, define:

`Finer R S` iff every pair related by `R` is related by `S`.

For equivalence relations, this means that `R` induces a
partition at least as fine as the partition induced by `S`.

The discrete equivalence is the bottom element.
The total equivalence is the top element.

**Rationale:**

This ordering agrees with the paper's refinement convention
and makes the adjunction and lattice operations consistent.

**Consequence:**

All descriptions of refinement, monotonicity, meets,
joins, kernels, and generated regimes must respect
this ordering.

## DEC-002. Keep the Two Carriers Distinct

**Decision:** Accepted.

The theory distinguishes:

- A frame carrier.
- An occurrence carrier.
- A probe carrier.
- An interpretation function connecting them.

Equivalence relations on different carriers are not
interchangeable.

**Rationale:**

The research concerns compatibility across interpretation,
not an assumed identity between the underlying carriers.

**Consequence:**

Connections between frame and occurrence equivalences
must be expressed through the interpretation construction.

The interpretation function is total in the formal model.
Applications must account explicitly for missing,
invalid, or inapplicable interpretations.

## DEC-003. Use Conjunctive Probe Semantics

**Decision:** Accepted.

The interpretation-induced kernel relates two frames
when their interpreted outputs are equivalent under
every selected probe.

The Lean representation selects probes through a predicate
over an ambient probe type.

The paper's fixed probe-family formulation is represented
through this selection.

**Rationale:**

Universal quantification gives an explicit and consistent
meaning to agreement across selected probes.

The Lean theory establishes the associated inclusion,
union, and empty-family laws.

**Consequence:**

Adding probes can refine the induced frame kernel and
increase the required occurrence equivalence.

Probe multiplicity, order, existential selection,
and weighted semantics are not represented by this choice.

The mathematical correctness of conjunctive semantics
does not establish their adequacy for every application.

## DEC-004. Generate the Least Compatible Occurrence Equivalence

**Decision:** Accepted.

The generated occurrence regime is the equivalence closure
of the occurrence pairs induced by selected probes
and frame-equivalence requirements.

**Rationale:**

Equivalence closure supplies the least equivalence relation
containing the generating pairs.

Lean establishes that the construction:

- Is an equivalence relation.
- Contains its generators.
- Is least among equivalences containing those generators.

These properties characterize the intended construction.

**Consequence:**

A separate equivalence theorem against Mathlib's
`Relation.EqvGen` is not required for mathematical correctness.

Such a bridge may be added for interoperability,
but it is not an unresolved foundational obligation.

Applications must still justify any additional
identifications introduced by equivalence closure.

## DEC-005. Do Not Restrict the Foundational Theory to Finite Carriers

**Decision:** Accepted.

The foundational relations and theorems are stated
without assuming finite frame, occurrence, or probe carriers.

**Rationale:**

The central mathematical constructions do not depend
on finiteness.

Finite examples and computational procedures instantiate
the general theory rather than define its scope.

**Consequence:**

Computational decidability, algorithm correctness,
and complexity claims are evaluated separately.

A finite implementation does not establish those
properties for arbitrary carriers.

## DEC-006. Maintain Explicit Paper–Lean Correspondence

**Decision:** Accepted.

The paper and Lean formalization must use compatible
definitions, ordering conventions, and theorem hypotheses.

The initial comparison of the paper's Sections 3–6
with the Lean definitions found agreement for:

- Refinement order.
- Interpretation-induced kernel.
- Generated occurrence regime.
- Adjunction.
- Unit and counit.
- Conjunctive probe semantics.

The signature characterization and probe-selection
correspondence are also expressed by Lean theorems.

**Rationale:**

A machine-checked theorem supports a paper claim only
when the formal statement represents the intended claim.

**Consequence:**

The initial correspondence assessment is based on
reading and comparing the TeX and Lean source.

It is not an automatically verified correspondence
between two independently parsed specifications.

Substantive changes to either formulation require
renewed comparison.

## DEC-007. Audit Formal Assumptions Explicitly

**Decision:** Accepted.

The formalization uses Lean's axiom-reporting facilities
to inspect the assumptions of its declarations.

The reported initial audit found no `Classical.choice`
dependency in the central adjunction, preservation,
generating-set, signature, threshold, and representation results.

`Classical.choice` occurs in selected witness-existence
and finite-example declarations.

Other reported dependencies include `propext`
and `Quot.sound`.

**Rationale:**

A successful Lean build does not by itself communicate
which logical assumptions a result uses.

**Consequence:**

Claims about constructivity or axiom independence
must be scoped to the relevant declarations.

The theory must not be described globally as
choice-free merely because its principal results
do not depend on classical choice.

Axiom audits should be repeated when relevant
definitions or proofs change.

## DEC-008. Distinguish Generated Regimes from Comparison Liftings

**Decision:** Accepted.

Two related constructions use the word "lifting"
in the existing research artifacts.

The Lean function `liftRel` constructs the generated
occurrence regime.

A comparison lifting carries an equivalence on
component outputs to an equivalence on structured objects.

**Rationale:**

These constructions have different mathematical roles
and should not be conflated.

**Consequence:**

In explanatory prose:

- Call `L_P` the generated occurrence regime.
- Call `C` a comparison lifting.

Use the precise Lean identifiers when discussing
formal declarations.

## DEC-009. Separate Mathematical Correctness from Scientific Claims

**Decision:** Accepted.

The research is evaluated against three independent criteria:

1. Mathematical Correctness.
2. Scientific Adequacy.
3. Theoretical Contribution.

**Rationale:**

Formal verification establishes mathematical consequences
of definitions and assumptions.

It does not independently establish that supplied
interpretations, equivalence criteria, or probes
correctly represent intended real-world referents.

Nor does it establish novelty relative to existing theory.

**Consequence:**

Claims of coherence, admissibility, or compatibility
must remain conditional on their declared inputs.

Interpretation-induced equivalence must not be
presented as independently established referent identity.

The adjunction and generalized-ultrametric constructions
must not be claimed as novel merely because they
have been formalized in Lean.

Scientific adequacy and theoretical contribution
remain separately evaluated research obligations.

## DEC-010. Keep the Foundational Theory Independent of Applications

**Decision:** Accepted.

Interpretive Kernel defines mathematical relationships
among equivalences, probes, and interpretations.

It does not incorporate domain-specific scheduling
semantics or operational identity auditing into
the foundational definitions.

**Rationale:**

The formal constructions should remain reusable
across different interpretations and applications.

**Consequence:**

Domain applications must supply and justify their
own carriers, probes, interpretation functions,
and equivalence criteria.

A finite example establishes the behavior of a
mathematical construction under its assumptions.
It does not by itself constitute empirical validation.

---

## Maintenance

Record a new decision when a substantive choice affects
the theory's meaning, assumptions, scope, or interpretation.

Use the next available stable `DEC-` identifier.

Do not renumber existing decisions.

If a decision is superseded, retain its identifier,
mark it superseded, and link to the replacement decision.

Routine implementation details and theorem inventories
belong in the source, reference registries, or changelog.

Active unresolved questions belong in `DOUBTS.md`.
