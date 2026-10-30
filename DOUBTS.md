# Research Doubts and Open Questions

This document records the current research assessment,
known limitations, unresolved questions, and safeguards
against overclaiming for this theory.

For the three research criteria, doubt classifications,
status definitions, and procedures, see the
[SE Research Doubts Standard](https://raw.githubusercontent.com/structural-explainability/.github/refs/heads/main/docs/en/research/doubts.md).

## Repository Summary

This assessment is a summary of the present evidence.

| Criterion                | Current assessment                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| ------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Mathematical Correctness | The Lean definitions match the paper's Sections 3 to 6 (compared by reading the TeX). The kernel, generated regime, adjunction, unit and counit, preservation laws, probe-union duality, generating-set reduction, thresholds, pairwise demand, ultrametric laws, and the representation theorem with uniqueness are proved without classical choice. Public declarations are registered in `reference/`. Paper Sections 7 to 10 are not formalized. |
| Scientific Adequacy      | Not established. No choice of probes, regimes, or interpretation is justified here, and no empirical meaning is claimed.                                                                                                                                                                                                                                                                                                                             |
| Theoretical Contribution | Not established by Lean. The paper itself calls the adjunction classical and the representation a finite specialization of prior work. The claimed contribution is the explicit probe-generated pair, its finite construction, and its threshold reading.                                                                                                                                                                                            |

The doubts below identify specific issues affecting these assessments.

---

<!-- markdownlint-disable MD024 -->

## Register 1. Doubts About Assumptions (Undermining Doubts)

These questions concern the premises of an argument.
Even if a theorem is correctly proved, can we establish the assumptions necessary to apply it?

### UM-1. (OPEN) Does the Python implementation match the paper and the Lean?

- Criterion: Mathematical Correctness.
- Status: Open.
- Concern: no executable check ties the Lean to the Python.
- Established: `partition.py` agrees on refinement direction (finer is
  lower), meet as intersection, join as closure of the union, and empty meet
  and join as top and bottom. These match `K_∅ = ⊤` and `L_∅ = ⊥`, which are
  proved in Lean (`kernelRel_noProbes`, `liftRel_noProbes`).
  `lifting.py` states `C(ρ) = {(x, y) | δ(x, y) refines ρ}`, the same form as
  `kernelRel_iff_demand_finer`.
- Unresolved:
  - no Python module for `K`, `L`, or witnesses was available to compare;
  - the other supplied modules (`model.py`, `oracle.py`, `fast.py`,
    `generate.py`, `check.py`, `paper_cases.py`) are SE-210 Operational
    Identity code, not SE-220;
  - `lifting.py` says the kernel construction requires `C` to preserve
    arbitrary meets, while the paper's Monotone Comparison Lifting requires
    only monotonicity. Meet preservation enters at the representation
    theorem. Which is intended is unchecked.
- To close: supply the module computing `K`, `L`, and witnesses; compare it
  on the finite examples in `ExamplesPaper.lean`; state in the Python which
  of monotone and meet-preserving applies to the kernel and which to the
  representation.

### UM-2. (OPEN) Are the computational procedure and its complexity verified?

- Criterion: Mathematical Correctness.
- Status: Open.
- Established in Lean: the mathematical facts the procedure uses.
  Generating-set reduction (`liftRel_eq_of_generates`), explicit pairwise
  form (`demand_explicit`), signature form of the kernel
  (`kernelRel_iff_signature_eq`), and a bounded decision procedure over
  explicit lists (`coherent_or_witness`).
- Unresolved: union-find correctness, near-linear complexity, the
  spanning-forest count `|E| - |E/φ|`, and decidability for arbitrary finite
  carriers. Lean core has no `Fintype`.
- To close: keep correctness under the Python differential tests. A
  list-based correctness theorem for the forest procedure can be added
  later. Complexity bounds in Lean are not recommended.

### UM-3. (OPEN) Are the paper's later results supported by Lean?

- Criterion: Mathematical Correctness.
- Status: Open.
- Concern: only part of the paper is formalized.
- Not in Lean:
  - Section 7 counterexamples on comparison liftings (matching, quotient
    image, partition validation). The finite law checks run in `lifting.py`.
    This is a different construction from `liftRel`.
  - Section 8 schedule interpretation, which is a domain application.
  - Section 10 evidence plan, which is not a Lean question.
- To close: Section 7 can be formalized as a separate module when needed.
  Sections 8 and 10 are outside the scope of a foundational theory.

### UM-4. (OPEN) Do the declared dependencies match the dependencies the Lean source uses?

- Criterion: Mathematical Correctness.
- Status: Open.
- Concern: dependencies must be explicit. `lakefile.toml` requires
  `se-theory-neutral-substrate` and `se-theory-transformation`, but no Lean
  file in this repository imports either one.
- Established: the Lean source imports only Lean core and its own modules.
  `reference/dependency-registry.toml` records both theories as allowed but
  not required, and records identity regimes, operational identity,
  persistence, and the integration theory as forbidden.
- Unresolved: the lakefile and the registry disagree about whether the two
  theories are needed. The forbidden entries are checked only by the absence
  of imports; they record architectural intent that Lean does not enforce.
- To close: remove the two `require`s from `lakefile.toml`, or add an
  import and a theorem that uses each one and mark it required in the
  registry.

## Register 2. Doubts About Conclusions (Rebutting Doubts)

These questions concern whether a claimed conclusion is false.
For example, a counterexample satisfying all the premises
but violating the conclusion would challenge the claimed theorem or its formalization.
A model that violates a required assumption does not
necessarily refute a conditional theorem.
If a counterexample is found,
we must identify the exact claim it challenges and
whether its assumptions are satisfied.

**None currently identified.**

## Register 3. Doubts About What Our Results Mean (Undercutting Doubts)

These questions concern the connection
between a formal theorem and the scientific claim made about it.
A theorem may be correct while its informal interpretation is too strong.
Some of these doubts are addressed by permanent documentation
rules rather than additional proofs.

### UC-1. (OPEN) Closure across probes may force unintended identifications

- Criterion: Scientific Adequacy.
- Status: Open.
- Established: the generating pairs of `L` are not transitive, yet every
  admissible regime must relate their closure (Example E).
- Unresolved: whether this forced identification is acceptable is a domain
  decision that no theorem settles.
- To close: for each application, list the generated identifications beyond
  the generating pairs and justify them or change the probes or regimes.

### UC-2. (OPEN) Theoretical contribution beyond existing machinery

- Criterion: Theoretical Contribution.
- Status: Open.
- Established: Lean confirms the adjunction and the representation are
  correct. It does not address novelty.
  The paper states the adjunction and its preservation laws are classical,
  and the representation is a finite specialization of the prior
  correspondence between meet-preserving equivalence families and
  lattice-valued ultrametrics.
- Claimed in the paper: the explicit probe-generated pair, its finite
  construction from an interpretation table, and its reading as an exact
  threshold. The specialization has three features: the value lattice is
  the partition lattice of occurrences, the family is generated from probes,
  and the pairwise value has an operational threshold meaning.
- To close: independent literature comparison; an application where the
  threshold reading changes a conclusion that the bare adjunction does not.

## Standing Limitations

These limitations remain relevant even when the formal theorems
are mathematically correct.

They are not unresolved mathematical defects.
They identify conditions and boundaries that must be respected
when interpreting or applying the theory.

### SL-1. Occurrence Regimes Must Be Equivalence Relations

The adjunction requires the supplied occurrence relation
to be an equivalence relation.

The result does not hold for arbitrary relations without
the required hypotheses.

Applications must establish these properties before
invoking the adjunction.

### SL-2. Coherence May Be Vacuous

Coherence holds for the total occurrence equivalence
and for an empty selected probe family.

Such results may provide little discriminating information.

Applications must justify their occurrence equivalence
and probe selection before treating coherence as
scientifically informative.

### SL-3. Observational Equivalence Is Not Referent Identity

An interpretation-induced kernel may relate distinct frames.

Likewise, zero pairwise demand does not establish
identity of the intended referents.

The construction identifies equivalence under the
supplied interpretation, probes, and occurrence criterion.
It does not independently establish real-world identity.

### SL-4. Incompatibility Does Not Identify Its Cause

An incompatibility witness establishes that the
supplied frame and occurrence equivalences are
incompatible under the selected interpretation and probes.

It does not determine which assumption or input
is scientifically incorrect.

Diagnosing the cause requires additional evidence.

<!-- markdownlint-enable MD024 -->
