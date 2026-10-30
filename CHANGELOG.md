# Changelog

<!-- markdownlint-disable MD024 -->

All notable changes to this project will be documented in this file.

The format is based on **[Keep a Changelog](https://keepachangelog.com/en/1.1.0/)**
and this project adheres to **[Semantic Versioning](https://semver.org/spec/v2.0.0.html)**.

---

## [Unreleased]

---

## [0.1.0] - 2026-10-30

### Added

- Initial Lean 4 formalization of the SE-220 Interpretive Kernel theory.
  Public import: `SE.InterpretiveKernel`. Lean core only; no Mathlib.
- `SE.InterpretiveKernel.Core`: the ordering convention (`Finer R S` is
  `R ⊆ S`; finer is lower) and `EqvClosure`, with minimality and monotonicity.
- `SE.InterpretiveKernel.Kernel`: the interpretation-induced kernel
  `kernelRel` (`K_Q(ρ)`), coherence, and monotonicity in the occurrence
  relation and the probe family.
- `SE.InterpretiveKernel.Lifting`: the generated occurrence regime `liftRel`
  (`L_Q(φ)`) as the least compatible occurrence relation, with minimality,
  uniqueness, and monotonicity.
- `SE.InterpretiveKernel.Adjunction`: the adjunction `L_Q ⊣ K_Q`, unit,
  counit, and the closure identities `L K L = L` and `K L K = K`.
- `SE.InterpretiveKernel.Lattice` and `SE.InterpretiveKernel.Preservation`:
  meets and joins of relations; `K` preserves meets, `L` preserves joins;
  probe-family union duality; the empty probe family.
- `SE.InterpretiveKernel.Generating`: generating-set reduction for the
  generated occurrence regime.
- `SE.InterpretiveKernel.Threshold`: admissible occurrence regimes and the
  interpretive threshold, including extremal regimes and the threshold as the
  meet of all admissible regimes.
- `SE.InterpretiveKernel.Representation`: pairwise interpretive demand, the
  generalized (pseudo-)ultrametric laws, and the representation theorem for
  complete meet homomorphisms on equivalence relations, with uniqueness.
- `SE.InterpretiveKernel.Signature`: bridges to the paper's probe signature
  and fixed probe family.
- `SE.InterpretiveKernel.Witness`: incompatibility witnesses and a bounded
  decision procedure over explicit enumerations.
- `SETest.InterpretiveKernel.Examples` and
  `SETest.InterpretiveKernel.ExamplesPaper`: finite examples and
  counterexamples, including a strict unit and counit, `K` not preserving
  joins, `L` not preserving meets, incomparable thresholds, and the failure of
  the adjunction without `Equivalence ρ`.
- Root drivers `SE.lean` and `SETest.lean`, using the Lean module system.
- `docs/en/index.md`, `DOUBTS.md`, and `DECISIONS.md`.
- Theory reference under `reference/`: `theory-reference.toml`, and registries
  for types, vocabulary, predicates, theorems, and dependencies.

---

## Notes on versioning and releases

- We use **SemVer**:
  - **MAJOR** - breaking changes
  - **MINOR** - backward-compatible additions
  - **PATCH** - fixes, documentation, tooling
- Versions are driven by git tags.
- Tag `vX.Y.Z` to release.
- During `0.x` development, breaking formal-surface changes
  may occur in a **MINOR** release.

## Release Procedure (Required)

Follow these steps exactly when creating a new release.

### One-Time Zenodo Authorization

1. Sign in to Zenodo.
2. Open your profile menu in the upper-right.
3. Select GitHub.
4. Click Sync now.
5. Find structural-explainability/ this repo.
6. Turn on the repository toggle/slider.
7. Refresh the page and confirm it appears as enabled.
8. Zenodo will ingest future GitHub Releases from this repo.

### Task 1. Update release metadata (manual edits)

1.1. CITATION.cff: update version and date-released
1.2. lakefile.toml: update version
1.3. CHANGELOG.md: add section, move unreleased entries, update links
1.4. pyproject.toml: update version (near top of the file)

### Task 2. Set up and Validate

```pwsh
# set up or update Python environment
# Run repository checks.
.\sit.ps1

# Update GitHub Actions and pin all action references to immutable SHAs.
uvx gha-tools autoupdate --pin=all --write .github/workflows

# Audit the resulting GitHub configuration for security findings.
# NO .github\workflows\deploy-zensical.yml
# YES  .github\workflows\deploy-zensical-lean.yml
uvx zizmor@latest .github/
# Some suppressed are still okay

# Validate.
uvx cffconvert --validate
uvx se-manifest-schema validate-manifest --strict

# Format Markdown.
npx markdownlint-cli2 --fix

.\rel.ps1
.\sit.ps1
```

Review all generated and modified files before committing.

### Task 3. Commit, tag, push

```shell
git add -A
git commit -m "Prep X.Y.Z"
git push -u origin main
```

Verify actions run on GitHub. After success:

```shell
git tag vX.Y.Z -m "X.Y.Z"
git push origin vX.Y.Z
```

### Task 4. After tagging, verify tag consistency

```shell
uvx --from se-manifest-schema se-manifest check-version --require-tag
```

Confirms CITATION.cff version matches the pushed git tag.
Run this after `git push origin vX.Y.Z`; it will fail before that point.

## Only As Needed (delete a tag)

```shell
git tag -d vX.Z.Y
git push origin :refs/tags/vX.Z.Y
```

## Links

[Unreleased]: https://github.com/structural-explainability/se-theory-interpretive-kernel/compare/v0.3.0...HEAD
[0.1.0]: https://github.com/structural-explainability/se-theory-interpretive-kernel/releases/tag/v0.1.0
