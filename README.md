# SE Theory: Identity Regimes

[![Docs Site](https://img.shields.io/badge/docs-site-blue?logo=github)](https://structural-explainability.github.io/se-theory-interpretive-kernel/)
[![Repo](https://img.shields.io/badge/repo-GitHub-black?logo=github)](https://github.com/structural-explainability/se-theory-interpretive-kernel)
[![Tooling](https://img.shields.io/badge/python-3.15%2B-blue?logo=python)](./pyproject.toml)
[![License](https://img.shields.io/badge/license-Apache--2.0-yellow.svg)](./LICENSE)

[![CI-Lean](https://github.com/structural-explainability/se-theory-interpretive-kernel/actions/workflows/ci-lean.yml/badge.svg?branch=main)](https://github.com/structural-explainability/se-theory-interpretive-kernel/actions/workflows/ci-lean.yml)
[![CI](https://github.com/structural-explainability/se-theory-interpretive-kernel/actions/workflows/ci-python-zensical.yml/badge.svg?branch=main)](https://github.com/structural-explainability/se-theory-interpretive-kernel/actions/workflows/ci-python-zensical.yml)
[![Docs](https://github.com/structural-explainability/se-theory-interpretive-kernel/actions/workflows/deploy-zensical.yml/badge.svg?branch=main)](https://github.com/structural-explainability/se-theory-interpretive-kernel/actions/workflows/deploy-zensical.yml)
[![Links](https://github.com/structural-explainability/se-theory-interpretive-kernel/actions/workflows/links.yml/badge.svg?branch=main)](https://github.com/structural-explainability/se-theory-interpretive-kernel/actions/workflows/links.yml)

> Lean 4 formalization of the identity regimes of Structural Explainability.

This repository defines the six canonical identity regimes and derived
regime-profile structure over admissible neutral substrates.

For the full documentation, see [`docs/en/index.md`](./docs/en/index.md).

## Authority

Lean source files are authoritative for formal definitions, predicates, axioms,
theorems, proof obligations, and reference rules.

Reference artifacts under `reference/` and generated artifacts under
`data/` mirror the Lean public surface.
They do not define theory semantics independently of Lean.

The CI-Lean workflow builds the declared public Lean surface with
`lake build --wfail`,
failing on reported warnings, including `sorry`.
Successful compilation verifies formal declarations against their
stated assumptions; it does not establish the scientific adequacy
of those assumptions or interpretations.

## Import

Downstream Lean projects should import the public surface:

```text
import SE.InterpretiveKernel
```

The public import surface is curated in:

```text
SE.InterpretiveKernel.lean
SE.InterpretiveKernel/Surface.lean
```

## Developer

Maintain:

- `lakefile.toml`
- `lean-toolchain`
- `reference/theory-reference.toml` - hand-maintained configuration
- `reference/*.toml` - reference source artifacts
- Lean source and RR traceability comments (`-- RR.DEFINES`, `-- RR.IMPLEMENTS`) - hand-maintained theory source

### Clone and Open Project in VS Code

Open a machine terminal where you want the project:

```shell
git clone https://github.com/structural-explainability/se-theory-interpretive-kernel

cd se-theory-interpretive-kernel
code .
```

### In a VS Code terminal

Use VS Code Menu:
View / Command Palette / `Developer: Reload Window` to refresh.

```shell
.\sit.ps1

elan self update
lake update

# build Lean source of truth
lake build
lake test

# inspect shared theory-reference command surface
uv run se-theory-reference --help
uv run se-theory-reference validate --help
uv run se-theory-reference scaffold --help
uv run se-theory-reference export --help
uv run se-theory-reference catalog --help
uv run se-theory-reference inspect --help

# validate reference artifacts against the declared Lean public surface
uv run se-theory-reference validate
uv run se-theory-reference validate --strict

# scaffold reference artifacts from Lean public declarations
uv run se-theory-reference scaffold
uv run se-theory-reference scaffold --dry-run
uv run se-theory-reference scaffold --overwrite

# regenerate or check generated JSON artifacts from reference TOML
uv run se-theory-reference export
uv run se-theory-reference export --check

# build or verify the generated reference catalog
uv run se-theory-reference catalog
uv run se-theory-reference catalog --check

# inspect resolved repository configuration and reference declarations
uv run se-theory-reference inspect

# validate SE manifest file
uvx se-manifest-schema validate-manifest --path SE_MANIFEST.toml --strict

# fix issues
git add -A
uvx pre-commit run --all-files
# repeat if changes were made
uvx pre-commit run --all-files

# type checks, tests, docs
uv run python -m pyright
uv run python -m pytest
uv run python -m zensical build

# save progress
git add -A
git commit -m "update"
git push -u origin main
```

</details>

## Authority Manifest

[.accountability/surfaces.toml](./.accountability/surfaces.toml)

## Citation

[CITATION.cff](./CITATION.cff)

## License

[Apache 2.0](./LICENSE)

## Repository Manifest

[SE_MANIFEST.toml](./SE_MANIFEST.toml)
