# Hintz2026 Lean Formalization

[中文版](README.zh-CN.md)

This repository contains the self-contained Lean formalization of the theorem
`Hintz2026.main`. It includes only the 27 source modules in its transitive
import closure, the theorem audit, and the files needed to reproduce a build.
The repository does not include the parent Atlas project, its Kerr vacuum
certificates, release bundles, platform theorem stubs, CAS scripts, or other
unrelated material.

The theorem is defined in [`Hintz2026/MainTheorem.lean`](Hintz2026/MainTheorem.lean).
Its statement is `Hintz2026.main`; the proof combines the independently proved
positive- and negative-spin pointwise equivalences `main_pos` and `main_neg`.

## Mathematical scope

Parameters `p : Hintz2026.SubextremalKN` satisfy `M > 0`, `Q ≠ 0`, and
`a² + Q² < M²`. On `U = {(r, θ) : r > M + sqrt(M² − a² − Q²), 0 < θ < π}`,
the theorem proves the pointwise equivalence of systems (1) and (7), through
system (4) and explicit transformations, for arbitrary complex fields smooth
on `U`, both spin signs, and real `ω` and `m`. Equation numbers refer to the
source cited in the Lean files:
[Hintz, arXiv:2609.33661v1](https://arxiv.org/abs/2609.33661v1).

The packaged result is this local equivalence. Derivation from the
Einstein–Maxwell equations, the full separation and spectral argument, and
mode stability are outside its scope. Cite the mathematical source and this
formalization separately.

The corresponding task is the Prove2Me mission
[Exact Vacuum Atlas III: Matrix Integrating Factors and Local Equivalence of Kerr–Newman Perturbation Systems](https://prove2.me/missions/Exact_Vacuum_Atlas_III%3A_Matrix_Integrating_Factors_and_Local_Equivalence_of_Kerr%E2%80%93Newman_Perturbation_Systems).
This mission page provides the formalization task and its context. The precise
claim packaged here is `Hintz2026.main`, with the scope stated above.

## Locked environment

- Lean: `v4.33.1` (`lean-toolchain`)
- Mathlib: commit `0df444a360eaa60ab8c11dca51a86af692955474`
- Lean options: `autoImplicit = false`
- Tools: Bash, Python 3.9 or newer, Git, and ripgrep (`rg`).

The lock file [`lake-manifest.json`](lake-manifest.json) records the exact
Mathlib dependency graph. It is intentionally checked in; do not run
`lake update` when reproducing this result.

## Reproduce

From the repository root:

```bash
python3 -I scripts/check_source_boundary.py
bash scripts/check_no_placeholders.sh
python3 -I scripts/run_logged.py logs/build.log \
  ./scripts/build_isolated.sh lake build Hintz2026
```

To run the kernel-level theorem audit and record a log:

```bash
python3 -I scripts/run_logged.py logs/main-audit.log \
  ./scripts/build_isolated.sh lake build MainAudit
```

The audit prints `#print axioms Hintz2026.main`. The expected axiom closure is
only Lean's standard logical closure:
`[propext, Classical.choice, Quot.sound]`.

The log runner writes command output to the log file. Inspect it with
`tail -n 3 logs/build.log` and
`rg "'Hintz2026.main' depends on axioms" logs/main-audit.log`.
Printed axiom names may include universe annotations.

The first build may fetch the pinned Mathlib dependencies from the URLs in the
manifest. No generated `.lake` or log files are part of the source package.
Install the pinned Lean version with elan if necessary. This is a source
archive; dependencies are obtained locally. See
[`docs/REPRODUCIBILITY.md`](docs/REPRODUCIBILITY.md) for the full procedure.

## Comparator verification

Lean Comparator checks a submitted solution against a specified challenge
and its permitted axioms. **No Comparator acceptance is claimed for this
package.** The pinned environment's support and actual verification status
are recorded in [`docs/VERIFICATION.md`](docs/VERIFICATION.md).

`scripts/check_source_boundary.py` checks the 27-module import closure,
allowed `Hintz2026.*`/`Mathlib` imports, entry points, declaration anchor,
and proof-placeholder tokens. This Python source check is not Lean Comparator;
it does not replace the Lean build, kernel checking, or the axiom audit.

## Import

Downstream files can use the theorem with:

```lean
import Hintz2026.MainTheorem

#check Hintz2026.main
```

The old platform export under the parent project contained theorem
placeholders. Those files are deliberately absent here; this repository
contains the proof-bearing source only.

Source provenance and the publication boundary are recorded in
[`docs/PROVENANCE.md`](docs/PROVENANCE.md). Release checks are listed in
[`docs/PUBLISHING_CHECKLIST.md`](docs/PUBLISHING_CHECKLIST.md).

## Citation and Zenodo

Author: **He Wang** (ORCID [0000-0002-1353-391X](https://orcid.org/0000-0002-1353-391X)). Version: **0.1.0**.

- DOI: [10.5281/zenodo.23684720](https://doi.org/10.5281/zenodo.23684720)
- [Zenodo record](https://zenodo.org/records/23684720)

Version 0.1.0 was published on 2026-10-27 under the Apache-2.0 license.
Use [`CITATION.bib`](CITATION.bib) to cite the immutable Zenodo record:

```bibtex
@misc{hintz2026_lean_formalization,
  author       = {Wang, He},
  title        = {{Hintz2026: A Lean 4 Formalization of the Local Equivalence of Kerr--Newman Perturbation Systems (1) and (7)}},
  year         = {2026},
  version      = {0.1.0},
  publisher    = {Zenodo},
  doi          = {10.5281/zenodo.23684720},
  url          = {https://doi.org/10.5281/zenodo.23684720},
  howpublished = {Lean 4 source code},
  note         = {Author ORCID: 0000-0002-1353-391X. Proof of Hintz2026.main. Lean v4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Licensed under Apache-2.0.}
}
```

## Source archive

```bash
python3 -I scripts/make_release.py
```

The script builds a ZIP from the explicit
[`RELEASE_FILES.txt`](RELEASE_FILES.txt) allowlist and includes checksums.
It excludes Git history, `.lake`, logs, unrelated parent-project materials,
and local upload-page snapshots.

## License

This repository is released under the [Apache License 2.0](LICENSE). The
published Zenodo record uses the same license.
