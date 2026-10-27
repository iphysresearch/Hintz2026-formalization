# Provenance and publication boundary

The formalization task is the Prove2Me mission
[Exact Vacuum Atlas III: Matrix Integrating Factors and Local Equivalence of Kerr–Newman Perturbation Systems](https://prove2.me/missions/Exact_Vacuum_Atlas_III%3A_Matrix_Integrating_Factors_and_Local_Equivalence_of_Kerr%E2%80%93Newman_Perturbation_Systems).
The mission supplies the task context; the mathematical equation source is
Hintz, arXiv:2609.33661v1, as cited in the retained Lean files.

This package is an isolated extraction of the `Hintz2026.main` proof and its
transitive Lean imports from the parent development. The source was copied
from the proof-bearing modules at the historical closure commit
`7e5917f5d4480e23eb3d765c9935565f01b2a663` and the module prefix was renamed
from `Atlas.Perturbations.Hintz2026` to `Hintz2026` so that the package has no
parent-project import dependency. Compared with that historical commit,
eight residual-identity proofs in `Eq1to4Pos.lean` and `Eq1to4Neg.lean`
simplify powers of `Complex.I` earlier in the same algebraic normalization,
removing redundant intermediate `ring_nf` calls. The theorem statements and
definitions are unchanged. `MainTheorem.lean` also has a neutral docstring
wording change. These differences were checked against all 27 historical
modules during release preparation; the standalone proofs were rebuilt.

Included content is limited to the 27-module import closure of
`Hintz2026.MainTheorem`, its root import, the audit, locked Lake configuration,
and reproducibility scripts and documentation. The parent Atlas libraries,
Einstein-Maxwell work, Kerr vacuum certificates, platform exports, release
artifacts, CAS/reference scripts, credentials, and build caches are excluded.

The Zenodo record `10.5281/zenodo.23684720` was published on 2026-10-27
under Apache-2.0. The repository carries the corresponding `LICENSE` text.

The archive is assembled from `RELEASE_FILES.txt`, not by recursively
compressing the development directory or exporting its Git history. It
contains no upload-page snapshot or local account metadata.
