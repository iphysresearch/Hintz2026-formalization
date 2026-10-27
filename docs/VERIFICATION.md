# Verification status

Checked on 2026-10-27 with Lean `v4.33.1` and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.

| Check | Result and scope |
| --- | --- |
| Source boundary | Re-verified this round: 27 modules in the exact local import closure of `Hintz2026.MainTheorem`; imports limited to `Hintz2026.*` and `Mathlib`. |
| Placeholder scan | Re-verified this round: no `sorry`, `admit`, `native_decide`, or `Lean.ofReduceBool` in the retained Lean source, root, or audit. |
| Lean build and audit | Re-verified this round: `lake build Hintz2026 MainAudit` exited 0. Existing dependency/build caches were reused. |
| Extracted-source rebuild | Re-verified this round: an extracted ZIP with a new package build directory passed `lake build Hintz2026` and a fresh `lake env lean audit/MainAudit.lean`, both exit 0. The pinned dependency cache was reused. |
| Main theorem's axiom closure | Re-verified this round: `[propext, Classical.choice, Quot.sound]` for `Hintz2026.main`, `main_pos`, `main_neg`, `main_pos_on_U`, and `main_neg_on_U`. |
| Historical source comparison | All 27 modules compared with historical commit `7e5917f5d4480e23eb3d765c9935565f01b2a663`; permitted extraction differences described in `PROVENANCE.md`. |
| Lean Comparator | Unavailable in the locked Lake command interface: `lake comparator` exited 1 with `error: unknown command 'comparator'`. No Comparator acceptance is claimed. |

The local logs are `logs/release-build-audit.log` and
`logs/comparator-command.log`. The separate extraction directory also retains
`logs/archive-build.log` and `logs/archive-main-audit.log`. They are excluded
from the source archive. The commands in `REPRODUCIBILITY.md` regenerate the
evidence.
`lake help comparator` returns generic help with exit status 0 on this Lake;
that result must not be treated as Comparator support or acceptance.

For the archive test, the package's `.lake/build` was initially absent;
only `.lake/packages` reused the existing pinned dependency cache. The Lean
sources, audit, build scripts and locked configuration were compared byte for
byte with the final ZIP. This checks rebuilding the packaged proof, without
claiming a fresh download or rebuild of all external dependencies.

The Python boundary scanner is a source packaging check. Neither it nor
this written report substitutes for Lean elaboration and the axiom audit.
The report does not claim an independent semantic review, an offline
reproduction, or verification of results outside `Hintz2026.main`'s scope.
