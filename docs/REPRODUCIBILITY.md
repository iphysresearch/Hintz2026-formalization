# Reproducibility record

## Source boundary

The package was extracted from the `Hintz2026` proof module and its transitive
imports only. The retained modules are:

`Domain`, `IntegratingFactor`, `Derivatives`, `Eq6`, `System4Defs`,
`System1Defs`, `Prefactors`, `Assembly`, `XEntries`, `XDerivatives`,
`XDiagDeriv`, `Smooth`, `FieldInterface`, `SolutionCorr`, `Residual`,
`Chiral`, `Eq1to4Identity`, `Eq1to4Pos`, `Eq1to4Neg`, `Equivalence1to4`,
`ChiralSmooth`, `Transform7`, `AdjDeriv`, `CSeparation`, `CAdjugate`,
`Equivalence4to7`, and `MainTheorem`.

The independent audit imports only `MainTheorem`. `System8`, `CEntries`, the
old Sprint 02 audit files, and all parent-project modules are outside this
theorem's import closure and are excluded.

## Verification commands

Run these commands with Lean `v4.33.1` and the manifest as checked in:

```bash
python3 -I scripts/check_source_boundary.py
bash scripts/check_no_placeholders.sh
python3 -I scripts/run_logged.py logs/build.log \
  ./scripts/build_isolated.sh lake build Hintz2026
python3 -I scripts/run_logged.py logs/main-audit.log \
  ./scripts/build_isolated.sh lake build MainAudit
```

The audit must exit with status 0 and report no `sorryAx`, `admitAx`, or other
nonstandard proof axiom for `Hintz2026.main`. The source scan must report no
`sorry`, `admit`, `native_decide`, or `Lean.ofReduceBool` in the retained Lean
files.

The log runner creates the log directory and writes output and the exit
status to the named file. Check `exit=0` at the end of each successful log.
`lake build MainAudit` elaborates the audit and prints its results; the
resulting empty executable does not recheck the theorem when run later.
To force a fresh audit elaboration while reusing built imports, run:

```bash
python3 -I scripts/run_logged.py logs/audit-fresh.log \
  ./scripts/build_isolated.sh lake env lean audit/MainAudit.lean
```

## Initial setup and archive reproduction

Prerequisites are the pinned Lean toolchain managed by elan, Bash, Python
3.9 or newer, Git, and ripgrep. Install these if absent. Initial dependency
downloads need network access. For a source-only fresh checkout, the pinned
Mathlib cache can be fetched without changing versions:

```bash
python3 -I scripts/run_logged.py logs/mathlib-cache.log \
  ./scripts/build_isolated.sh lake exe cache get
```

Then run the build and audit above. The ZIP contains no Mathlib sources or
compiled dependencies and is not an offline bundle.

Each release ZIP contains a `SHA256SUMS` file. After extracting it and
entering its top-level directory, verify every packaged file with either:

```bash
sha256sum -c SHA256SUMS        # Linux
shasum -a 256 -c SHA256SUMS    # macOS
```

To reproduce the archive from the same source tree, run
`python3 -I scripts/make_release.py`. The script uses the explicit
`RELEASE_FILES.txt` allowlist, stable entry order, timestamps and modes, and
generates a SHA-256 sidecar for the ZIP. Python/zlib versions can affect
compression bytes; the internal per-file checksums are the portable source
identity.

## Comparator verification

`scripts/check_source_boundary.py` recomputes the import graph from the
source and checks the 27-module closure, the permitted import boundary,
entry points, main declaration anchor and placeholder tokens. It is a
source packaging check, not Lean Comparator.

On 2026-10-27, the real command `lake comparator` in this locked environment
returned `error: unknown command 'comparator'` with exit status 1. Its help
queries return generic Lake help and do not establish support. No Comparator
acceptance result is available, and no toolchain upgrade was made to obtain
one. Lean build and axiom-audit results are reported separately in
[`VERIFICATION.md`](VERIFICATION.md).

## Reproduction policy

Do not run `lake update`, change the Mathlib revision, or change the Lean
toolchain when reproducing the recorded result. Build artifacts belong in
`.lake/` and logs belong in `logs/`; both are ignored by Git.
