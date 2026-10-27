#!/usr/bin/env python3
"""Compare the packaged Hintz2026 source boundary with its recorded closure.

This is a source/interface check.  Lean's elaborator and kernel audit remain
the authority for proof correctness and axiom use.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


EXPECTED_MODULES = {
    "Hintz2026.AdjDeriv",
    "Hintz2026.Assembly",
    "Hintz2026.CAdjugate",
    "Hintz2026.CSeparation",
    "Hintz2026.Chiral",
    "Hintz2026.ChiralSmooth",
    "Hintz2026.Derivatives",
    "Hintz2026.Domain",
    "Hintz2026.Eq1to4Identity",
    "Hintz2026.Eq1to4Neg",
    "Hintz2026.Eq1to4Pos",
    "Hintz2026.Eq6",
    "Hintz2026.Equivalence1to4",
    "Hintz2026.Equivalence4to7",
    "Hintz2026.FieldInterface",
    "Hintz2026.IntegratingFactor",
    "Hintz2026.MainTheorem",
    "Hintz2026.Prefactors",
    "Hintz2026.Residual",
    "Hintz2026.Smooth",
    "Hintz2026.SolutionCorr",
    "Hintz2026.System1Defs",
    "Hintz2026.System4Defs",
    "Hintz2026.Transform7",
    "Hintz2026.XDerivatives",
    "Hintz2026.XDiagDeriv",
    "Hintz2026.XEntries",
}

IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$")
FORBIDDEN_RE = re.compile(r"\b(?:sorry|admit)\b|native_decide|Lean\.ofReduceBool")


def fail(message: str) -> None:
    print(f"Source boundary check failed: {message}", file=sys.stderr)
    raise SystemExit(1)


def imports(path: Path) -> list[str]:
    found: list[str] = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        match = IMPORT_RE.match(line)
        if match:
            found.append(match.group(1))
        elif line.lstrip().startswith("import "):
            fail(f"cannot parse import at {path}:{line_number}")
    return found


def module_path(repo: Path, module: str) -> Path:
    return repo.joinpath(*module.split(".")).with_suffix(".lean")


def main() -> None:
    repo = Path(__file__).resolve().parent.parent
    source_dir = repo / "Hintz2026"

    actual_files = {
        "Hintz2026." + path.relative_to(source_dir).with_suffix("").as_posix().replace("/", ".")
        for path in source_dir.rglob("*.lean")
    }
    if actual_files != EXPECTED_MODULES:
        missing = sorted(EXPECTED_MODULES - actual_files)
        extra = sorted(actual_files - EXPECTED_MODULES)
        fail(f"27-module boundary mismatch (missing={missing}, extra={extra})")

    graph: dict[str, list[str]] = {}
    for module in sorted(EXPECTED_MODULES):
        path = module_path(repo, module)
        if not path.is_file():
            fail(f"missing source file for {module}: {path}")
        imported = imports(path)
        outside = [name for name in imported if name != "Mathlib" and name not in EXPECTED_MODULES]
        if outside:
            fail(f"{module} imports outside the Hintz2026/Mathlib boundary: {outside}")
        graph[module] = [name for name in imported if name in EXPECTED_MODULES]

    reachable: set[str] = set()
    pending = ["Hintz2026.MainTheorem"]
    while pending:
        module = pending.pop()
        if module in reachable:
            continue
        reachable.add(module)
        pending.extend(graph[module])
    if reachable != EXPECTED_MODULES:
        fail(
            "MainTheorem transitive closure mismatch "
            f"(missing={sorted(EXPECTED_MODULES - reachable)}, "
            f"extra={sorted(reachable - EXPECTED_MODULES)})"
        )

    root_imports = imports(repo / "Hintz2026.lean")
    if root_imports != ["Hintz2026.MainTheorem"]:
        fail(f"root Hintz2026.lean must import MainTheorem exactly once, got {root_imports}")
    audit_imports = imports(repo / "audit" / "MainAudit.lean")
    if audit_imports != ["Hintz2026.MainTheorem"]:
        fail(f"audit boundary must import MainTheorem exactly once, got {audit_imports}")

    main_source = (repo / "Hintz2026" / "MainTheorem.lean").read_text(encoding="utf-8")
    if "namespace Hintz2026" not in main_source or not re.search(r"\btheorem\s+main\s*\(", main_source):
        fail("Hintz2026.main declaration anchor is missing from MainTheorem.lean")

    checked_files = [*sorted(source_dir.rglob("*.lean")), repo / "Hintz2026.lean", repo / "audit" / "MainAudit.lean"]
    violations: list[str] = []
    for path in checked_files:
        for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if FORBIDDEN_RE.search(line):
                violations.append(f"{path.relative_to(repo)}:{line_number}")
    if violations:
        fail("proof placeholder or forbidden reduction token found at " + ", ".join(violations))

    print("Source boundary check passed (not a Lean Comparator verdict)")
    print(f"  modules: {len(reachable)} (MainTheorem transitive closure)")
    print("  imports: Hintz2026 modules plus Mathlib only")
    print("  anchor: Hintz2026.main")
    print("  placeholders: none")


if __name__ == "__main__":
    main()
