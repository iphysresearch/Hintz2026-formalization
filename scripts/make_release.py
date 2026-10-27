#!/usr/bin/env python3
"""Create a source-only release ZIP from an explicit reviewed allowlist."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path, PurePosixPath
import subprocess
import sys
import zipfile


ROOT_NAME = "Hintz2026-formalization-v0.1.0"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    repo = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=repo / "dist")
    args = parser.parse_args()
    subprocess.run(
        [sys.executable, "-I", str(repo / "scripts/check_source_boundary.py")],
        check=True,
    )
    paths = (repo / "RELEASE_FILES.txt").read_text(encoding="utf-8").splitlines()
    if not paths or paths != sorted(set(paths)):
        raise SystemExit("RELEASE_FILES.txt must contain unique sorted paths")
    files: dict[str, bytes] = {}
    for name in paths:
        path = PurePosixPath(name)
        if path.is_absolute() or ".." in path.parts or str(path) != name:
            raise SystemExit(f"unsafe archive path: {name}")
        if any(part.startswith(".") and part != ".gitignore" for part in path.parts):
            raise SystemExit(f"hidden development material is not allowed: {name}")
        if path.suffix not in {".lean", ".md", ".json", ".toml", ".py", ".sh", ".txt", ".bib"} and name not in {".gitignore", "lean-toolchain", "LICENSE"}:
            raise SystemExit(f"unexpected source-file type: {name}")
        source = repo / name
        if any(p.is_symlink() for p in (source, *source.parents) if p != repo.parent):
            raise SystemExit(f"symlink is not allowed in the release: {name}")
        if not source.is_file():
            raise SystemExit(f"missing allowlisted file: {name}")
        files[name] = source.read_bytes()
    lean_files = {
        str(p.relative_to(repo)) for directory in (repo / "Hintz2026", repo / "audit")
        for p in directory.rglob("*.lean")
    } | {"Hintz2026.lean"}
    if {name for name in files if name.endswith(".lean")} != lean_files:
        raise SystemExit("archive Lean file boundary differs from the checked source")
    checksums = "".join(f"{sha256(data)}  {name}\n" for name, data in files.items())
    files["SHA256SUMS"] = checksums.encode("utf-8")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    archive = args.output_dir / f"{ROOT_NAME}.zip"
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as output:
        for name, data in sorted(files.items()):
            info = zipfile.ZipInfo(f"{ROOT_NAME}/{name}", date_time=(1980, 1, 1, 0, 0, 0))
            info.create_system = 3
            mode = 0o755 if name.startswith("scripts/") and name.endswith(".sh") else 0o644
            info.external_attr = (0o100000 | mode) << 16
            output.writestr(info, data, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    digest = sha256(archive.read_bytes())
    sidecar = archive.with_suffix(archive.suffix + ".sha256")
    sidecar.write_text(f"{digest}  {archive.name}\n", encoding="utf-8")
    print(f"Archive: {archive}")
    print(f"Files: {len(files)}; bytes: {archive.stat().st_size}")
    print(f"SHA-256: {digest}")
    print(f"Checksum file: {sidecar}")


if __name__ == "__main__":
    main()
