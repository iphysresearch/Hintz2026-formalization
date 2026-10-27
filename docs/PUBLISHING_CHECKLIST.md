# Release checklist

- Confirm that `LICENSE` and the Zenodo record use Apache-2.0. The published
  v0.1.0 ZIP is immutable; include `LICENSE` in a future version's allowlist
  when creating a new archive.
- Run the logged build and audit commands in
  [`REPRODUCIBILITY.md`](REPRODUCIBILITY.md).
- Run `python3 -I scripts/check_source_boundary.py` and confirm the
  27-module boundary. This Python check is not Lean Comparator.
- Run `./scripts/check_no_placeholders.sh`.
- Run the logged `MainAudit` target and verify the axiom line for
  `Hintz2026.main` contains only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Review the staged file list and confirm that `.lake/` and `logs/` remain
  ignored.
- Keep the README's Comparator status accurate: this pinned Lake reports
  `unknown command 'comparator'`; no Comparator acceptance is claimed.
- Confirm that both READMEs and `CITATION.bib` agree with Zenodo: He Wang,
  ORCID `0000-0002-1353-391X`, version `0.1.0`, DOI
  `10.5281/zenodo.23684720`.
- Include the Prove2Me mission link in the Zenodo description and Related
  works, as well as in both READMEs.
- Confirm the Zenodo license and repository license agree. Mathlib remains
  an external dependency; this archive does not redistribute its sources.
- Generate the source ZIP with `python3 -I scripts/make_release.py`, verify
  its checksums and file list, and upload that ZIP rather than the working
  directory or a parent-project archive.
- For a future release, review Zenodo's preview and fill the publication date
  with the actual release date before publishing.
- Set the intended Git author identity, create the release commit, and review
  the remote URL before any push.
