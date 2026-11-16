# Reproduce the public verification package

The paper PDF and TeX source are not required. All mathematical calculation routines, parameter lists, and selected formal statements are in this package.

1. Run `python tools/check_integrity.py --archive-bytes` before changing outputs.
2. Install `python/requirements-verification.txt` with Python 3.10 or later.
3. Run `python tools/run_python_checks.py` from the root.
4. With Lean installed, run `lake exe cache get` inside `lean/`.
5. From the root, run `python tools/run_lean_checks.py`.

## Expected outputs

| Program | Expected result |
| --- | --- |
| `verify_examples.py` | 1,752 exact checks |
| `verify_period_formulas.py` | 177 exact checks |
| `verify_extended_formulas.py` | 1,027 exact checks |
| `verify_weighted_division.py` | 3,910 independent finite-ring checks |
| Companion search (3,2,1) | Minimum 7 |
| Companion search (5,2,1) | Minimum 11 |
| Companion search (3,3,1) | Minimum 19 |
| Companion search (3,3,2) | Minimum 7 |
| Lean project | 33 theorem declarations and 33 axiom reports |

The first and fourth Python suites and the search use only the standard library. The other suites use SymPy 1.14.0 and mpmath 1.3.0. The extended suite imports utilities from the period suite; keep both files together.

The independent finite-ring program exhausts 3,406 small weighted-polynomial cases, tests 480 deterministic larger cases, checks nine sharp-exponent vanishings and nine earlier nonvanishings, and detects six counterexamples to weakened coefficient hypotheses.

The Lean toolchain is 4.19.0, with Mathlib v4.19.0 at the committed revision and all nine dependencies pinned in the lockfile. The saved source and axiom records remain valid for the supplied proof files. The formalization scope is in `FORMALIZATION_SCOPE.md`.

## Provenance and refreshed outputs

Each Python output records its own program hash and the citation metadata from `paper_reference.json`. The manuscript hash there is explicitly a previously recorded reference, not a claim that an absent manuscript was checked by the public runner.

`check_integrity.py` checks the program/output correspondence and the Lean source/axiom records without reading any paper file. Its `--archive-bytes` mode checks the content manifest too. After intentionally rerunning programs, use `python tools/update_manifest.py` to record new timestamps and output bytes.

Git attributes preserve recorded bytes across operating systems. Include `.gitattributes`, `.gitignore`, and `.github/` when uploading the repository.
