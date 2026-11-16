# Sharp matrix tests: Lean 4 and Python verification

Verification software accompanying Mohammadreza Mohajer's **Sharp matrix tests and integral gluing over affine p-adic groups**.

This public package contains the verification programs, selected formal proofs, documentation, and recorded outputs. The manuscript can be found in author's webpage.

The package includes 33 checked Lean theorem declarations, 6,866 exact Python checks, and four finite companion searches with minima 7, 11, 19, and 7. [The scope table](docs/FORMALIZATION_SCOPE.md) identifies the algebraic statements proved in Lean and their relation to the paper's written arithmetic and analytic arguments.

## Run Python

Use Python 3.10 or later from the repository root:

```text
python -m pip install -r python/requirements-verification.txt
python tools/run_python_checks.py
```

The runner executes all four exact suites and all four searches. It writes `results/python_run_status.json`; the individual outputs are beside the programs in `python/`. The suite counts are 1,752, 177, 1,027, and 3,910. The mathematical calculation routines are identical to those in the earlier package; only their output provenance was adapted to avoid reading the manuscript.

For individual runs:

```text
python python/verify_examples.py
python python/verify_period_formulas.py
python python/verify_extended_formulas.py
python python/verify_weighted_division.py
python python/cyclotomic_search.py --p 3 --d 2 --e 1
```

Keep the Python programs together. The extended suite imports arithmetic utilities from `verify_period_formulas.py`. `verification_context.py` reads the small citation record `paper_reference.json`.

## Run Lean

Install Lean using [the official instructions](https://lean-lang.org/install/), then run:

```text
cd lean
lake exe cache get
cd ..
python tools/run_lean_checks.py
```

The project pins Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The compiler output, source hashes, and every theorem's axiom report are in [results/lean/](results/lean/). The proof sources and saved Lean results are unchanged from the checked full package. The allowed standard axioms are `propext`, `Classical.choice`, and `Quot.sound`; no custom axioms or proof placeholders are introduced.

The saved run used the official portable Windows compiler with the pinned dependencies. `tools/run_lean_checks.py --lean-executable PATH_TO_LEAN` supports that route when the dependencies are already on `LEAN_PATH`. Generated `.olean` files and dependency downloads are recreated by the build commands.

## Contents

| Path | Contents |
| --- | --- |
| `lean/` | Six formalization modules, complete import file, axiom audit, and dependency lockfiles |
| `python/` | All exact calculation programs, their outputs, and pinned requirements |
| `results/` | Python run record, Lean compiler output, and package checks |
| `tools/` | Reproduction, integrity, citation, and content-manifest tools |
| `docs/` | Scope, literature comparison, reproduction, publishing, and citation instructions |
| `.github/workflows/verification.yml` | Python and Lean jobs for GitHub Actions |
| `paper_reference.json` | Citation metadata and a historical manuscript identifier |

`paper_reference.json` records the hash of the manuscript snapshot used when the verification was prepared. This is historical provenance, not a freshly recomputed paper hash. No paper file is needed by the public programs.

Run `python tools/check_integrity.py --archive-bytes` to check the supplied snapshot. Fresh runs change output timestamps; use `python tools/update_manifest.py` to record an intentionally regenerated snapshot.

## Publication, citation, and scope

[Publishing instructions](docs/PUBLISHING.md) explain the upload. After creating the public repository, run `python tools/link_repository.py ACTUAL_GITHUB_URL` to update `CITATION.cff` and [the citation text](docs/CITATION.md). Cite that software from the paper's appendix. Your journal manuscript can remain outside GitHub.

The finite calculations supplement the written proofs. Lean establishes the precise algebraic statements in the supplied sources; the local-field constructions, spectral classification, period rings, and analytic estimates retain their written arguments. The general regulator and unrestricted biextension constructions remain further research problems in the paper.

The verification programs, proof scripts, and documentation were prepared with assistance from OpenAI's ChatGPT. The mathematical attribution is described in [the literature comparison](docs/LITERATURE_COMPARISON.md). Mathlib supplies the polynomial, matrix, characteristic-p, and Cayley-Hamilton results used by the formalization.
