"""Check public verification sources and outputs; no paper files are required."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads((ROOT / path).read_text(encoding="utf-8"))


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--archive-bytes", action="store_true")
    args = parser.parse_args()
    reference = read("paper_reference.json")
    require(reference["manuscript_files_included"] is False, "Unexpected paper-file policy")
    require(bool(re.fullmatch(r"[0-9a-f]{64}", reference["recorded_manuscript_source_sha256"])), "Invalid historical reference hash")
    for script, result, count in [
        ("verify_examples.py", "finite_check_results.json", 1752),
        ("verify_period_formulas.py", "period_check_results.json", 177),
        ("verify_extended_formulas.py", "extended_check_results.json", 1027),
        ("verify_weighted_division.py", "weighted_division_results.json", 3910),
    ]:
        record = read("python/" + result)
        require(record["status"] == "passed" and record["check_count"] == count, "Failed suite: " + result)
        require(record["paper_reference"] == reference, "Stale citation metadata")
        require(record["script_sha256"] == sha(ROOT / "python" / script), "Stale program: " + script)
    for p, d, e, minimum in [(3, 2, 1, 7), (5, 2, 1, 11), (3, 3, 1, 19), (3, 3, 2, 7)]:
        result = read(f"python/cyclotomic_search_p{p}_d{d}_e{e}.json")
        require(result["minimum_dimension"] == minimum and result["paper_reference"] == reference, "Unexpected search result")
        require(result["script_sha256"] == sha(ROOT / "python/cyclotomic_search.py"), "Stale search program")
    lean = read("results/lean/status.json")
    require(lean["status"] == "passed" and lean["theorem_count"] == 33, "Lean run did not pass")
    for name, expected in {**lean["source_sha256"], **lean["configuration_sha256"]}.items():
        require(sha(ROOT / "lean" / name) == expected, "Stale Lean source or configuration: " + name)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    require(len(lean["axiom_reports"]) == len(set(lean["theorems"])) == 33, "Incomplete theorem audit")
    for record in lean["axiom_reports"]:
        require(set(record["axioms"]) <= allowed, "Unexpected axiom")
    declared = []
    for path in sorted((ROOT / "lean/SharpMatrix").glob("*.lean")):
        declared += ["SharpMatrix." + name for name in re.findall(r"^theorem\s+(\w+)", path.read_text(encoding="utf-8"), re.MULTILINE)]
    require(set(declared) == set(lean["theorems"]), "Theorem list differs from the sources")
    python = read("results/python_run_status.json")
    require(python["status"] == "passed" and python["exact_check_count"] == 6866, "Python run did not pass")
    require(python["paper_reference"] == reference and python["manuscript_files_required"] is False, "Unexpected provenance")
    if args.archive_bytes:
        for entry in read("content_manifest.json")["files"]:
            path = ROOT / entry["path"]
            require(path.resolve().is_relative_to(ROOT.resolve()), "Unexpected manifest path")
            require(path.is_file() and path.stat().st_size == entry["bytes"] and sha(path) == entry["sha256"], "Archived bytes changed: " + entry["path"])
    print("Integrity passed: 33 Lean declarations, 6,866 exact checks and four searches; no manuscript files required.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
