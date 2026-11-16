"""Reproduce all exact Python checks without the paper PDF or TeX source."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
PYTHON_DIR = ROOT / "python"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    started = datetime.now(timezone.utc).isoformat()
    reference = json.loads((ROOT / "paper_reference.json").read_text(encoding="utf-8"))
    jobs = [
        ("verify_examples.py", [], "finite_check_results.json", 1752),
        ("verify_period_formulas.py", [], "period_check_results.json", 177),
        ("verify_extended_formulas.py", [], "extended_check_results.json", 1027),
        ("verify_weighted_division.py", [], "weighted_division_results.json", 3910),
    ]
    for p, d, e, minimum in [(3, 2, 1, 7), (5, 2, 1, 11), (3, 3, 1, 19), (3, 3, 2, 7)]:
        jobs.append(("cyclotomic_search.py", ["--p", str(p), "--d", str(d), "--e", str(e)],
                     f"cyclotomic_search_p{p}_d{d}_e{e}.json", minimum))
    records = []
    for script, arguments, output, expected in jobs:
        command = [sys.executable, str(PYTHON_DIR / script), *arguments]
        result = subprocess.run(command, cwd=PYTHON_DIR, capture_output=True, text=True, encoding="utf-8")
        records.append({"script": script, "arguments": arguments, "exit_code": result.returncode,
                        "stdout": result.stdout, "stderr": result.stderr, "output": "python/" + output})
        if result.returncode != 0:
            print(result.stdout + result.stderr)
            raise RuntimeError(script + " failed")
        data = json.loads((PYTHON_DIR / output).read_text(encoding="utf-8"))
        if data.get("paper_reference") != reference or data.get("script_sha256") != sha(PYTHON_DIR / script):
            raise RuntimeError("Stale program or citation metadata: " + output)
        actual = data.get("minimum_dimension") if script == "cyclotomic_search.py" else data.get("check_count")
        if actual != expected or data.get("status", "passed") != "passed":
            raise RuntimeError("Unexpected result: " + output)
        print(script + " " + " ".join(arguments) + ": passed (" + str(actual) + ")", flush=True)
    summary = {"status": "passed", "started_utc": started,
               "finished_utc": datetime.now(timezone.utc).isoformat(), "python_version": sys.version,
               "paper_reference": reference, "manuscript_files_required": False,
               "exact_check_count": 6866, "exact_suite_counts": [1752, 177, 1027, 3910],
               "search_minima": [7, 11, 19, 7], "jobs": records}
    destination = ROOT / "results/python_run_status.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print("All 6,866 finite checks and four searches passed without manuscript files.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
