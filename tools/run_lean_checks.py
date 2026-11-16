"""Compile all project modules and audit every theorem's logical dependencies."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"
OUTPUT = ROOT / "results" / "lean"
MODULES = ["WeightedDivision", "WeightedMatrix", "HermiteSmith", "Witness", "PeriodIdentities", "Sylvester"]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean-executable", help="Direct compiler mode for an existing pinned runtime and configured LEAN_PATH; default uses Lake.")
    args = parser.parse_args()
    started = datetime.now(timezone.utc).isoformat()
    OUTPUT.mkdir(parents=True, exist_ok=True)
    sources = ["SharpMatrix/" + name + ".lean" for name in MODULES] + ["SharpMatrix.lean", "Audit.lean"]
    declarations = []
    for source in sources:
        text = (LEAN / source).read_text(encoding="utf-8")
        if re.search(r"\b(?:sorry|admit|native_decide|unsafe)\b", re.sub(r"/-[\s\S]*?-/|--[^\n]*", "", text)):
            raise RuntimeError("Disallowed proof placeholder or trusted computation in " + source)
        if re.search(r"^\s*(?:axiom|opaque)\s", text, re.MULTILINE):
            raise RuntimeError("Additional axiom or opaque declaration in " + source)
        declarations += ["SharpMatrix." + name for name in re.findall(r"^theorem\s+(\w+)", text, re.MULTILINE)]
    logs = []

    def run(command, display):
        result = subprocess.run(command, cwd=LEAN, capture_output=True, text=True, encoding="utf-8")
        logs.append({"command": display, "exit_code": result.returncode,
                     "stdout": result.stdout, "stderr": result.stderr})
        if result.returncode:
            (OUTPUT / "failed_run.json").write_text(json.dumps(logs, indent=2), encoding="utf-8")
            print(result.stdout + result.stderr)
            raise RuntimeError("Compiler command failed: " + " ".join(display))
        return result.stdout + result.stderr

    prefix = [args.lean_executable] if args.lean_executable else ["lake", "env", "lean"]
    version = run(prefix + ["--version"], ["lean", "--version"])
    if not re.search(r"version 4\.19\.0(?:,|\s)", version):
        raise RuntimeError("Use the pinned Lean 4.19.0 toolchain")
    if args.lean_executable:
        for source in sources[:-1]:
            output = source.removesuffix(".lean") + ".olean"
            run(prefix + ["-o", output, source], ["lean", "-o", output, source])
            print(source + ": compiler passed", flush=True)
    else:
        run(["lake", "build"], ["lake", "build"])
    axiom_output = run(prefix + ["Audit.lean"], ["lean", "Audit.lean"])
    reports = re.findall(r"'([^']+)' (does not depend on any axioms|depends on axioms:\s*\[[^\]]*\])", axiom_output)
    report_names = [name for name, _ in reports]
    if set(report_names) != set(declarations) or len(report_names) != len(declarations):
        raise RuntimeError("Axiom audit does not cover exactly every theorem")
    parsed = []
    for name, report in reports:
        dependencies = [] if report.startswith("does not") else [item.strip() for item in report.split("[", 1)[1].rsplit("]", 1)[0].split(",") if item.strip()]
        if not set(dependencies) <= ALLOWED_AXIOMS:
            raise RuntimeError("Unexpected axiom dependency in " + name + ": " + repr(dependencies))
        parsed.append({"theorem": name, "axioms": dependencies})
    (OUTPUT / "version.txt").write_text(version, encoding="utf-8")
    (OUTPUT / "axioms.txt").write_text(axiom_output, encoding="utf-8")
    (OUTPUT / "build_output.txt").write_text("\n".join("$ " + " ".join(job["command"]) + "\n" + job["stdout"] + job["stderr"] for job in logs), encoding="utf-8")
    manifest = json.loads((LEAN / "lake-manifest.json").read_text(encoding="utf-8"))
    summary = {
        "status": "passed", "started_utc": started, "finished_utc": datetime.now(timezone.utc).isoformat(),
        "execution_mode": "direct pinned compiler with prebuilt pinned Mathlib dependencies" if args.lean_executable else "Lake build and compiler audit",
        "lean_version": version.strip(),
        "mathlib_revision": next(package["rev"] for package in manifest["packages"] if package["name"] == "mathlib"),
        "source_sha256": {source: digest(LEAN / source) for source in sources},
        "configuration_sha256": {name: digest(LEAN / name) for name in ["lakefile.toml", "lake-manifest.json", "lean-toolchain"]},
        "theorem_count": len(declarations), "theorems": declarations,
        "axiom_reports": parsed, "allowed_standard_axioms": sorted(ALLOWED_AXIOMS),
        "proof_placeholders": False, "additional_axioms": False, "native_decide_used": False,
        "scope": "The selected statements in docs/FORMALIZATION_SCOPE.md; the full analytic and arithmetic constructions are not asserted to be formalized.",
    }
    (OUTPUT / "status.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(str(len(declarations)) + " Lean theorem declarations compiled and passed the axiom audit.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
