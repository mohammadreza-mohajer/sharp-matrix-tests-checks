"""Hash the portable repository snapshot, excluding build and Git files."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SKIP_PARTS = {".git", ".lake", "__pycache__", ".venv"}
SKIP_SUFFIXES = {".olean", ".ilean", ".pyc", ".aux", ".log", ".out", ".zip"}
SKIP_NAMES = {"content_manifest.json", "Probe.lean", "failed_run.json"}


def release_files():
    return sorted(path for path in ROOT.rglob("*") if path.is_file()
                  and not set(path.relative_to(ROOT).parts) & SKIP_PARTS
                  and path.suffix not in SKIP_SUFFIXES
                  and path.name not in SKIP_NAMES
                  and not path.name.startswith("private_"))


def main():
    files = [{"path": path.relative_to(ROOT).as_posix(), "bytes": path.stat().st_size,
              "sha256": hashlib.sha256(path.read_bytes()).hexdigest()} for path in release_files()]
    payload = {"hash_algorithm": "SHA-256", "scope": "Portable release files, excluding this manifest itself and generated build/Git files.", "files": files}
    (ROOT / "content_manifest.json").write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print("Manifest updated for " + str(len(files)) + " files.")


if __name__ == "__main__":
    main()
