"""Public citation metadata; no manuscript file is needed by the checks."""
import json
from pathlib import Path


def paper_reference():
    reference = json.loads((Path(__file__).resolve().parent.parent / "paper_reference.json").read_text(encoding="utf-8"))
    if reference.get("manuscript_files_included") is not False:
        raise ValueError("Use the verification-only paper reference metadata")
    return reference
