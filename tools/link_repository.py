"""Record the public repository URL and generate a software citation."""
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent


def main():
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python tools/link_repository.py https://github.com/OWNER/REPOSITORY")
    url = sys.argv[1].rstrip("/").removesuffix(".git")
    if not re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", url):
        raise SystemExit("Use the actual HTTPS URL of the created GitHub repository")
    cff = ROOT / "CITATION.cff"
    text = re.sub(r"^repository-code:.*\n?", "", cff.read_text(encoding="utf-8"), flags=re.MULTILINE)
    cff.write_text(text + 'repository-code: "' + url + '"\n', encoding="utf-8")
    citation = """# Software citation

Mohajer, M. (2026). *Lean 4 formalizations and exact Python checks for Sharp matrix tests and integral gluing over affine p-adic groups* (version 1.0.0) [Computer software]. REPOSITORY_URL

For the paper's bibliography:

```latex
\\bibitem{MohajerChecks2026}
M.~Mohajer,
\\emph{Lean 4 formalizations and exact Python checks for
Sharp matrix tests and integral gluing over affine $p$-adic groups},
version~1.0.0, 2026, computer software.
\\url{REPOSITORY_URL}.
```
""".replace("REPOSITORY_URL", url)
    (ROOT / "docs/CITATION.md").write_text(citation, encoding="utf-8")
    subprocess.run([sys.executable, str(ROOT / "tools/update_manifest.py")], check=True)
    print("Updated CITATION.cff and docs/CITATION.md; no manuscript files were read or changed.")


if __name__ == "__main__":
    main()
