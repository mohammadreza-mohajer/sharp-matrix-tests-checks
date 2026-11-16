# Publish the verification-only repository

Use repository name `sharp-matrix-tests-checks` and visibility **Public**.

Extract this archive and open its inner folder. Upload every item inside that folder, preserving the directory structure. Include names beginning with a dot: `.gitattributes`, `.gitignore`, and `.github/`. Put `README.md` directly at the GitHub repository root.

This package contains `python/`, not the earlier `manuscript/` directory. It includes no paper PDF, paper TeX source, journal class, cover letter, or submission notes. The original full package remains your private submission material.

Create an empty GitHub repository without generating another README or license, then upload these files. Once committed, the Actions tab will run the Python and Lean jobs. No hosted run is claimed in the supplied local records.

The archive contains only the public files, with no Git history. Initialize the new public repository from this extracted directory so the earlier private manuscript commits remain separate.

After the repository exists, run:

```text
python tools/link_repository.py https://github.com/OWNER/sharp-matrix-tests-checks
```

This command updates `CITATION.cff`, writes the actual software citation into `docs/CITATION.md`, and refreshes the content manifest. It reads no manuscript file. Commit and push those changes.

Use the generated software citation in the paper's bibliography and cite it from the appendix. The replacement appendix previously supplied for the journal submission remains suitable; it describes the code, formalizations, and outputs rather than requiring the paper to be hosted on GitHub.

When the hosted checks pass, a release named `v1.0.0` provides a stable software snapshot. The journal submission is a separate action.
