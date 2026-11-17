# Lean verification template

A template for formalizing theorems from a paper in Lean.

Follow [AGENTS.md](AGENTS.md) for setup, challenge approval, proof development, verification, and preparation of the finished repository.

`Challenge.lean` contains the statements to review. `Solution.lean` proves those statements independently, with supporting proof modules in `LeanVerificationTemplate/`. External dependencies are declared in `lakefile.toml` and pinned in `lake-manifest.json`.

The final check uses `bash scripts/verify-comparator.sh` to run Comparator with Lean, NanoDa, and con-ron. The empty template has no theorem targets and is not a verified formalization.

Use [README.template.md](README.template.md) to write the finished project's README, then remove that template file from the output.
