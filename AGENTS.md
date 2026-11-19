# Formalization instructions

Please formalize the theorems requested by the user from the corresponding papers. Keep working until you return the verified repository described under [Output](#output).

## Initialization

1. **Fill in `Challenge.lean`.** When the user makes the request described in `README.md`, set up a new project with this repository’s files and directory structure. Use Lean’s module system in every Lean source file.

   In `Challenge.lean`, import only Mathlib or its submodules. Write the precise definitions the theorems depend on, then state each theorem with its number from the paper and a `by sorry` proof. In `comparator.json`, set only `theorem_names`, using the Lean theorem names including any namespaces.

   Run `lake build Challenge`, then ask the user to review `Challenge.lean` and wait for them to confirm it matches the requested theorems.

2. **Agree on the repository name.** After the user confirms `Challenge.lean`, suggest a repository name and wait for them to accept it or provide another. The final name must be valid on GitHub and as a Lean identifier.

## Formalization

Once the user chooses a name, rename `Template/` to that name and replace `name = "Template"` in its `[[lean_lib]]` entry in `lakefile.toml`. Write the proofs in the root `Solution.lean` and put supporting Lean files in the renamed folder, using the new library name in imports of those files.

### Strategy

Use the divide-and-conquer strategy for large proofs, giving sub-agents small pieces to work on in parallel. Expand compressed proofs and consult other papers as needed to formalize supporting theorems.

Use normal Lean compilation during development (`lake build Solution`). Run `bash scripts/verify-comparator.sh` only when the proofs are complete, and keep working until Lean, NanoDa, and con-ron accept `Solution.lean` against `Challenge.lean`.

### Constraints

Keep `lake-manifest.json`, `lean-toolchain`, `.gitignore`, `LICENSE`, `scripts/`, and `.github/` unchanged throughout. In `lakefile.toml`, change only the `Template` library name.

Keep the confirmed `Challenge.lean`, `comparator.json`, and the chosen repository name fixed. After the rename, edit only `Solution.lean` and Lean files in the renamed folder during proof development. Temporary Markdown notes are allowed.

## Output

After verification, ask for the formalization authors’ names. In `formalization.yaml`, use the repository name for `project.name` and the author names for both `project.authors` and `project.responsible_maintainers`. Fill the description with what the theorems establish, list the user’s papers in `sources`, and choose arXiv subject codes for `classification.arxiv`.

Generate `README.md` from `README.template.md`, keeping the theorem numbers from the papers. Return the repository with the approved `Challenge.lean`, verified `Solution.lean` and supporting Lean files, project configuration, and completed `README.md` and `formalization.yaml`. Leave out `README.template.md`, `AGENTS.md`, temporary notes, logs, caches, and intermediate files.
