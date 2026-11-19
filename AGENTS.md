# Formalization instructions

Please formalize the theorems requested by the user from the corresponding papers. Keep working until you return the verified repository described under [Output](#output).

## Initialization

Set up a new project with this repository’s files and directory structure. Use Lean’s module system in every Lean source file. In `Challenge.lean`, import only Mathlib or its submodules. Write the precise definitions needed to state the theorems the user wants to formalize. Then state each theorem in Lean in `Challenge.lean` exactly as it is stated in the paper, keeping its label and number, and give it a `by sorry` proof. Set `theorem_names` in `comparator.json` to the corresponding Lean theorem names, including any namespaces, and leave the other fields unchanged.

Run `lake build Challenge`, then ask the user to review `Challenge.lean` and confirm it matches the theorems they want. Once they confirm it, keep `Challenge.lean` and `comparator.json` fixed for the rest of the task. Then suggest a repository name and wait for the user to accept it or provide another. The final name must be valid on GitHub and as a Lean identifier.

## Formalization

Once the user chooses a repository name, rename `Template/` to that name. In `lakefile.toml`, replace only `name = "Template"` in the corresponding `[[lean_lib]]` entry with the chosen name, then keep `lakefile.toml` unchanged. Find a `Solution.lean` that passes Comparator against `Challenge.lean`, with all supporting Lean files in the renamed folder and imports that use their new module names.

### Strategy

Use the divide-and-conquer strategy for large proofs, giving sub-agents small pieces to work on in parallel. Expand mathematical proofs that are too compressed to translate into Lean, and download other papers as needed to formalize the results those proofs rely on. When a proof depends on a result not already available in the pinned libraries, formalize that result and its prerequisites, and keep working until `lake build Solution` succeeds and `bash scripts/verify-comparator.sh` passes against the unchanged, user-approved `Challenge.lean` and `comparator.json`, without adding axioms or leaving proof gaps.

Use normal Lean compilation during development (`lake build Solution`). Run `bash scripts/verify-comparator.sh` only when the proofs are complete, and keep working until Lean, NanoDa, and con-ron accept the solution.

### Constraints

Keep `lake-manifest.json`, `lean-toolchain`, `.gitignore`, `LICENSE`, `scripts/`, and `.github/` unchanged throughout.

Keep the confirmed `Challenge.lean`, `comparator.json`, and the chosen repository name fixed. After the rename, edit only `Solution.lean` and Lean files in the renamed folder during proof development. Temporary Markdown notes are allowed.

## Output

After verification, generate `README.md` from `README.template.md`. Name the formalized theorems by their original labels and numbers in the opening paragraph, and use the papers’ wording and notation for the definitions and statements. In the template’s Verification section, use “theorem” and “statement” for one formalized result and “theorems” and “statements” for more than one. Replace `{{VERIFIED_THEOREM_LINKS}}` with links to every formalized statement above, using each result’s original label and number, and check that each link opens the correct statement. Keep the rest of the Verification section unchanged. Preview `README.md` using GitHub’s Markdown renderer and check that every formula displays correctly.

Then ask for the formalization authors’ names. In `formalization.yaml`, use the repository name for `project.name` and the author names for both `project.authors` and `project.responsible_maintainers`. Fill the description with what the theorems establish, list the user’s papers in `sources`, and choose arXiv subject codes for `classification.arxiv`. Fill only the placeholders in `formalization.yaml`. Keep all other fields and wording unchanged, including the entire `automation` and `review` sections. Do not add project-specific notes there.

Return the repository with the approved `Challenge.lean`, verified `Solution.lean` and supporting Lean files, project configuration, and completed `README.md` and `formalization.yaml`. Leave out `README.template.md`, `AGENTS.md`, temporary notes, logs, caches, and intermediate files.
