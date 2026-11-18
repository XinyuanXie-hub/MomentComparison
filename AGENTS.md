# Formalization instructions

Please formalize the theorems requested by the user from the corresponding papers. Please keep working until you return a ready-to-publish GitHub repository according to the procedure below.

1. **Initialization.** Set up a formalization project using the same files and directory structure as this GitHub repository. Use Lean’s module system in every Lean source file.

   In `Challenge.lean`, import only Mathlib or its submodules. First write the precise definitions the requested theorems depend on, then state the theorems. Use the same theorem numbers as in the papers and give each theorem a `by sorry` proof. Fill in `theorem_names` in `comparator.json`, keeping the other fields fixed, and compile `Challenge.lean`.

   Ask the user to review and approve `Challenge.lean` and a suggested repository name.

2. **Formalization.** Once approved, find a `Solution.lean` that passes the comparator check against `Challenge.lean`, with any supporting Lean files in `Template/`.

   Use the divide-and-conquer strategy for large proofs: split the proof into small pieces so that you can generate many sub-agents working in parallel. Expand proofs that are too compressed to translate into Lean. Retrieve other papers as needed and formalize the supporting theorems the proof relies on. You may use temporary Markdown notes to share expanded proofs with other agents.

   Keep `Challenge.lean`, `comparator.json`, the repository name, and the files listed under **Constants** unchanged. Change only `Solution.lean` and the Lean files in `Template/`.

   Use normal Lean compilation during development. Run `bash scripts/verify-comparator.sh` only when the proofs are complete, and keep working until Lean, NanoDa, and con-ron accept the solution.

After formalization, ask the user for the names of the formalization authors. In `formalization.yaml`, enter the approved repository name as `project.name` and put the author names in both `project.authors` and `project.responsible_maintainers`. Complete the description with what the theorems establish, using “Verification that …, as shown in the source.” Use the papers provided by the user for `sources`, and choose the arXiv subject codes for the mathematics.

Generate `README.md` from `README.template.md`, keeping the original theorem numbering from the papers. Return the verified repository without `README.template.md`, `AGENTS.md`, temporary notes, logs, caches, or intermediate files.

## System specification

This section is for humans to check what goes into this agentic workflow, what output to expect, and what constraints apply.

**Input:** The user will provide the theorem(s) to formalize from given paper(s).

**Interactions:** The agent will ask the user to accept a suggested repository name and review `Challenge.lean`, if approved, the agent will keep working until `Solution.lean` passes the comparator check. After formalization, the agent will ask for the names of the formalization authors.

**Output:** A ready-to-publish GitHub repository for submission to Palomar, containing `Challenge.lean`, `Solution.lean`, supporting files, `comparator.json`, `README.md`, and `formalization.yaml`.

**Constraints:**

- **Constants:** `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `scripts/`, `.github/`, `.gitignore`, and `LICENSE`.
- **Setup:** Repository name, `Challenge.lean`, and theorem names in `comparator.json`. Every import in `Challenge.lean` must be from Mathlib or its submodules.
- **Formalization:** `Solution.lean` and supporting Lean files in `Template/`. Temporary Markdown notes are allowed during development.
- **Finally:** Fill in `formalization.yaml`. Update `README.md` as in `README.template.md`, then remove `README.template.md`, `AGENTS.md`, and temporary notes from the output.
