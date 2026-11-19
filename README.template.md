# {{PROJECT_TITLE}}

This project uses Lean to verify {{THEOREM_LABELS_AND_NUMBERS_FROM_THE_PAPERS}}.

> {{AUTHORS}}, *{{PAPER_TITLE}}*, [{{REFERENCE}}]({{PAPER_URL}}).

{{ADDITIONAL_PAPER_CITATIONS_IF_NEEDED}}

## Mathematical statements

<!-- Replace the placeholders with the papers’ original labels and numbers, wording, and mathematical notation. State only the definitions needed for the theorems. Use one block per theorem and identify its source when citing multiple papers. Remove this comment from the finished README. -->

{{DEFINITIONS_IN_THE_PAPERS_WORDING_AND_NOTATION}}

<a name="{{THEOREM_ANCHOR}}"></a>

**{{ORIGINAL_THEOREM_LABEL_AND_NUMBER}}.** {{ORIGINAL_THEOREM_STATEMENT}}

{{ADDITIONAL_THEOREM_BLOCKS_IF_NEEDED}}

## Verification

Check that the statements and definitions in [Challenge.lean](Challenge.lean) match the mathematical statements above and the cited sources. Then run:

```sh
bash scripts/verify-comparator.sh
```

This runs the full Comparator with Lean, NanoDa, and con-ron.

To inspect verification on GitHub:

1. Open this repository’s **Actions** tab and select the run for the commit being reviewed.
2. Open “Verify the Challenge against Solution”, then “Run Comparator with Lean, NanoDa, and con-ron”.
3. Check that the log reports acceptance by Lean, NanoDa, and con-ron, followed by `Your solution is okay!`.

Successful verification checks the recorded Lean statements and proofs; fidelity to the paper requires reviewing Challenge.lean.

See Lean's documentation on [validating proofs](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator) and [Comparator](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator).
