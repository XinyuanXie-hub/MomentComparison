# {{PROJECT_TITLE}}

This project uses Lean to verify {{RESULT_DESCRIPTION}}.

> {{AUTHORS}}, *{{PAPER_TITLE}}*, [{{REFERENCE}}]({{PAPER_URL}}).

{{ADDITIONAL_PAPER_CITATIONS_IF_NEEDED}}

## Mathematical statements

{{ONLY_THE_DEFINITIONS_NEEDED_FOR_THE_STATEMENTS}}

<a name="{{THEOREM_ANCHOR}}"></a>

**{{ORIGINAL_THEOREM_LABEL}}.** {{PRECISE_STATEMENT}}

{{ADD_FURTHER_STATEMENTS_WITH_THEIR_ORIGINAL_PAPER_NUMBERS}}

## Verification

Check that the statements and definitions in [Challenge.lean](Challenge.lean) match the mathematical statements above and the cited sources. Then run:

```sh
bash scripts/verify-comparator.sh
```

This runs the full Comparator with Lean, NanoDa, and con-ron.

To inspect verification on GitHub:

1. Open [Actions](https://github.com/{{OWNER}}/{{REPOSITORY}}/actions) and select the run for the commit being reviewed.
2. Open “Verify the Challenge against Solution”, then “Run Comparator with Lean, NanoDa, and con-ron”.
3. Confirm acceptance by all three checkers and successful completion of Comparator.

Successful verification checks the recorded Lean statements and proofs; fidelity to the paper requires reviewing Challenge.lean.

See Lean's documentation on [validating proofs](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator) and [Comparator](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator).
