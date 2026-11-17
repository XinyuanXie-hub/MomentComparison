# {{PROJECT_TITLE}}

This project uses Lean to verify {{RESULT_DESCRIPTION}}, from the paper cited below.

> {{AUTHORS}}, *{{PAPER_TITLE}}*, [{{REFERENCE}}]({{PAPER_URL}}).

## Mathematical statements

{{ONLY_THE_DEFINITIONS_NEEDED_FOR_THE_STATEMENTS}}

<a name="theorem-1"></a>

**Theorem 1.** {{PRECISE_STATEMENT}}

{{ADD_FURTHER_STATEMENTS_NUMBERED_2_3_AND_SO_ON}}

## Verification

Check that the statements and definitions in [Challenge.lean](Challenge.lean) match the mathematical statements above and the cited paper. Then run:

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
