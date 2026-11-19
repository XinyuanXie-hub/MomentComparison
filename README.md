# Moment Comparison

This project uses Lean to verify Theorem 2 of Ivanisvili and Xie.

> Paata Ivanisvili and Xinyuan Xie, *Grokability in five inequalities*, [arXiv:2605.05193v1](https://arxiv.org/abs/2605.05193v1).

## Mathematical statements

For a function $`f:\{-1,1\}^n\to\mathbb{R}`$, define its moments with respect to the uniform probability measure by

```math
\|f\|_p = \left(2^{-n}\sum_{x\in\{-1,1\}^n}|f(x)|^p\right)^{1/p}.
```

Write $`\deg f`$ for the degree of the Fourier–Walsh expansion of $f$. The optimal exponential base in the $L_2$–$L_1$ moment comparison is

```math
C_\ast = \inf\left\{ C>0 :
  \|f\|_2 \le C^d\|f\|_1\ \text{for every } n,d\ge 1
  \text{ and every } f:\{-1,1\}^n\to\mathbb{R} \text{ with } \deg f\le d
\right\}.
```

The upper bound $2.408\ldots$ denotes the exact constant defined by Eskenazis and Ivanisvili in [equation (191)](https://arxiv.org/html/1902.02406#S5.E191).

<a name="theorem-2"></a>

**Theorem 2.** One has

```math
2.408\ldots \ge C_\ast \ge \sqrt{3}.
```

## Verification

To verify the correctness of the theorem in Lean, one only needs to check that the statement and definitions in [Challenge.lean](Challenge.lean) match [Theorem 2](#theorem-2) stated above, and confirm that `lake comparator` succeeds.

The results of `lake comparator` can be checked through the GitHub workflow provided by this project as follows:

1. Sign in to GitHub, open the “Actions” tab, then open the first workflow run listed there.
2. Click “Verify the Challenge against Solution”, then expand “Run Comparator with Lean, NanoDa, and con-ron”.
3. Check that the log (lines 198–203) reports acceptance by con-ron, NanoDa, and Lean, followed by `Your solution is okay!`.


Note: Here, we use the [“gold standard”](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator) for validating proofs in Lean, and we refer readers to [“Challenges and External Checkers”](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator) for details on how it works.
