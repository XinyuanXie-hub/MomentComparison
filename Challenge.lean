module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

open scoped BigOperators

namespace Grokability

/-- The Hamming cube, with `true` representing 1 and `false` representing −1. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- Expectation under the uniform distribution on the Hamming cube. -/
noncomputable def cubeAverage {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  (∑ x, f x) / (2 : ℝ) ^ n

/-- The Fourier–Walsh coefficients above degree `d` vanish. -/
def HasDegreeLE {n : ℕ} (f : Cube n → ℝ) (d : ℕ) : Prop :=
  ∀ s : Finset (Fin n), d < s.card →
    cubeAverage (fun x => f x * ∏ i ∈ s, if x i then 1 else -1) = 0

/-- The infimum of the positive bases for which ‖f‖₂ ≤ C^d ‖f‖₁. -/
noncomputable def Cstar : ℝ :=
  sInf {C : ℝ | 0 < C ∧
    ∀ (n d : ℕ), 0 < n → 0 < d → ∀ f : Cube n → ℝ, HasDegreeLE f d →
      Real.sqrt (cubeAverage fun x => f x ^ 2) ≤ C ^ d * cubeAverage (fun x => |f x|)}

/-- The constant denoted by `2.408…`, given by equation (191) of
Eskenazis–Ivanisvili. Complex powers use the principal branch. -/
noncomputable def upperBase : ℝ :=
  sInf ((fun p : ℝ =>
    let r := Real.sqrt (p - 1)
    let θ := 2 * Real.arcsin (2 * r / p)
    let α : ℂ := (Real.pi / (2 * Real.pi - θ) : ℝ)
    let z := Complex.I * (r : ℂ)
    let a := (z - 1) ^ α
    let b := (z + 1) ^ α
    ‖(a + b) / (a - b)‖ ^ (p / (2 * (p - 2)))) '' Set.Ioi 2)

/-- Theorem 2 of Ivanisvili–Xie, *Grokability in five inequalities*. -/
theorem theorem2 : Real.sqrt 3 ≤ Cstar ∧ Cstar ≤ upperBase := by
  sorry

end Grokability
