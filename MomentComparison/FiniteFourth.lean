module

public import MomentComparison.Counting
public import MomentComparison.Walsh
import all MomentComparison.Basic

public section

open scoped BigOperators
open Finset

namespace Grokability

/-- The contribution of symmetric differences of size (2k) to the fourth moment. -/
theorem finite_fourth_ge (n m k : ℕ) (hkm : k ≤ m) :
    (n.choose (2 * k) : ℝ) * ((2 * k).choose k : ℝ) ^ 2 *
      ((n - 2 * k).choose (m - k) : ℝ) ^ 2 ≤
      cubeAverage (fun x => walshLayer n m x ^ 4) := by
  let supports := (univ : Finset (Fin n)).powersetCard (2 * k)
  let pairs := ((2 * k).choose k : ℝ) * ((n - 2 * k).choose (m - k) : ℝ)
  rw [cubeAverage_walshLayer_fourth]
  calc
    _ = ∑ _T ∈ supports, pairs ^ 2 := by
      simp only [sum_const, nsmul_eq_mul, supports, card_powersetCard, card_univ,
        Fintype.card_fin, pairs, mul_pow, mul_assoc]
    _ ≤ ∑ T ∈ supports, (walshPairCount n m T : ℝ) ^ 2 := by
      apply sum_le_sum
      intro T hT
      have hsize := (mem_powersetCard.mp hT).2
      have hcount := pair_count_ge m k hkm T hsize
      rw [Fintype.card_fin] at hcount
      apply pow_le_pow_left₀ (by dsimp [pairs]; positivity) _ 2
      change pairs ≤ (walshPairCount n m T : ℝ)
      dsimp [pairs, walshPairCount]
      exact_mod_cast hcount
    _ ≤ ∑ T : Finset (Fin n), (walshPairCount n m T : ℝ) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ supports) (fun _ _ _ => sq_nonneg _)

end Grokability
