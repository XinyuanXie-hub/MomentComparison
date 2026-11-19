module

public import MomentComparison.MomentNorm
public import Mathlib.Analysis.MeanInequalities
import all MomentComparison.Basic

public section

open scoped BigOperators

namespace Grokability

/-- Hölder's inequality for the bilinear pairing under uniform cube probability. -/
theorem norm_cubePair_le {n : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (f g : Cube n → ℂ) :
    ‖(∑ x, f x * g x) / (2 : ℂ) ^ n‖ ≤ complexMomentNorm p f * complexMomentNorm q g := by
  let N := (2 : ℝ) ^ n
  have hN : 0 < N := by dsimp [N]; positivity
  have hsum : ‖(∑ x, f x * g x) / (2 : ℂ) ^ n‖ ≤ (∑ x, ‖f x‖ * ‖g x‖) / N := by
    rw [norm_div, norm_pow]
    have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [htwo]
    apply div_le_div_of_nonneg_right _ hN.le
    simpa only [norm_mul] using
      (norm_sum_le (Finset.univ : Finset (Cube n)) (fun x => f x * g x))
  have hH := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun x => ‖f x‖) (g := fun x => ‖g x‖) hpq
    (fun x _ => norm_nonneg _) (fun x _ => norm_nonneg _)
  refine hsum.trans ((div_le_div_of_nonneg_right hH hN.le).trans_eq ?_)
  unfold complexMomentNorm cubeAverage
  rw [Real.div_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) hN.le,
    Real.div_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) hN.le,
    div_mul_div_comm, ← Real.rpow_add hN, hpq.inv_add_inv_eq_one, Real.rpow_one]
  simp only [one_div]

end Grokability
