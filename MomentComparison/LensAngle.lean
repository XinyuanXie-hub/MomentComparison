module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

public section

namespace MomentComparison

/-- The angle in equation (191) in terms of the slope of the lens at its vertex. -/
theorem lensAngle_eq_four_arctan {p : ℝ} (hp : 2 < p) :
    2 * Real.arcsin (2 * Real.sqrt (p - 1) / p) =
      4 * Real.arctan (Real.sqrt (p - 1))⁻¹ := by
  let r := Real.sqrt (p - 1)
  have hsq : r ^ 2 = p - 1 := Real.sq_sqrt (by linarith)
  have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hr1 : 1 < r := (Real.lt_sqrt (by norm_num)).2 (by linarith)
  have hsin : Real.sin (2 * Real.arctan r⁻¹) = 2 * r / p := by
    rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    have hss := Real.sq_sqrt (x := 1 + r⁻¹ ^ 2) (by positivity)
    have hs : 0 < Real.sqrt (1 + r⁻¹ ^ 2) := Real.sqrt_pos.2 (by positivity)
    calc
      _ = (2 * r⁻¹) / (Real.sqrt (1 + r⁻¹ ^ 2) ^ 2) := by
        field_simp [hs.ne']
      _ = (2 * r⁻¹) / (1 + r⁻¹ ^ 2) := by rw [hss]
      _ = _ := by
        field_simp [hr.ne', show p ≠ 0 by linarith]
        nlinarith [congrArg (fun y : ℝ => r * y) hsq]
  have ha₀ : 0 ≤ Real.arctan r⁻¹ := Real.arctan_nonneg.2 (inv_nonneg.2 hr.le)
  have ha₁ : Real.arctan r⁻¹ < Real.pi / 4 := by
    rw [← Real.arctan_one]
    exact Real.arctan_strictMono (inv_lt_one_of_one_lt₀ hr1)
  have he := Real.arcsin_eq_of_sin_eq hsin
    ⟨by linarith [Real.pi_pos], by linarith⟩
  change 2 * Real.arcsin (2 * r / p) = 4 * Real.arctan r⁻¹
  rw [he]
  ring

/-- The aperture and boundary slope of the complex hypercontractivity lens. -/
theorem lensParameters {p : ℝ} (hp : 2 < p) :
    let r := Real.sqrt (p - 1)
    let β := (2 * Real.pi - 2 * Real.arcsin (2 * r / p)) / Real.pi
    let k := (p - 2) / (2 * r)
    0 < r ∧ r ^ 2 = p - 1 ∧ 0 < β ∧ β < 2 ∧
      Real.cos (β * Real.pi / 2) + k * Real.sin (β * Real.pi / 2) = 0 := by
  let r := Real.sqrt (p - 1)
  let a := Real.arcsin (2 * r / p)
  let β := (2 * Real.pi - 2 * a) / Real.pi
  let k := (p - 2) / (2 * r)
  have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hr2 : r ^ 2 = p - 1 := Real.sq_sqrt (by linarith)
  have hp0 : 0 < p := by linarith
  have hy0 : 0 < 2 * r / p := by positivity
  have hy1 : 2 * r / p < 1 := by
    apply (div_lt_one hp0).mpr
    have hs : (2 * r) ^ 2 < p ^ 2 := by
      nlinarith only [hr2, sq_pos_of_pos (show 0 < p - 2 by linarith)]
    nlinarith only [hs, hr, hp0]
  have ha0 : 0 < a := Real.arcsin_pos.mpr hy0
  have ha1 : a < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hy1
  refine ⟨hr, hr2, div_pos (by linarith [Real.pi_pos]) Real.pi_pos,
    (div_lt_iff₀ Real.pi_pos).mpr (by linarith), ?_⟩
  change Real.cos (β * Real.pi / 2) + k * Real.sin (β * Real.pi / 2) = 0
  have hβ : β * Real.pi / 2 = Real.pi - a := by
    dsimp [β]
    field_simp [Real.pi_ne_zero]
  have hc : Real.cos a = (p - 2) / p := by
    dsimp [a]
    rw [Real.cos_arcsin]
    refine (Real.sqrt_eq_iff_eq_sq (by nlinarith [sq_nonneg (2 * r / p)])
      (by positivity)).mpr ?_
    field_simp
    nlinarith [hr2]
  rw [hβ, Real.sin_pi_sub, Real.cos_pi_sub, hc, Real.sin_arcsin (by linarith) hy1.le]
  dsimp [k]
  field_simp [hp0.ne', hr.ne']
  ring

end MomentComparison
