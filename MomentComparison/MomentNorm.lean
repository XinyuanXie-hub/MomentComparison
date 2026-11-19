module

public import MomentComparison.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import all MomentComparison.Basic

public section

open scoped BigOperators

namespace MomentComparison

/-- The uniform probability moment norm on the cube. -/
@[expose] noncomputable def complexMomentNorm {n : ℕ} (p : ℝ) (f : Cube n → ℂ) : ℝ :=
  (cubeAverage fun x => ‖f x‖ ^ p) ^ p⁻¹

theorem cubeAverage_nonneg {n : ℕ} {f : Cube n → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ cubeAverage f :=
  div_nonneg (Finset.sum_nonneg fun x _ => hf x) (by positivity)

theorem cubeAverage_pos {n : ℕ} {f : Cube n → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hpos : ∃ x, 0 < f x) : 0 < cubeAverage f := by
  obtain ⟨x, hx⟩ := hpos
  exact div_pos (Finset.sum_pos' (fun x _ => hf x) ⟨x, Finset.mem_univ _, hx⟩)
    (by positivity)

theorem complexMomentNorm_nonneg {n : ℕ} (p : ℝ) (f : Cube n → ℂ) :
    0 ≤ complexMomentNorm p f :=
  Real.rpow_nonneg (cubeAverage_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) _

theorem complexMomentNorm_pos {n : ℕ} (p : ℝ) {f : Cube n → ℂ}
    (hf : ∃ x, f x ≠ 0) : 0 < complexMomentNorm p f := by
  obtain ⟨x, hx⟩ := hf
  exact Real.rpow_pos_of_pos (cubeAverage_pos
    (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    ⟨x, Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _⟩) _

/-- Log-convexity of the moments, in the power parameter. -/
theorem complexMoment_interpolate {n : ℕ} (f : Cube n → ℂ) {a b u : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < u) (hu' : u < 1) :
    cubeAverage (fun x => ‖f x‖ ^ ((1 - u) * a + u * b)) ≤
      cubeAverage (fun x => ‖f x‖ ^ a) ^ (1 - u) *
      cubeAverage (fun x => ‖f x‖ ^ b) ^ u := by
  let A : Cube n → ℝ := fun x => ‖f x‖ ^ a / (2 : ℝ) ^ n
  let B : Cube n → ℝ := fun x => ‖f x‖ ^ b / (2 : ℝ) ^ n
  have hA (x) : 0 ≤ A x := by dsimp [A]; positivity
  have hB (x) : 0 ≤ B x := by dsimp [B]; positivity
  have hconj : ((1 - u)⁻¹).HolderConjugate u⁻¹ :=
    Real.holderConjugate_iff.mpr
      ⟨(one_lt_inv₀ (by linarith)).mpr (by linarith), by simp⟩
  have hH := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun x => A x ^ (1 - u)) (g := fun x => B x ^ u) hconj
    (fun x _ => Real.rpow_nonneg (hA x) _) (fun x _ => Real.rpow_nonneg (hB x) _)
  have hA' (x) : (A x ^ (1 - u)) ^ (1 - u)⁻¹ = A x := by
    rw [← Real.rpow_mul (hA x), mul_inv_cancel₀ (by linarith : 1 - u ≠ 0), Real.rpow_one]
  have hB' (x) : (B x ^ u) ^ u⁻¹ = B x := by
    rw [← Real.rpow_mul (hB x), mul_inv_cancel₀ hu.ne', Real.rpow_one]
  simp only [hA', hB', one_div, inv_inv] at hH
  have hterm (x) :
      A x ^ (1 - u) * B x ^ u =
        ‖f x‖ ^ ((1 - u) * a + u * b) / (2 : ℝ) ^ n := by
    dsimp [A, B]
    have hN : 0 < (2 : ℝ) ^ n := by positivity
    rw [Real.div_rpow (Real.rpow_nonneg (norm_nonneg _) _) hN.le,
      Real.div_rpow (Real.rpow_nonneg (norm_nonneg _) _) hN.le,
      div_mul_div_comm, ← Real.rpow_add hN]
    rw [sub_add_cancel, Real.rpow_one,
      ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul (norm_nonneg _),
      ← Real.rpow_add_of_nonneg (norm_nonneg _) (mul_nonneg ha (by linarith))
        (mul_nonneg hb hu.le)]
    congr 2
    ring
  simpa only [hterm, A, B, ← Finset.sum_div, cubeAverage] using hH

/-- Interpolation between the first and `p`th norm on the cube. -/
theorem complexMomentNorm_interpolate {n : ℕ} (f : Cube n → ℂ) {p r u : ℝ}
    (hp : 0 < p) (hr : 0 < r) (hu : 0 < u) (hu' : u < 1)
    (heq : r = (1 - u) + u * p) :
    complexMomentNorm r f ≤
      complexMomentNorm 1 f ^ ((1 - u) / r) *
      complexMomentNorm p f ^ (u * p / r) := by
  have hleft := complexMoment_interpolate f (a := 1) (b := p)
    zero_le_one hp.le hu hu'
  rw [mul_one, ← heq] at hleft
  have h := Real.rpow_le_rpow (cubeAverage_nonneg fun _ =>
    Real.rpow_nonneg (norm_nonneg _) _) hleft (inv_nonneg.mpr hr.le)
  have ha : 0 ≤ cubeAverage (fun x => ‖f x‖ ^ (1 : ℝ)) :=
    cubeAverage_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  have hb : 0 ≤ cubeAverage (fun x => ‖f x‖ ^ p) :=
    cubeAverage_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  unfold complexMomentNorm
  rw [Real.mul_rpow (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _) ] at h
  rw [← Real.rpow_mul ha, ← Real.rpow_mul hb] at h
  rw [inv_one, Real.rpow_one, ← Real.rpow_mul hb]
  convert h using 2 <;> congr 1
  field_simp

end MomentComparison
