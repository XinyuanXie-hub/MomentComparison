module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

public section

namespace Grokability

/-- Division subtracts principal arguments when the difference lies in the principal interval. -/
theorem arg_div_of_arg_sub {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hlo : -Real.pi < x.arg - y.arg) (hhi : x.arg - y.arg ≤ Real.pi) :
    (x / y).arg = x.arg - y.arg := by
  calc
    (x / y).arg = ((↑((x / y).arg)) : Real.Angle).toReal :=
      (Complex.arg_coe_angle_toReal_eq_arg _).symm
    _ = (((x.arg - y.arg : ℝ) : Real.Angle)).toReal := by
      rw [Complex.arg_div_coe_angle hx hy, Real.Angle.coe_sub]
    _ = x.arg - y.arg := Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr ⟨hlo, hhi⟩

/-- Principal complex powers distribute over division within a common branch. -/
theorem cpow_div_of_arg_sub {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hlo : -Real.pi < x.arg - y.arg) (hhi : x.arg - y.arg ≤ Real.pi) (b : ℂ) :
    (x / y) ^ b = x ^ b / y ^ b := by
  have hlog : Complex.log (x / y) = Complex.log x - Complex.log y := by
    apply Complex.ext
    · rw [Complex.log_re, Complex.sub_re, Complex.log_re, Complex.log_re, norm_div,
        Real.log_div (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)]
    · simpa only [Complex.sub_im, Complex.log_im] using arg_div_of_arg_sub hx hy hlo hhi
  simp only [Complex.cpow_def_of_ne_zero (div_ne_zero hx hy), Complex.cpow_def_of_ne_zero hx,
    Complex.cpow_def_of_ne_zero hy, hlog, sub_mul, Complex.exp_sub]

/-- Positive real powers scale the argument while it stays in its principal interval. -/
theorem arg_cpow_ofReal {z : ℂ} (hz : z ≠ 0) {b : ℝ}
    (hl : -Real.pi < z.arg * b) (hu : z.arg * b ≤ Real.pi) :
    (z ^ (b : ℂ)).arg = z.arg * b := by
  rw [Complex.cpow_def_of_ne_zero hz, Complex.arg_exp]
  simp [Complex.mul_im, Complex.log_im, toIocMod_eq_self Real.two_pi_pos (a := -Real.pi),
    show -Real.pi + 2 * Real.pi = Real.pi by ring, hl, hu]

end Grokability
