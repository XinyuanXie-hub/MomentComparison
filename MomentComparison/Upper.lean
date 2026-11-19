module

public import MomentComparison.Pairing
public import MomentComparison.Conformal
public import MomentComparison.Hypercontractivity
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Basic.Real.ConjExponents
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import all MomentComparison.Basic

public section

open scoped BigOperators

namespace Grokability

private theorem complexMomentNorm_real_one {n : ℕ} (f : Cube n → ℝ) :
    complexMomentNorm 1 (fun x => (f x : ℂ)) = cubeAverage (fun x => |f x|) := by
  simp only [complexMomentNorm, inv_one, Real.rpow_one, Complex.norm_real, Real.norm_eq_abs]

private theorem complexMomentNorm_real_two {n : ℕ} (f : Cube n → ℝ) :
    complexMomentNorm 2 (fun x => (f x : ℂ)) = Real.sqrt (cubeAverage fun x => f x ^ 2) := by
  simp only [complexMomentNorm, Real.rpow_two, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, Real.sqrt_eq_rpow, one_div]

/-- Hölder’s inequality in the form used in the moment comparison proof. -/
private theorem complexMomentNorm_interpolate' {n : ℕ} (f : Cube n → ℂ)
    {p r : ℝ} (hr1 : 1 < r) (hrp : r < p) :
    complexMomentNorm r f ≤
      complexMomentNorm 1 f ^ (1 - p * (r - 1) / (r * (p - 1))) *
      complexMomentNorm p f ^ (p * (r - 1) / (r * (p - 1))) := by
  have hp1 : 1 < p := hr1.trans hrp
  have hr : 0 < r := by linarith
  have hp : 0 < p := by linarith
  have hpm : 0 < p - 1 := sub_pos.mpr hp1
  let u := (r - 1) / (p - 1)
  have hu : 0 < u := div_pos (sub_pos.mpr hr1) hpm
  have hu' : u < 1 := (div_lt_one hpm).mpr (by linarith)
  have heq : r = (1 - u) + u * p := by
    dsimp [u]
    field_simp
    ring
  have h := complexMomentNorm_interpolate f hp hr hu hu' heq
  have hb : u * p / r = p * (r - 1) / (r * (p - 1)) := by
    dsimp [u]
    field_simp
  have ha : (1 - u) / r = 1 - p * (r - 1) / (r * (p - 1)) := by
    rw [← hb]
    apply (div_eq_iff hr.ne').mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hr.ne', heq]
    ring
  rwa [ha, hb] at h

/-- A reverse comparison between conjugate exponents yields a bound at `(2, 1)`. -/
theorem moment_comparison_of_conjugate {n d : ℕ} {p L : ℝ} (hp : 2 < p)
    (hL : 0 < L) (f : Cube n → ℝ)
    (hReverse : complexMomentNorm p (fun x => (f x : ℂ)) ≤
      L ^ d * complexMomentNorm (p / (p - 1)) (fun x => (f x : ℂ))) :
    Real.sqrt (cubeAverage fun x => f x ^ 2) ≤
      (L ^ (p / (2 * (p - 2)))) ^ d * cubeAverage (fun x => |f x|) := by
  let g : Cube n → ℂ := fun x => f x
  by_cases hg : ∃ x, g x ≠ 0
  · have hp1 : 1 < p := by linarith
    have hppos : 0 < p := by linarith
    have hpm1 : 0 < p - 1 := by linarith
    have hpm2 : 0 < p - 2 := by linarith
    let q := p / (p - 1)
    have hq1 : 1 < q := (lt_div_iff₀ hpm1).mpr (by linarith)
    have hqp : q < p := by
      apply (div_lt_iff₀ hpm1).mpr
      nlinarith [mul_pos hppos hpm2]
    let b := p / (2 * (p - 1))
    let c := 1 / (p - 1)
    let e := p / (2 * (p - 2))
    have hb : 0 < b := by dsimp [b]; positivity
    have hc : 0 < 1 - c := by
      dsimp [c]
      apply sub_pos.mpr
      exact (div_lt_one hpm1).mpr (by linarith)
    have he : 0 < e := by dsimp [e]; positivity
    have heq : e * (1 - c) = b := by
      dsimp [e, c, b]
      field_simp
      ring
    have h2 := complexMomentNorm_interpolate' g (r := 2) (p := p) (by norm_num) hp
    have hq := complexMomentNorm_interpolate' g hq1 hqp
    have hb' : p * ((2 : ℝ) - 1) / (2 * (p - 1)) = b := by norm_num [b]
    have hc' : p * (q - 1) / (q * (p - 1)) = c := by
      dsimp [q, c]
      field_simp
      ring
    rw [hb'] at h2
    rw [hc'] at hq
    have hA : 0 < complexMomentNorm 1 g := complexMomentNorm_pos _ hg
    have hB : 0 < complexMomentNorm p g := complexMomentNorm_pos _ hg
    have hTwo : 0 < complexMomentNorm 2 g := complexMomentNorm_pos _ hg
    have hQ : 0 < complexMomentNorm q g := complexMomentNorm_pos _ hg
    have h2Log := Real.log_le_log hTwo h2
    have hqLog := Real.log_le_log hQ hq
    have hReverseLog := Real.log_le_log hB hReverse
    change Real.log (complexMomentNorm p g) ≤ Real.log (L ^ d * complexMomentNorm q g)
      at hReverseLog
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hA _))
      (ne_of_gt (Real.rpow_pos_of_pos hB _)), Real.log_rpow hA, Real.log_rpow hB] at h2Log hqLog
    rw [Real.log_mul (pow_ne_zero _ hL.ne') hQ.ne', Real.log_pow] at hReverseLog
    have hGap : (1 - c) * (Real.log (complexMomentNorm p g) -
        Real.log (complexMomentNorm 1 g)) ≤ d * Real.log L := by
      linarith
    have hScaled := mul_le_mul_of_nonneg_left hGap he.le
    rw [← mul_assoc, heq] at hScaled
    have hFinal : Real.log (complexMomentNorm 2 g) ≤
        (d : ℝ) * (e * Real.log L) + Real.log (complexMomentNorm 1 g) := by
      linarith
    rw [← complexMomentNorm_real_one, ← complexMomentNorm_real_two]
    apply (Real.log_le_log_iff hTwo (mul_pos (pow_pos (Real.rpow_pos_of_pos hL _) _) hA)).mp
    rw [Real.log_mul (pow_ne_zero _ (Real.rpow_pos_of_pos hL e).ne') hA.ne',
      Real.log_pow, Real.log_rpow hL]
    simpa only [smul_eq_mul, mul_comm e (Real.log L)] using hFinal
  · push Not at hg
    have hf : f = 0 := by
      funext x
      exact Complex.ofReal_eq_zero.1 (hg x)
    simp [hf, cubeAverage]

/-- Reduces the upper bound to a uniform reverse comparison for conjugate exponents. -/
theorem cstar_le_inf_of_reverse {L : ℝ → ℝ}
    (hL : ∀ p, 2 < p → 0 < L p)
    (hReverse : ∀ p, 2 < p → ∀ {n d : ℕ} (f : Cube n → ℝ), HasDegreeLE f d →
      complexMomentNorm p (fun x => (f x : ℂ)) ≤
        L p ^ d * complexMomentNorm (p / (p - 1)) (fun x => (f x : ℂ))) :
    Cstar ≤ sInf ((fun p => L p ^ (p / (2 * (p - 2)))) '' Set.Ioi 2) := by
  refine le_csInf ⟨L 3 ^ ((3 : ℝ) / (2 * (3 - 2))), 3, by norm_num, rfl⟩ ?_
  rintro _ ⟨p, hp, rfl⟩
  have hp' : 2 < p := hp
  have hLp := hL p hp'
  apply csInf_le ⟨0, fun _ h => h.1.le⟩
  refine ⟨Real.rpow_pos_of_pos hLp _, ?_⟩
  intro n d hn hd f hf
  exact moment_comparison_of_conjugate hp' hLp f (hReverse p hp' f hf)

/-- A bound on every scalar pairing implies the corresponding moment norm bound.
For real functions the dual witness is `x ↦ f x * |f x|^(p - 2)`. -/
theorem realMomentNorm_le_of_pairing {n : ℕ} {p q M : ℝ} (hp : 2 < p)
    (hpq : p.HolderConjugate q) (hM : 0 ≤ M) (f : Cube n → ℝ)
    (hbound : ∀ g : Cube n → ℂ,
      ‖(∑ x, (f x : ℂ) * g x) / (2 : ℂ) ^ n‖ ≤ M * complexMomentNorm q g) :
    complexMomentNorm p (fun x => (f x : ℂ)) ≤ M := by
  let g : Cube n → ℂ := fun x => (f x * |f x| ^ (p - 2) : ℝ)
  let A := cubeAverage fun x => |f x| ^ p
  have hp0 : p ≠ 0 := by linarith
  have hp2 : 0 ≤ p - 2 := by linarith
  have hA : 0 ≤ A := cubeAverage_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
  have hnorm : complexMomentNorm p (fun x => (f x : ℂ)) = A ^ p⁻¹ := by
    simp only [A, complexMomentNorm, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  by_cases hA0 : A = 0
  · rw [hA0, Real.zero_rpow (inv_ne_zero hp0)]
    exact hM
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  have hg (x) : ‖g x‖ = |f x| ^ (p - 1) := by
    unfold g
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    calc
      |f x| * |f x| ^ (p - 2) = |f x| ^ (1 : ℝ) * |f x| ^ (p - 2) := by
        rw [Real.rpow_one]
      _ = |f x| ^ (1 + (p - 2)) := by
        rw [Real.rpow_add_of_nonneg (abs_nonneg _) zero_le_one hp2]
      _ = |f x| ^ (p - 1) := by congr 1; ring
  have hg' (x) : ‖g x‖ ^ q = |f x| ^ p := by
    rw [hg, ← Real.rpow_mul (abs_nonneg _), hpq.sub_one_mul_conj]
  have hgNorm : complexMomentNorm q g = A ^ q⁻¹ := by
    simp only [complexMomentNorm, A, hg']
  have hterm (x) : (f x : ℂ) * g x = ((|f x| ^ p : ℝ) : ℂ) := by
    unfold g
    rw [← Complex.ofReal_mul]
    congr 1
    have hrpow2 : f x * f x = |f x| ^ (2 : ℝ) := by
      rw [Real.rpow_two, sq_abs, pow_two]
    rw [← mul_assoc, hrpow2, ← Real.rpow_add_of_nonneg (abs_nonneg _) (by norm_num) hp2]
    congr 1
    ring
  have hpair : (∑ x, (f x : ℂ) * g x) / (2 : ℂ) ^ n = (A : ℂ) := by
    simp only [hterm, A, cubeAverage, Complex.ofReal_div, Complex.ofReal_sum,
      Complex.ofReal_pow, Complex.ofReal_ofNat]
  have h := hbound g
  rw [hpair, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA, hgNorm] at h
  refine le_of_mul_le_mul_right ?_ (Real.rpow_pos_of_pos hApos q⁻¹)
  rwa [← Real.rpow_add hApos, hpq.inv_add_inv_eq_one, Real.rpow_one]

/-- Polynomial growth transfers a contraction on a complex set to a
reverse moment comparison at the point `1`. -/
theorem reverse_moment_comparison_of_polynomial_growth
    {n d : ℕ} {p q L : ℝ} (hp : 2 < p) (hpq : p.HolderConjugate q) (hL : 0 ≤ L)
    {V : Set ℂ} (f : Cube n → ℝ) (F : ℂ → Cube n → ℂ)
    (hFone : ∀ x, F 1 x = (f x : ℂ))
    (hcontract : ∀ w ∈ V, complexMomentNorm p (F w) ≤
      complexMomentNorm q (fun x => (f x : ℂ)))
    (hpoly : ∀ g : Cube n → ℂ, ∃ P : Polynomial ℂ, P.natDegree ≤ d ∧
      ∀ w, P.eval w = (∑ x, F w x * g x) / (2 : ℂ) ^ n)
    (hgrowth : ∀ (P : Polynomial ℂ), P.natDegree ≤ d → ∀ M : ℝ, 0 ≤ M →
      (∀ w ∈ V, ‖P.eval w‖ ≤ M) → ‖P.eval 1‖ ≤ L ^ d * M) :
    complexMomentNorm p (fun x => (f x : ℂ)) ≤
      L ^ d * complexMomentNorm q (fun x => (f x : ℂ)) := by
  let M := complexMomentNorm q (fun x => (f x : ℂ))
  have hM : 0 ≤ M := complexMomentNorm_nonneg _ _
  apply realMomentNorm_le_of_pairing hp hpq (mul_nonneg (pow_nonneg hL _) hM) f
  intro g
  obtain ⟨P, hdeg, heval⟩ := hpoly g
  have hnorm := complexMomentNorm_nonneg q g
  have hV (w) (hw : w ∈ V) : ‖P.eval w‖ ≤ M * complexMomentNorm q g := by
    rw [heval]
    exact (norm_cubePair_le hpq (F w) g).trans
      (mul_le_mul_of_nonneg_right (hcontract w hw) hnorm)
  have h := hgrowth P hdeg _ (mul_nonneg hM hnorm) hV
  rw [heval, ← mul_assoc] at h
  simpa only [hFone] using h

/-- The upper bound follows from complex hypercontractivity and scalar polynomial
growth for the lens of conjugate exponents. -/
theorem cstar_le_upperBase_of_estimates
    (hHyper : ∀ p : ℝ, 2 < p → ∀ (n : ℕ) (f : Cube n → ℂ) (w : ℂ),
      inLens p w → complexMomentNorm p (complexNoise w f) ≤
        complexMomentNorm (p / (p - 1)) f)
    (hGrowth : ∀ p : ℝ, 2 < p → ∀ (d : ℕ) (P : Polynomial ℂ), P.natDegree ≤ d →
      ∀ M : ℝ, 0 ≤ M → (∀ w, inLens p w → ‖P.eval w‖ ≤ M) →
        ‖P.eval 1‖ ≤ lensFactor p ^ d * M) :
    Cstar ≤ upperBase := by
  change Cstar ≤ sInf ((fun p => lensFactor p ^ (p / (2 * (p - 2)))) '' Set.Ioi 2)
  apply cstar_le_inf_of_reverse
  · intro p hp
    have h := hGrowth p hp 1 1 (by simp) 1 zero_le_one (by simp)
    have h' : 1 ≤ lensFactor p := by simpa using h
    exact zero_lt_one.trans_le h'
  · intro p hp n d f hf
    have hpq : p.HolderConjugate (p / (p - 1)) :=
      (Real.holderConjugate_iff_eq_conjExponent (by linarith)).mpr rfl
    exact reverse_moment_comparison_of_polynomial_growth hp hpq (norm_nonneg _)
      (V := {w | inLens p w}) f (fun w => complexNoise w (fun x => (f x : ℂ)))
      (complexNoise_one_ofReal f) (hHyper p hp n _)
      (exists_noise_polynomial f hf) (fun P hP M hM hV => hGrowth p hp d P hP M hM hV)

/-- The upper bound in Theorem 2. -/
theorem cstar_le_upperBase : Cstar ≤ upperBase :=
  cstar_le_upperBase_of_estimates
    (fun _ hp _ f _ hw => complexNoise_contract hp hw f)
    (fun _ hp _ _ hP _ hM hbound => polynomialGrowth hp hP hM hbound)

end Grokability
