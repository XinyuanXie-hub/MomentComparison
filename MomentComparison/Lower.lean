module

public import MomentComparison.Basic
import MomentComparison.FiniteFourth
import MomentComparison.RealHypercontractivity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.Linarith
import all MomentComparison.Basic

open Filter Finset
open scoped Topology

namespace MomentComparison

/-- The leading coefficient of a shifted binomial polynomial. -/
private theorem tendsto_choose_normalized (a d : ℕ) :
    Tendsto (fun n : ℕ => ((n - a).choose d : ℝ) / (n : ℝ) ^ d)
      atTop (𝓝 ((d.factorial : ℝ)⁻¹)) := by
  have hdesc (e : ℕ) :
      Tendsto (fun n : ℕ => ((n - a).descFactorial e : ℝ) / (n : ℝ) ^ e)
        atTop (𝓝 1) := by
    induction e with
    | zero => simp
    | succ e ih =>
      have hratio : Tendsto (fun n : ℕ => ((n - a - e : ℕ) : ℝ) / (n : ℝ))
          atTop (𝓝 1) := by
        have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).sub
          (tendsto_const_div_atTop_nhds_zero_nat ((a + e : ℕ) : ℝ))
        apply (by simpa only [sub_zero] using h :
          Tendsto (fun n : ℕ => 1 - ((a + e : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1)).congr'
        filter_upwards [eventually_ge_atTop (a + e), eventually_ge_atTop (1 : ℕ)] with n hn hp
        rw [Nat.sub_sub, Nat.cast_sub hn, sub_div, div_self (by positivity)]
      apply (by simpa only [one_mul] using hratio.mul ih :
        Tendsto (fun n : ℕ => ((n - a - e : ℕ) : ℝ) / (n : ℝ) *
          (((n - a).descFactorial e : ℝ) / (n : ℝ) ^ e)) atTop (𝓝 1)).congr'
      filter_upwards with n
      rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ', mul_div_mul_comm]
  convert (hdesc d).const_mul ((d.factorial : ℝ)⁻¹) using 1
  · funext n
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_div_assoc, ← mul_assoc,
      inv_mul_cancel₀ (by positivity), one_mul]
  · simp

private theorem exists_large_binomial_term (m : ℕ) :
    ∃ k ≤ m, (9 : ℝ) ^ m ≤ ((m : ℝ) + 1) ^ 2 * (2 * (m : ℝ) + 1) *
      ((2 * k).choose k : ℝ) * (m.choose k : ℝ) ^ 2 := by
  let terms := range (m + 1)
  let value (j : ℕ) : ℝ := (2 : ℝ) ^ j * (m.choose j : ℝ)
  obtain ⟨k, hk, hmax⟩ := exists_max_image terms value (⟨0, by simp [terms]⟩)
  have hkm : k ≤ m := by simpa [terms] using hk
  have hsum : (3 : ℝ) ^ m = ∑ j ∈ terms, value j := by
    simpa [terms, value, show (2 : ℝ) + 1 = 3 by norm_num] using (add_pow (2 : ℝ) 1 m)
  have hle : (3 : ℝ) ^ m ≤ ((m : ℝ) + 1) * value k := by
    rw [hsum]
    calc
      _ ≤ ∑ j ∈ terms, value k := sum_le_sum fun j hj => hmax j hj
      _ = _ := by simp [terms, nsmul_eq_mul]
  have hcenter : (4 : ℝ) ^ k ≤ (2 * (k : ℝ) + 1) * ((2 * k).choose k : ℝ) := by
    exact_mod_cast Nat.four_pow_le_two_mul_add_one_mul_centralBinom k
  refine ⟨k, hkm, ?_⟩
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (3 : ℝ) ^ m) hle 2
  calc
    (9 : ℝ) ^ m = ((3 : ℝ) ^ m) ^ 2 := by rw [pow_two, ← mul_pow]; norm_num
    _ ≤ (((m : ℝ) + 1) * value k) ^ 2 := hsq
    _ = ((m : ℝ) + 1) ^ 2 * (4 : ℝ) ^ k * (m.choose k : ℝ) ^ 2 := by
      dsimp only [value]
      rw [mul_pow, mul_pow, pow_two ((2 : ℝ) ^ k), ← mul_pow]; norm_num; ring
    _ ≤ _ := by
      have hkm' : (k : ℝ) ≤ m := by exact_mod_cast hkm
      have hcenter' := hcenter.trans (show (2 * (k : ℝ) + 1) * ((2 * k).choose k : ℝ) ≤
          (2 * (m : ℝ) + 1) * ((2 * k).choose k : ℝ) by gcongr)
      repeat rw [mul_assoc (((m : ℝ) + 1) ^ 2)]
      gcongr

private theorem exponential_base_ge_sqrt_three {C : ℝ} (hC : 0 < C)
    (h : ∀ m : ℕ, 0 < m →
      (9 : ℝ) ^ m ≤ ((m : ℝ) + 1) ^ 2 * (2 * (m : ℝ) + 1) * C ^ (4 * m)) :
    Real.sqrt 3 ≤ C := by
  by_contra! hc
  have hc₂ : C ^ 2 < 3 := by nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
  have hc₄ : C ^ 4 < 9 := by nlinarith [mul_pos (sub_pos.mpr hc₂) (show 0 < 3 + C ^ 2 by positivity)]
  let q := C ^ 4 / 9
  have hq : |q| < 1 := by
    rw [abs_of_nonneg (by dsimp [q]; positivity)]
    exact (div_lt_one (by norm_num)).mpr hc₄
  have ht := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 3 hq).const_mul (12 : ℝ)
  have ht' : Tendsto (fun m : ℕ => (12 : ℝ) * ((m : ℝ) ^ 3 * q ^ m)) atTop (𝓝 0) := by
    simpa using ht
  have he : ∀ᶠ m : ℕ in atTop, (1 : ℝ) ≤ 12 * ((m : ℝ) ^ 3 * q ^ m) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hp : ((m : ℝ) + 1) ^ 2 * (2 * (m : ℝ) + 1) ≤ 12 * (m : ℝ) ^ 3 := by
      calc
        _ ≤ (2 * (m : ℝ)) ^ 2 * (3 * (m : ℝ)) := by
          gcongr <;> linarith
        _ = _ := by ring
    have hineq := h m (by omega)
    have hquo : (1 : ℝ) ≤ (((m : ℝ) + 1) ^ 2 * (2 * (m : ℝ) + 1) * C ^ (4 * m)) / 9 ^ m :=
      (le_div_iff₀ (by positivity)).2 (by simpa using hineq)
    calc
      (1 : ℝ) ≤ (((m : ℝ) + 1) ^ 2 * (2 * (m : ℝ) + 1)) * q ^ m := by
        simpa only [q, div_pow, ← mul_div_assoc, ← pow_mul] using hquo
      _ ≤ _ := by rw [← mul_assoc]; gcongr
  have := ge_of_tendsto ht' he
  norm_num at this

/-- Passing a finite fourth-moment bound to its leading binomial coefficient. -/
private theorem binomial_limit_bound {A : ℝ} {m k : ℕ} (hkm : k ≤ m)
    (h : ∀ n : ℕ, 0 < n →
      (n.choose (2 * k) : ℝ) * ((2 * k).choose k : ℝ) ^ 2 *
        ((n - 2 * k).choose (m - k) : ℝ) ^ 2 ≤ A * (n.choose m : ℝ) ^ 2) :
    ((2 * k).choose k : ℝ) * (m.choose k : ℝ) ^ 2 ≤ A := by
  let b := ((2 * k).choose k : ℝ)
  let kf := (k.factorial : ℝ)
  let rf := ((m - k).factorial : ℝ)
  let mf := (m.factorial : ℝ)
  let df := ((2 * k).factorial : ℝ)
  have hkf : 0 < kf := by dsimp [kf]; positivity
  have hrf : 0 < rf := by dsimp [rf]; positivity
  have hmf : 0 < mf := by dsimp [mf]; positivity
  have hdf : 0 < df := by dsimp [df]; positivity
  have hden (n : ℕ) :
      (n : ℝ) ^ (2 * k) * ((n : ℝ) ^ (m - k)) ^ 2 = ((n : ℝ) ^ m) ^ 2 := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hleft : Tendsto (fun n : ℕ => (n.choose (2 * k) : ℝ) / (n : ℝ) ^ (2 * k) *
      b ^ 2 * (((n - 2 * k).choose (m - k) : ℝ) / (n : ℝ) ^ (m - k)) ^ 2)
      atTop (𝓝 (df⁻¹ * b ^ 2 * rf⁻¹ ^ 2)) := by
    simpa [df, rf] using
      ((tendsto_choose_normalized 0 (2 * k)).mul_const (b ^ 2)).mul
        ((tendsto_choose_normalized (2 * k) (m - k)).pow 2)
  have hright : Tendsto (fun n : ℕ => A * ((n.choose m : ℝ) / (n : ℝ) ^ m) ^ 2)
      atTop (𝓝 (A * mf⁻¹ ^ 2)) := by
    simpa [mf] using ((tendsto_choose_normalized 0 m).pow 2).const_mul A
  have hlim : df⁻¹ * b ^ 2 * rf⁻¹ ^ 2 ≤ A * mf⁻¹ ^ 2 := by
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hscaled := div_le_div_of_nonneg_right (h n (by omega)) (sq_nonneg ((n : ℝ) ^ m))
    rw [div_pow, div_pow, div_mul_eq_mul_div, div_mul_div_comm, hden, ← mul_div_assoc]
    exact hscaled
  have hbf : b * kf * kf = df := by
    dsimp [b, kf, df]
    exact_mod_cast (by simpa [show 2 * k - k = k by omega] using
      Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega))
  have hmf' : (m.choose k : ℝ) * kf * rf = mf := by
    dsimp [kf, rf, mf]
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkm
  have hB : b / df = (kf⁻¹) ^ 2 := by
    field_simp
    linarith [hbf]
  have hM : mf / rf = (m.choose k : ℝ) * kf := by
    exact (div_eq_iff hrf.ne').2 hmf'.symm
  calc
    b * (m.choose k : ℝ) ^ 2 = (df⁻¹ * b ^ 2 * rf⁻¹ ^ 2) * mf ^ 2 := by
      symm
      calc
        _ = b * (b / df) * (mf / rf) ^ 2 := by ring
        _ = _ := by rw [hB, hM]; field_simp
    _ ≤ (A * mf⁻¹ ^ 2) * mf ^ 2 := by gcongr
    _ = A := by field_simp

public section

/-- Every admissible base is at least √3, as witnessed by squares of symmetric Walsh sums. -/
theorem lowerBound_of_admissible {C : ℝ} (hC : 0 < C)
    (h : ∀ (n d : ℕ), 0 < n → 0 < d → ∀ f : Cube n → ℝ, HasDegreeLE f d →
      Real.sqrt (cubeAverage fun x => f x ^ 2) ≤ C ^ d * cubeAverage (fun x => |f x|)) :
    Real.sqrt 3 ≤ C := by
  apply exponential_base_ge_sqrt_three hC
  intro m hm
  obtain ⟨k, hkm, hlarge⟩ := exists_large_binomial_term m
  have hratio : ((2 * k).choose k : ℝ) * (m.choose k : ℝ) ^ 2 ≤ C ^ (4 * m) := by
    apply binomial_limit_bound hkm
    intro n hn
    have hnorm := h n (2 * m) hn (by omega) (fun x => walshLayer n m x ^ 2)
      (hasDegreeLE_walshLayer_sq n m)
    have habs : ∀ x : Cube n, |walshLayer n m x ^ 2| = walshLayer n m x ^ 2 :=
      fun x => abs_of_nonneg (sq_nonneg _)
    simp only [habs, ← pow_mul, show (2 : ℕ) * 2 = 4 by decide,
      cubeAverage_walshLayer_sq] at hnorm
    have hsquare := (Real.sqrt_le_left
      (by positivity : 0 ≤ C ^ (2 * m) * (n.choose m : ℝ))).1 hnorm
    apply (finite_fourth_ge n m k hkm).trans
    convert hsquare using 1
    rw [mul_pow, ← pow_mul]
    congr 2
    omega
  exact hlarge.trans (by rw [mul_assoc (((m : ℝ) + 1) ^ 2 * (2 * (m : ℝ) + 1))]; gcongr)

/-- The lower bound in Theorem 2. -/
theorem lowerBound : Real.sqrt 3 ≤ Cstar := by
  unfold Cstar
  refine le_csInf admissible_nonempty ?_
  rintro C ⟨hC, h⟩
  exact lowerBound_of_admissible hC h


end

end MomentComparison
