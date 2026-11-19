module

public import MomentComparison.Basic
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
import all MomentComparison.Basic

public section

open scoped BigOperators symmDiff

namespace Grokability

open Finset

/-- A cube coordinate interpreted as a real sign. -/
@[expose] def cubeSign {n : ℕ} (x : Cube n) (i : Fin n) : ℝ := if x i then 1 else -1

/-- The Walsh character with support `s`. -/
@[expose] def walsh {n : ℕ} (s : Finset (Fin n)) (x : Cube n) : ℝ := ∏ i ∈ s, cubeSign x i

@[simp] theorem walsh_empty {n : ℕ} (x : Cube n) : walsh ∅ x = 1 := by
  simp [walsh]

@[simp] theorem cubeSign_mul_self {n : ℕ} (x : Cube n) (i : Fin n) :
    cubeSign x i * cubeSign x i = 1 := by
  cases h : x i <;> simp [cubeSign, h]

theorem walsh_symmDiff {n : ℕ} (s t : Finset (Fin n)) (x : Cube n) :
    walsh (s ∆ t) x = walsh s x * walsh t x := by
  change (∏ i ∈ (s \ t) ∪ (t \ s), cubeSign x i) = _
  rw [prod_union (disjoint_sdiff_sdiff : Disjoint (s \ t) (t \ s))]
  unfold walsh
  have hs := prod_inter_mul_prod_sdiff s t (cubeSign x)
  have ht := prod_inter_mul_prod_sdiff t s (cubeSign x)
  rw [inter_comm t s] at ht
  rw [← hs, ← ht]
  have h : (∏ i ∈ s ∩ t, cubeSign x i) * (∏ i ∈ s ∩ t, cubeSign x i) = 1 := by
    rw [← prod_mul_distrib]
    simp only [cubeSign_mul_self, prod_const_one]
  calc
    _ = (∏ i ∈ s \ t, cubeSign x i) * (∏ i ∈ t \ s, cubeSign x i) * 1 := by rw [mul_one]
    _ = _ := by rw [← h]; ring

theorem cubeAverage_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Cube n → ℝ) :
    cubeAverage (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, cubeAverage (f i) := by
  simp only [cubeAverage, div_eq_mul_inv, ← sum_mul]
  congr 1
  exact sum_comm

theorem cubeAverage_const_mul {n : ℕ} (c : ℝ) (f : Cube n → ℝ) :
    cubeAverage (fun x => c * f x) = c * cubeAverage f := by
  simp only [cubeAverage, ← mul_sum, mul_div_assoc]

theorem cubeAverage_mul_const {n : ℕ} (f : Cube n → ℝ) (c : ℝ) :
    cubeAverage (fun x => f x * c) = cubeAverage f * c := by
  simpa only [mul_comm] using cubeAverage_const_mul c f

@[simp] theorem cubeAverage_const {n : ℕ} (c : ℝ) :
    cubeAverage (fun _ : Cube n => c) = c := by
  unfold cubeAverage
  simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact mul_div_cancel_left₀ _ (by positivity)

theorem cubeAverage_cons {n : ℕ} (f : Cube (n + 1) → ℝ) :
    cubeAverage f = (cubeAverage (fun x => f (Fin.cons true x)) +
      cubeAverage (fun x => f (Fin.cons false x))) / 2 := by
  unfold cubeAverage
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
    (fun x => f (Fin.cons x.1 x.2)) f (fun x => rfl)]
  rw [Fintype.sum_prod_type]
  have h : (Finset.univ : Finset Bool) = {true, false} := by decide
  rw [h]
  simp [pow_succ]
  ring

private def flip {n : ℕ} (i : Fin n) (x : Cube n) : Cube n :=
  Function.update x i (!x i)

private theorem flip_involutive {n : ℕ} (i : Fin n) : Function.Involutive (flip i) := by
  intro x
  ext j
  by_cases h : j = i
  · subst j
    simp [flip]
  · simp [flip, Function.update_of_ne h]

private theorem walsh_flip {n : ℕ} (s : Finset (Fin n)) (x : Cube n) {i : Fin n}
    (hi : i ∈ s) : walsh s (flip i x) = -walsh s x := by
  unfold walsh
  rw [← prod_erase_mul s _ hi, ← prod_erase_mul s _ hi]
  have he : (∏ j ∈ s.erase i, cubeSign (flip i x) j) =
      ∏ j ∈ s.erase i, cubeSign x j := by
    apply prod_congr rfl
    intro j hj
    simp [cubeSign, flip, Function.update_of_ne (ne_of_mem_erase hj)]
  rw [he]
  cases h : x i <;> simp [cubeSign, flip, h]

theorem cubeAverage_walsh {n : ℕ} (s : Finset (Fin n)) :
    cubeAverage (walsh s) = if s = ∅ then 1 else 0 := by
  split_ifs with h
  · subst s
    simpa only [show walsh (∅ : Finset (Fin n)) = fun _ => 1 from funext walsh_empty] using
      (cubeAverage_const (n := n) 1)
  · obtain ⟨i, hi⟩ := nonempty_iff_ne_empty.mpr h
    let e := (flip_involutive i).toPerm (flip i)
    have he := Equiv.sum_comp e (walsh s)
    change (∑ x, walsh s (flip i x)) = ∑ x, walsh s x at he
    simp_rw [walsh_flip s _ hi, sum_neg_distrib] at he
    have hz : (∑ x, walsh s x) = 0 := by linarith
    simp [cubeAverage, hz]

theorem cubeAverage_walsh_mul {n : ℕ} (s t : Finset (Fin n)) :
    cubeAverage (fun x => walsh s x * walsh t x) = if s = t then 1 else 0 := by
  simp_rw [← walsh_symmDiff]
  simp only [cubeAverage_walsh, Finset.symmDiff_eq_empty]

theorem hasDegreeLE_sum_walsh {n d : ℕ} {ι : Type*} (u : Finset ι)
    (s : ι → Finset (Fin n)) (a : ι → ℝ)
    (h : ∀ i ∈ u, (s i).card ≤ d) :
    HasDegreeLE (fun x => ∑ i ∈ u, a i * walsh (s i) x) d := by
  intro t ht
  change cubeAverage (fun x => (∑ i ∈ u, a i * walsh (s i) x) * walsh t x) = 0
  simp_rw [sum_mul, mul_assoc]
  rw [cubeAverage_sum]
  apply sum_eq_zero
  intro i hi
  have hne : s i ≠ t := fun he => (not_lt_of_ge (he ▸ h i hi)) ht
  simp [cubeAverage_const_mul, cubeAverage_walsh_mul, hne]

/-- Sum of the Walsh characters of a single degree. -/
@[expose] noncomputable def walshLayer (n m : ℕ) (x : Cube n) : ℝ :=
  ∑ s ∈ (univ : Finset (Fin n)).powersetCard m, walsh s x

theorem cubeAverage_walshLayer_sq (n m : ℕ) :
    cubeAverage (fun x => walshLayer n m x ^ 2) = (n.choose m : ℝ) := by
  simp_rw [walshLayer, pow_two, sum_mul, mul_sum, cubeAverage_sum, cubeAverage_walsh_mul]
  have h : ((univ : Finset (Fin n)).powersetCard m).filter (fun s => s.card = m) =
      (univ : Finset (Fin n)).powersetCard m :=
    filter_true_of_mem fun _ hs => (mem_powersetCard.mp hs).2
  simp [h, card_powersetCard]

theorem card_walsh_symmDiff_le {n : ℕ} (s t : Finset (Fin n)) :
    (s ∆ t).card ≤ s.card + t.card := by
  exact (card_le_card (symmDiff_le_sup : s ∆ t ⊆ s ∪ t)).trans (card_union_le s t)

theorem hasDegreeLE_walshLayer_sq (n m : ℕ) :
    HasDegreeLE (fun x => walshLayer n m x ^ 2) (2 * m) := by
  simp_rw [walshLayer, pow_two, sum_mul, mul_sum, ← walsh_symmDiff, ← sum_product']
  let u := (univ : Finset (Fin n)).powersetCard m
  simpa only [one_mul] using
    hasDegreeLE_sum_walsh (d := 2 * m) (u ×ˢ u) (fun st => st.1 ∆ st.2) (fun _ => 1) (by
      intro st hst
      obtain ⟨hs, ht⟩ := mem_product.mp hst
      calc
        _ ≤ st.1.card + st.2.card := card_walsh_symmDiff_le _ _
        _ = 2 * m := by rw [(mem_powersetCard.mp hs).2, (mem_powersetCard.mp ht).2, two_mul])


/-- The Walsh kernel is diagonal in the point basis of the cube. -/
theorem walsh_kernel {n : ℕ} (x y : Cube n) :
    (∑ s : Finset (Fin n), walsh s x * walsh s y) = if x = y then (2 : ℝ)^n else 0 := by
  have hprod : (∑ s : Finset (Fin n), walsh s x * walsh s y) =
      ∏ i : Fin n, (cubeSign x i * cubeSign y i + 1) := by
    rw [Fintype.prod_add]
    simp only [prod_const_one, mul_one, walsh, prod_mul_distrib]
  rw [hprod]
  by_cases h : x = y
  · subst y
    simp [cubeSign_mul_self, show (1 : ℝ) + 1 = 2 by norm_num]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra! he
      exact h (funext he)
    refine prod_eq_zero (mem_univ i) ?_
    cases hx : x i <;> cases hy : y i <;> simp_all [cubeSign]

/-- A real function on the cube is reconstructed from its Walsh coefficients. -/
theorem walshExpansion {n : ℕ} (f : Cube n → ℝ) (x : Cube n) :
    (∑ s : Finset (Fin n), (cubeAverage fun y => f y * walsh s y) * walsh s x) = f x := by
  calc
    _ = (∑ s : Finset (Fin n), cubeAverage (fun y => f y * (walsh s y * walsh s x))) := by
      simp_rw [← mul_assoc, cubeAverage_mul_const]
    _ = cubeAverage (fun y => f y * ∑ s : Finset (Fin n), walsh s y * walsh s x) := by
      simp_rw [mul_sum, cubeAverage_sum]
    _ = f x := by
      simp only [walsh_kernel, mul_ite, mul_zero, cubeAverage, Fintype.sum_ite_eq',
        mul_div_cancel_right₀ _ (show (2 : ℝ)^n ≠ 0 by positivity)]

theorem constant_of_hasDegreeLE_zero {n : ℕ} {f : Cube n → ℝ}
    (h : HasDegreeLE f 0) : ∃ c, ∀ x, f x = c := by
  refine ⟨cubeAverage f, fun x => ?_⟩
  rw [← walshExpansion f x]
  have hz : ∀ s : Finset (Fin n), s ≠ ∅ →
      (cubeAverage fun y => f y * walsh s y) * walsh s x = 0 := by
    intro s hs
    have he := h s (card_pos.mpr (nonempty_iff_ne_empty.mpr hs))
    change cubeAverage (fun y => f y * walsh s y) = 0 at he
    simp [he]
  rw [sum_eq_single ∅ (fun s _ hs => hz s hs) (by simp)]
  simp [walsh_empty]

/-- Number of ordered pairs of sets of size `m` with symmetric difference `T`. -/
@[expose] def walshPairCount (n m : ℕ) (T : Finset (Fin n)) : ℕ :=
  let u := (univ : Finset (Fin n)).powersetCard m
  ((u ×ˢ u).filter (fun st => st.1 ∆ st.2 = T)).card

theorem walshLayer_sq_expansion (n m : ℕ) (x : Cube n) :
    walshLayer n m x ^ 2 = ∑ T : Finset (Fin n), (walshPairCount n m T : ℝ) * walsh T x := by
  simp_rw [walshLayer, pow_two, sum_mul, mul_sum, ← walsh_symmDiff, ← sum_product']
  let u := (univ : Finset (Fin n)).powersetCard m
  rw [← sum_fiberwise (u ×ˢ u) (fun st => st.1 ∆ st.2) (fun st => walsh (st.1 ∆ st.2) x)]
  apply sum_congr rfl
  intro T _
  unfold walshPairCount
  rw [← nsmul_eq_mul, ← sum_const]
  exact sum_congr rfl (fun st hst => congrArg (fun S => walsh S x) (mem_filter.mp hst).2)

theorem cubeAverage_walshLayer_fourth (n m : ℕ) :
    cubeAverage (fun x => walshLayer n m x ^ 4) =
      ∑ T : Finset (Fin n), (walshPairCount n m T : ℝ) ^ 2 := by
  have hpow (z : ℝ) : z ^ 4 = z ^ 2 * z ^ 2 := by ring
  simp_rw [hpow, walshLayer_sq_expansion, sum_mul, mul_sum, cubeAverage_sum]
  let a := fun T : Finset (Fin n) => (walshPairCount n m T : ℝ)
  change (∑ s : Finset (Fin n), ∑ t : Finset (Fin n),
    cubeAverage (fun x => (a s * walsh s x) * (a t * walsh t x))) = _
  have havg (s t : Finset (Fin n)) :
      cubeAverage (fun x => (a s * walsh s x) * (a t * walsh t x)) =
      if s = t then (a s)^2 else 0 := by
    have ha (x : Cube n) : (a s * walsh s x) * (a t * walsh t x) =
        (a s * a t) * (walsh s x * walsh t x) := by ring
    simp_rw [ha, cubeAverage_const_mul, cubeAverage_walsh_mul]
    split_ifs with h
    · subst t
      simp [pow_two]
    · simp
  simp_rw [havg]
  simp [a]

end Grokability
