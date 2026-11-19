module

public import MomentComparison.Walsh
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Defs
import all MomentComparison.Basic

public section

open scoped BigOperators

namespace Grokability

open Finset

/-- Complex noise on the cube, defined by applying the two-point noise operator
in each coordinate. -/
@[expose] noncomputable def complexNoise : {n : ℕ} → ℂ → (Cube n → ℂ) → Cube n → ℂ
  | 0, _, f, x => f x
  | n + 1, w, f, x =>
      let a := complexNoise w (fun y => f (Fin.cons true y : Cube (n + 1))) (Fin.tail x)
      let b := complexNoise w (fun y => f (Fin.cons false y : Cube (n + 1))) (Fin.tail x)
      (a + b) / 2 + (if x 0 then 1 else -1) * w * (a - b) / 2

theorem complexNoise_zero (w : ℂ) (f : Cube 0 → ℂ) (x : Cube 0) :
    complexNoise w f x = f x := rfl

theorem complexNoise_cons {n : ℕ} (w : ℂ) (f : Cube (n + 1) → ℂ) (b : Bool) (x : Cube n) :
    complexNoise w f (Fin.cons b x) =
      (complexNoise w (fun y => f (Fin.cons true y)) x +
        complexNoise w (fun y => f (Fin.cons false y)) x) / 2 +
      (if b then 1 else -1) * w *
        (complexNoise w (fun y => f (Fin.cons true y)) x -
          complexNoise w (fun y => f (Fin.cons false y)) x) / 2 := by
  simp only [complexNoise, Fin.cons_zero, Fin.tail_cons]

private theorem complexNoise_zero_function {n : ℕ} (w : ℂ) (x : Cube n) :
    complexNoise w (fun _ => 0) x = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Fin.cons_self_tail x, complexNoise_cons]
    simp [ih]

private theorem complexNoise_add {n : ℕ} (w : ℂ) (f g : Cube n → ℂ) (x : Cube n) :
    complexNoise w (fun y => f y + g y) x = complexNoise w f x + complexNoise w g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Fin.cons_self_tail x]
    simp only [complexNoise_cons, ih]
    ring

private theorem complexNoise_const_mul {n : ℕ} (w c : ℂ) (f : Cube n → ℂ) (x : Cube n) :
    complexNoise w (fun y => c * f y) x = c * complexNoise w f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Fin.cons_self_tail x]
    simp only [complexNoise_cons, ih]
    ring

private theorem complexNoise_sum {n : ℕ} {ι : Type*} (w : ℂ) (u : Finset ι)
    (f : ι → Cube n → ℂ) (x : Cube n) :
    complexNoise w (fun y => ∑ i ∈ u, f i y) x =
      ∑ i ∈ u, complexNoise w (f i) x := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [complexNoise_zero_function]
  | insert i u hi ih =>
    simp_rw [sum_insert hi, complexNoise_add, ih]

private def tailSet {n : ℕ} (s : Finset (Fin (n + 1))) : Finset (Fin n) :=
  univ.filter (fun i => i.succ ∈ s)

private theorem map_tailSet {n : ℕ} (s : Finset (Fin (n + 1))) :
    (tailSet s).map (Fin.succEmb n) = s.erase 0 := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [tailSet]
  · simp [tailSet]

private theorem walsh_tail {n : ℕ} (s : Finset (Fin (n + 1))) (b : Bool) (x : Cube n) :
    walsh (s.erase 0) (Fin.cons b x) = walsh (tailSet s) x := by
  rw [← map_tailSet s]
  simp only [walsh, prod_map]
  apply prod_congr rfl
  intro i _
  rfl

private theorem walsh_cons_of_mem {n : ℕ} (s : Finset (Fin (n + 1))) (h : 0 ∈ s)
    (b : Bool) (x : Cube n) :
    walsh s (Fin.cons b x) = walsh (tailSet s) x * (if b then 1 else -1) := by
  unfold walsh at *
  rw [← prod_erase_mul s _ h]
  change walsh (s.erase 0) (Fin.cons b x) * _ = _
  rw [walsh_tail]
  rfl

private theorem walsh_cons_of_notMem {n : ℕ} (s : Finset (Fin (n + 1))) (h : 0 ∉ s)
    (b : Bool) (x : Cube n) : walsh s (Fin.cons b x) = walsh (tailSet s) x := by
  simpa only [erase_eq_of_notMem h] using walsh_tail s b x

theorem complexNoise_walsh {n : ℕ} (w : ℂ) (s : Finset (Fin n)) (x : Cube n) :
    complexNoise w (fun y => (walsh s y : ℂ)) x = w ^ s.card * (walsh s x : ℂ) := by
  induction n with
  | zero =>
    have hs : s = ∅ := eq_empty_of_forall_notMem fun i _ => Fin.elim0 i
    simp [hs, complexNoise_zero]
  | succ n ih =>
    rw [← Fin.cons_self_tail x]
    let b := x 0
    let y := Fin.tail x
    change complexNoise w (fun z => (walsh s z : ℂ)) (Fin.cons b y) =
      w ^ s.card * (walsh s (Fin.cons b y) : ℂ)
    have hcard : (tailSet s).card = (s.erase 0).card := by
      rw [← map_tailSet, card_map]
    rw [complexNoise_cons]
    by_cases h : 0 ∈ s
    · have hc : s.card = (tailSet s).card + 1 := by
        rw [hcard, card_erase_add_one h]
      simp only [walsh_cons_of_mem s h, Bool.false_eq_true, ↓reduceIte, mul_neg, mul_one,
        Complex.ofReal_neg]
      have hn : complexNoise w (fun z => -(walsh (tailSet s) z : ℂ)) y =
          - complexNoise w (fun z => (walsh (tailSet s) z : ℂ)) y := by
        simpa only [neg_one_mul] using
          complexNoise_const_mul w (-1) (fun z => (walsh (tailSet s) z : ℂ)) y
      rw [hn, ih, hc, pow_succ]
      cases b <;> simp <;> ring
    · have hc : s.card = (tailSet s).card := by rw [hcard, erase_eq_of_notMem h]
      simp only [walsh_cons_of_notMem s h, ih, hc]
      ring

/-- Walsh level `k` acquires the factor `w^k` under complex noise. -/
theorem complexNoise_ofReal {n : ℕ} (w : ℂ) (f : Cube n → ℝ) (x : Cube n) :
    complexNoise w (fun y => (f y : ℂ)) x =
      ∑ s : Finset (Fin n), (cubeAverage (fun y => f y * walsh s y) : ℂ) *
        (w ^ s.card * (walsh s x : ℂ)) := by
  have hf : (fun y => (f y : ℂ)) = fun y => ∑ s : Finset (Fin n),
      (cubeAverage (fun z => f z * walsh s z) : ℂ) * (walsh s y : ℂ) := by
    funext y
    exact_mod_cast (walshExpansion f y).symm
  rw [hf, complexNoise_sum]
  simp_rw [complexNoise_const_mul, complexNoise_walsh]

theorem complexNoise_one_ofReal {n : ℕ} (f : Cube n → ℝ) (x : Cube n) :
    complexNoise 1 (fun y => (f y : ℂ)) x = (f x : ℂ) := by
  rw [complexNoise_ofReal]
  simp only [one_pow, one_mul]
  exact_mod_cast walshExpansion f x

/-- Pairing the noise evolution of a degree-`d` function with any fixed function
gives a scalar polynomial of degree at most `d`. -/
theorem exists_noise_polynomial {n d : ℕ} (f : Cube n → ℝ) (hf : HasDegreeLE f d)
    (g : Cube n → ℂ) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ d ∧ ∀ w : ℂ,
      P.eval w = (∑ x, complexNoise w (fun y => (f y : ℂ)) x * g x) / (2 : ℂ) ^ n := by
  let u : Finset (Finset (Fin n)) := univ.filter (fun s => s.card ≤ d)
  let a : Finset (Fin n) → ℂ := fun s => (cubeAverage (fun y => f y * walsh s y) : ℂ)
  let c : Finset (Fin n) → ℂ := fun s =>
    (∑ x : Cube n, a s * ((walsh s x : ℂ) * g x)) / (2 : ℂ) ^ n
  refine ⟨∑ s ∈ u, Polynomial.monomial s.card (c s), ?_, fun w => ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro s hs
    exact (Polynomial.natDegree_monomial_le _).trans (mem_filter.mp hs).2
  · simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, complexNoise_ofReal]
    have hzero (s : Finset (Fin n)) (hs : s ∉ u) : a s = 0 := by
      have he := hf s (by simpa [u] using hs)
      change cubeAverage (fun y => f y * walsh s y) = 0 at he
      simp [a, he]
    have htrunc (x : Cube n) :
        (∑ s : Finset (Fin n), a s * (w ^ s.card * (walsh s x : ℂ))) =
          ∑ s ∈ u, a s * (w ^ s.card * (walsh s x : ℂ)) := by
      symm
      apply sum_subset (subset_univ u)
      intro s _ hs
      simp [hzero s hs]
    change (∑ s ∈ u, c s * w ^ s.card) =
      (∑ x : Cube n, (∑ s : Finset (Fin n),
        a s * (w ^ s.card * (walsh s x : ℂ))) * g x) / (2 : ℂ) ^ n
    simp_rw [htrunc, sum_mul, div_eq_mul_inv, c, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro s _
    simp only [div_eq_mul_inv, sum_mul]
    apply sum_congr rfl
    intro x _
    ring

end Grokability
