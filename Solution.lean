module

public import MomentComparison.Lower
public import MomentComparison.Upper

public section

namespace MomentComparison

/-- Theorem 2 of Ivanisvili–Xie, *Grokability in five inequalities*. -/
theorem theorem2 : Real.sqrt 3 ≤ Cstar ∧ Cstar ≤ upperBase := by
  exact ⟨lowerBound, cstar_le_upperBase⟩

end MomentComparison
