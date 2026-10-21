module
public import MixingSource
@[expose] public section
noncomputable section
namespace HitAndRun.Markov
/-- Explicit source scaling with integer rounding. The zero-step branch is necessary
when the paper's informal logarithm is nonpositive; the TeX is not modified. -/
theorem mixingSource_budget_formula {c d M ε : ℝ} (hc : 0 < c) (hd : 0 < d) :
    mixingBudget (c/d) M ε =
      if M ≤ ε then 0 else Nat.ceil (d * Real.log (M/ε) / (2*c)) := by
  unfold mixingBudget
  split_ifs
  · rfl
  · congr 1
    field_simp
end HitAndRun.Markov
