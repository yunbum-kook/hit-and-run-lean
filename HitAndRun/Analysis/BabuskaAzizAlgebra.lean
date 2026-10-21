module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
@[expose] public section

/-! Exact scalar energy bookkeeping for Theorem 1.4, after the analytic lemmas.
This does not prove the weighted estimate or the source theorem by itself. -/
namespace HitAndRun.Analysis

/-- The residual/curl energy relations give exactly 1+4C, not 2+4C. -/
theorem babuskaAziz_energy_algebra {H D G C : ℝ}
    (hD : 0 ≤ D) (hG : 0 ≤ G) (hC : 0 ≤ C)
    (hweighted : H ≤ 4 * C * G) (hcs : G ^ 2 ≤ H * D) :
    H + D + 2 * G ≤ (1 + 4 * C) * (D + G) := by
  have hm := mul_le_mul_of_nonneg_right hweighted hD
  have hg : G ≤ 4 * C * D := by
    by_cases hz : G = 0
    · rw [hz]
      positivity
    · have hp : 0 < G := lt_of_le_of_ne hG (Ne.symm hz)
      nlinarith
  nlinarith
end HitAndRun.Analysis
