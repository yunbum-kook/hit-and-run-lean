module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic.Linarith
@[expose] public section

/-! Generic Hilbert-space dual certificate from Section 1.2.2 of arXiv:2608.16878v1.
This helper does not construct the Sobolev certificate or identify either Markov kernel.
-/
namespace HitAndRun

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- An actual adjoint preimage with a squared-norm bound controls the energy. -/
theorem norm_sq_le_of_dual_certificate (T : E →L[ℝ] F) (f : E) (g : F)
    (C : ℝ) (hcert : T.adjoint g = f)
    (hbound : ‖g‖ ^ 2 ≤ C * ‖f‖ ^ 2) :
    ‖f‖ ^ 2 ≤ C * ‖T f‖ ^ 2 := by
  have hi : inner ℝ (T f) g = ‖f‖ ^ 2 := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hcert, real_inner_self_eq_norm_sq]
  have hcs : ‖f‖ ^ 2 ≤ ‖T f‖ * ‖g‖ := by
    rw [← hi]
    exact real_inner_le_norm _ _
  have hsq := mul_self_le_mul_self (sq_nonneg ‖f‖) hcs
  have hb := mul_le_mul_of_nonneg_left hbound (sq_nonneg ‖T f‖)
  by_cases hf : f = 0
  · simp [hf]
  · have hp : 0 < ‖f‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
    nlinarith

end HitAndRun
