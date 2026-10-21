module
import HitAndRun.Sobolev.ZeroMean
open MeasureTheory HitAndRun.Sobolev
open scoped NNReal
example {n : ℕ} [NeZero n] (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (u : VectorField μ Ω) :
    ‖divergence μ Ω u‖ ≤ Real.sqrt n * ‖u‖ := norm_divergence_le u
example {n : ℕ} [NeZero n] (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (Ω : Set (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure (μ.restrict Ω)]
    (u : VectorField μ Ω) : (∫ x in Ω, divergence μ Ω u x ∂μ) = 0 := by
  rw [← meanCLM_eq_integral]
  exact divergence_mean_zero u
#print axioms HitAndRun.Sobolev.norm_diagonalDerivative_le
#print axioms HitAndRun.Sobolev.norm_divergence_sq_le
#print axioms HitAndRun.Sobolev.norm_divergence_le
#print axioms HitAndRun.Sobolev.meanCLM_eq_integral
#print axioms HitAndRun.Sobolev.integral_test_partial_zero
#print axioms HitAndRun.Sobolev.h01_partial_mean_zero
#print axioms HitAndRun.Sobolev.gradient_partial_mean_zero
#print axioms HitAndRun.Sobolev.divergence_mean_zero
#print axioms HitAndRun.Sobolev.centeredDivergence
