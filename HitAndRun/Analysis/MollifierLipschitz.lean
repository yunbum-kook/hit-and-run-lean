module
public import HitAndRun.External.EllipticPDE.Analysis.Mollifier
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! Probability mollification preserves the exact Lipschitz constant. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Analysis
open MeasureTheory Metric
open scoped Convolution NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Averaging translates against the normalized nonnegative bump does not enlarge Lipschitz constants. -/
theorem lipschitz_normed_convolution (rho : ContDiffBump (0 : E))
    {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (rho.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) := by
  have hi (x : E) : ConvolutionExistsAt (rho.normed μ) f x
      (ContinuousLinearMap.lsmul ℝ ℝ) μ :=
    rho.hasCompactSupport_normed.convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (rho.contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) _).continuous
      hf.continuous.locallyIntegrable x
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, convolution_def, convolution_def, ← integral_sub (hi x) (hi y)]
  calc
    _ ≤ ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ (rho.normed μ t)) (f (x - t)) -
        (ContinuousLinearMap.lsmul ℝ ℝ (rho.normed μ t)) (f (y - t))‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t, rho.normed μ t * ((K : ℝ) * dist x y) ∂μ := by
      apply integral_mono ((hi x).sub (hi y)).norm
        (rho.integrable_normed.mul_const ((K : ℝ) * dist x y))
      intro t
      simp only [Pi.sub_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul, ← mul_sub,
        norm_mul, Real.norm_eq_abs, abs_of_nonneg (rho.nonneg_normed t)]
      apply mul_le_mul_of_nonneg_left _ (rho.nonneg_normed t)
      simpa only [Real.dist_eq, dist_sub_right] using hf.dist_le_mul (x - t) (y - t)
    _ = (K : ℝ) * dist x y := by
      rw [integral_mul_const, rho.integral_normed, one_mul]

/-- The mollification of a K-Lipschitz function differs uniformly by at most K times the radius. -/
theorem norm_normed_convolution_sub_le (rho : ContDiffBump (0 : E))
    {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (x : E) :
    ‖(rho.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x - f x‖ ≤
      (K : ℝ) * rho.rOut := by
  have hi : ConvolutionExistsAt (rho.normed μ) f x
      (ContinuousLinearMap.lsmul ℝ ℝ) μ :=
    rho.hasCompactSupport_normed.convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (rho.contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) _).continuous
      hf.continuous.locallyIntegrable x
  have hc : (∫ t, rho.normed μ t * f x ∂μ) = f x := by
    rw [integral_mul_const, rho.integral_normed, one_mul]
  rw [convolution_def, ← hc, ← integral_sub hi (rho.integrable_normed.mul_const (f x))]
  calc
    _ ≤ ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ (rho.normed μ t)) (f (x - t)) -
        rho.normed μ t * f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, rho.normed μ t * ((K : ℝ) * rho.rOut) ∂μ := by
      apply integral_mono (hi.sub (rho.integrable_normed.mul_const (f x))).norm
        (rho.integrable_normed.mul_const ((K : ℝ) * rho.rOut))
      intro t
      simp only [Pi.sub_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul, ← mul_sub,
        norm_mul, Real.norm_eq_abs, abs_of_nonneg (rho.nonneg_normed t)]
      by_cases ht : rho.normed μ t = 0
      · simp [ht]
      · have hm : t ∈ Function.support (rho.normed μ) := ht
        rw [rho.support_normed_eq] at hm
        have hn : ‖t‖ ≤ rho.rOut := (by simpa only [mem_ball, dist_zero_right] using hm : ‖t‖ < rho.rOut).le
        apply mul_le_mul_of_nonneg_left _ (rho.nonneg_normed t)
        have hl := hf.dist_le_mul (x - t) x
        have he : dist (x - t) x = ‖t‖ := by simp [dist_eq_norm]
        rw [he, Real.dist_eq] at hl
        exact hl.trans (mul_le_mul_of_nonneg_left hn K.coe_nonneg)
    _ = (K : ℝ) * rho.rOut := by
      rw [integral_mul_const, rho.integral_normed, one_mul]
end HitAndRun.Analysis
