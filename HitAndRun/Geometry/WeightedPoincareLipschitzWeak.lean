module
public import HitAndRun.Geometry.WeightedPoincareLocallyLipschitz
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set Filter Metric
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Actual Fréchet weak derivative of a globally Lipschitz scalar function,
using Mathlib's difference-quotient integration by parts and Rademacher. -/
theorem lipschitz_integral_fderiv_test (μ : Measure E) [μ.IsAddHaarMeasure]
    {f φ : E → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (v : E) :
    (∫ x, f x * fderiv ℝ φ x v ∂μ) = -(∫ x, fderiv ℝ f x v * φ x ∂μ) := by
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcφ hφ (by norm_num)
  have h := hf.integral_lineDeriv_mul_eq hD hcφ v (μ := μ)
  have he : (∫ x, lineDeriv ℝ f x v * φ x ∂μ) = ∫ x, fderiv ℝ f x v * φ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf.ae_differentiableAt (μ := μ)] with x hx
    rw [hx.lineDeriv_eq_fderiv]
  rw [he] at h
  have he' : (∫ x, lineDeriv ℝ φ x (-v) * f x ∂μ) =
      -(∫ x, f x * fderiv ℝ φ x v ∂μ) := by
    simp_rw [((hφ.differentiable (by norm_num)).differentiableAt).lineDeriv_eq_fderiv,
      map_neg, neg_mul, integral_neg, mul_comm]
  rw [he'] at h
  linarith

/-- Source-faithful locally Lipschitz integration by parts. The extension is
only an auxiliary global Lipschitz function agreeing near the compact test. -/
theorem locallyLipschitz_integral_fderiv_test (μ : Measure E) [μ.IsAddHaarMeasure]
    {f φ : E → ℝ} (hf : LocallyLipschitz f)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (v : E) :
    (∫ x, f x * fderiv ℝ φ x v ∂μ) = -(∫ x, fderiv ℝ f x v * φ x ∂μ) := by
  obtain ⟨R, hR⟩ := hcφ.isBounded.subset_ball (0 : E)
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : E) R) (hf.locallyLipschitzOn (s := closedBall 0 R))
  obtain ⟨g, hg, heq⟩ := hC.extend_real
  have heqnear : ∀ x ∈ tsupport φ, f =ᶠ[𝓝 x] g := by
    intro x hx
    filter_upwards [isOpen_ball.mem_nhds (hR hx)] with y hy
    exact heq (ball_subset_closedBall hy)
  have hleft : (∫ x, f x * fderiv ℝ φ x v ∂μ) = ∫ x, g x * fderiv ℝ φ x v ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change f x * fderiv ℝ φ x v = g x * fderiv ℝ φ x v
      by_cases hx : x ∈ tsupport φ
      · rw [(heqnear x hx).eq_of_nhds]
      · rw [fderiv_of_notMem_tsupport ℝ hx]
        simp
  have hright : (∫ x, fderiv ℝ f x v * φ x ∂μ) = ∫ x, fderiv ℝ g x v * φ x ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change fderiv ℝ f x v * φ x = fderiv ℝ g x v * φ x
      by_cases hx : x ∈ tsupport φ
      · rw [(heqnear x hx).fderiv_eq]
      · rw [image_eq_zero_of_notMem_tsupport hx]
        simp
  rw [hleft, hright]
  exact lipschitz_integral_fderiv_test μ hg hφ hcφ v
end HitAndRun.Geometry
