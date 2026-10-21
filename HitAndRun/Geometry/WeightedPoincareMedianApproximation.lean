module
public import HitAndRun.Geometry.WeightedPoincareMedianDensity
@[expose] public section
namespace HitAndRun.Geometry
open MeasureTheory Filter Set
open scoped Topology

/-- Approximate first, then contract. This packages the L2 diagonal step for
smooth convolutions evaluated strictly inside a convex body. -/
theorem integral_sq_approx_dilation_sub_tendsto
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E} [μ.IsAddHaarMeasure] [μ.Regular]
    {K : Set E} [IsFiniteMeasure (μ.restrict K)]
    {f : E → F} {g : ℕ → E → F} (hf : MemLp f 2 μ) (hg : ∀ k, MemLp (g k) 2 μ)
    (hgf : Tendsto (fun k => ∫ x, ‖g k x - f x‖ ^ 2 ∂μ) atTop (𝓝 0))
    {a : ℕ → ℝ} (ha0 : ∀ k, 0 < a k) (ha : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun k => ∫ x in K, ‖g k (a k • x) - f x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hcoef : Tendsto (fun k => (a k ^ Module.finrank ℝ E)⁻¹) atTop (𝓝 1) := by
    simpa using (ha.pow (Module.finrank ℝ E)).inv₀ (by simp)
  have hd := integral_sq_dilation_sub_tendsto (K := K) hf ha0 ha
  have hupper : Tendsto (fun k =>
      2 * ((a k ^ Module.finrank ℝ E)⁻¹ * ∫ x, ‖g k x - f x‖ ^ 2 ∂μ) +
      2 * (∫ x in K, ‖f (a k • x) - f x‖ ^ 2 ∂μ)) atTop (𝓝 0) := by
    simpa using ((hcoef.mul hgf).const_mul 2).add (hd.const_mul 2)
  apply squeeze_zero (fun k => integral_nonneg fun x => sq_nonneg _) _ hupper
  intro k
  have hiu : Integrable (fun x => ‖g k (a k • x) - f (a k • x)‖ ^ 2) μ :=
    (memLp_comp_dilation ((hg k).sub hf) (ha0 k).ne').norm.integrable_sq
  have hiv : Integrable (fun x => ‖f (a k • x) - f x‖ ^ 2) μ :=
    ((memLp_comp_dilation hf (ha0 k).ne').sub hf).norm.integrable_sq
  have hit : Integrable (fun x => ‖g k (a k • x) - f x‖ ^ 2) μ :=
    ((memLp_comp_dilation (hg k) (ha0 k).ne').sub hf).norm.integrable_sq
  have hp : ∀ x, ‖g k (a k • x) - f x‖ ^ 2 ≤
      2 * ‖g k (a k • x) - f (a k • x)‖ ^ 2 + 2 * ‖f (a k • x) - f x‖ ^ 2 := by
    intro x
    have hn := norm_sub_le (g k (a k • x)) (f (a k • x))
    have ht : ‖g k (a k • x) - f x‖ ≤ ‖g k (a k • x) - f (a k • x)‖ + ‖f (a k • x) - f x‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    nlinarith [norm_nonneg (g k (a k • x) - f x), norm_nonneg (g k (a k • x) - f (a k • x)),
      norm_nonneg (f (a k • x) - f x),
      sq_nonneg (‖g k (a k • x) - f (a k • x)‖ - ‖f (a k • x) - f x‖)]
  have hi := integral_mono (μ := μ.restrict K) hit.restrict
    ((hiu.restrict.const_mul 2).add (hiv.restrict.const_mul 2)) hp
  rw [integral_add' (hiu.restrict.const_mul 2) (hiv.restrict.const_mul 2),
    integral_const_mul, integral_const_mul] at hi
  have hfull := integral_mono_measure (μ := μ.restrict K) Measure.restrict_le_self
    (Eventually.of_forall fun x => sq_nonneg ‖g k (a k • x) - f (a k • x)‖) hiu
  rw [integral_sq_dilation μ (fun x => g k x - f x) (ha0 k)] at hfull
  linarith
end HitAndRun.Geometry
