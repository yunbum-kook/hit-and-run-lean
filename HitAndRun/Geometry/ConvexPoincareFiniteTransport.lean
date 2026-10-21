module
public import HitAndRun.Geometry.ConvexCovarianceRadius
public import HitAndRun.Geometry.WeightedPoincareRadialBound
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The half-segment avoids the singularity in the affine Haar Jacobian. -/
theorem convex_half_homothety_integral_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hb : Bornology.IsBounded K) (hc : Convex ℝ K)
    {y : E} (hy : y ∈ K) {h : E → ℝ} (hh : Continuous h) (hpos : ∀ x, 0 ≤ h x)
    {a : ℝ} (ha : a ∈ Ioo (1/2 : ℝ) 1) :
    (∫ x in K, h ((1-a) • y + a • x) ∂μ) ≤
      ((1/2 : ℝ) ^ Module.finrank ℝ E)⁻¹ * ∫ x in K, h x ∂μ := by
  have hhalf : (0 : ℝ) < (1/2 : ℝ)^Module.finrank ℝ E := pow_pos (by norm_num) _
  have hpow : (1/2 : ℝ)^Module.finrank ℝ E ≤ a^Module.finrank ℝ E :=
    pow_le_pow_left₀ (by norm_num) ha.1.le _
  have hi := convex_affine_homothety_integral_le μ hc hy
    (lt_trans (by norm_num) ha.1) ha.2.le (continuous_integrableOn_bounded μ hb hh) hpos
  have hn : 0 ≤ ∫ x in K, h ((1-a) • y + a • x) ∂μ := integral_nonneg fun _ => hpos _
  have hh' := (mul_le_mul_of_nonneg_right hpow hn).trans hi
  exact (le_inv_mul_iff₀ hhalf).mpr hh'

/-- Integrable half-segment slices for continuous observables on bounded domains. -/
theorem integrable_half_homothety_slices (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hb : Bornology.IsBounded K) (y : E) {h : E → ℝ} (hh : Continuous h) :
    IntegrableOn (fun a => ∫ x in K, h ((1-a) • y + a • x) ∂μ)
      (Ioo (1/2 : ℝ) 1) volume := by
  have hjc : Continuous (fun p : ℝ × E => h ((1-p.1) • y + p.1 • p.2)) := by fun_prop
  have hj : Integrable (fun p : ℝ × E => h ((1-p.1) • y + p.1 • p.2))
      ((volume.restrict (Ioo (1/2 : ℝ) 1)).prod (μ.restrict K)) := by
    rw [Measure.prod_restrict]
    exact (hjc.continuousOn.integrableOn_compact
      (isCompact_Icc.prod hb.isCompact_closure)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self subset_closure)
  exact hj.integral_prod_left

/-- A finite dimension-exponential bound for all half-segment averages. -/
theorem integral_convex_half_homothety_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hb : Bornology.IsBounded K) (hc : Convex ℝ K)
    {y : E} (hy : y ∈ K) {h : E → ℝ} (hh : Continuous h) (hpos : ∀ x, 0 ≤ h x) :
    (∫ a in Ioo (1/2 : ℝ) 1, ∫ x in K, h ((1-a) • y + a • x) ∂μ) ≤
      ((1/2 : ℝ) ^ Module.finrank ℝ E)⁻¹ * ∫ x in K, h x ∂μ := by
  let C : ℝ := ((1/2 : ℝ) ^ Module.finrank ℝ E)⁻¹ * ∫ x in K, h x ∂μ
  have hC : 0 ≤ C := mul_nonneg (by positivity) (integral_nonneg hpos)
  have hbnd := integral_mono_ae (integrable_half_homothety_slices μ hb y hh)
    (integrable_const C) ((ae_restrict_mem measurableSet_Ioo).mono fun a ha =>
      convex_half_homothety_integral_le μ hb hc hy hh hpos ha)
  have he : (∫ _a in Ioo (1/2 : ℝ) 1, C) = (1/2 : ℝ) * C := by
    norm_num [integral_const]
  rw [he] at hbnd
  exact hbnd.trans (by dsimp [C] at *; nlinarith)

end HitAndRun.Geometry
