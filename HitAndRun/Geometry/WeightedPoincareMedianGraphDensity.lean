module
public import HitAndRun.Geometry.WeightedPoincareMedianH1Density
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Sobolev Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] [μ.Regular] {Ω : Set E}

lemma norm_sq_Lp_sub_eq_integral {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ν : Measure E} (u v : Lp F 2 ν) :
    ‖u - v‖^2 = ∫ x, ‖u x - v x‖^2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub u v] with x hx
  rw [hx, real_inner_self_eq_norm_sq, Pi.sub_apply]

lemma norm_sq_smoothGraph_sub (hb : Bornology.IsBounded Ω) (ho : IsOpen Ω)
    (f : E → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (U : H1Graph μ Ω) :
    ‖smoothGraph hb ho f hf - U‖^2 =
      (∫ x in Ω, ‖f x - fnL U x‖^2 ∂μ) +
      (∫ x in Ω, ‖gradient f x - gradL U x‖^2 ∂μ) := by
  rw [norm_sq_eq, map_sub, map_sub,
    norm_sq_Lp_sub_eq_integral, norm_sq_Lp_sub_eq_integral]
  congr 1
  · apply integral_congr_ae
    filter_upwards [smoothGraph_fn (μ := μ) hb ho f hf] with x hx
    rw [hx]
  · apply integral_congr_ae
    filter_upwards [smoothGraph_grad (μ := μ) hb ho f hf] with x hx
    rw [hx]

/-- Actual H1 graph convergence of global smooth restrictions on an arbitrary
bounded open convex body with an inner ball. No C1 boundary is assumed. -/
theorem exists_smoothGraph_tendsto_W12
    (hb : Bornology.IsBounded Ω) (ho : IsOpen Ω) (hc : Convex ℝ Ω)
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball (0 : E) r ⊆ Ω) (U : W12 μ Ω) :
    ∃ (f : ℕ → E → ℝ) (hf : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (f k)),
      Tendsto (fun k => smoothGraph hb ho (f k) (hf k)) atTop (𝓝 U.val) := by
  haveI : IsFiniteMeasure (μ.restrict Ω) := isFiniteMeasure_restrict.mpr
    (lt_of_le_of_lt (measure_mono subset_closure) hb.isCompact_closure.measure_lt_top).ne
  obtain ⟨f, hf, hfun, hgrad⟩ := exists_smooth_W12_approximation ho hc hr hball U
  refine ⟨f, hf, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hs : Tendsto (fun k => ‖smoothGraph hb ho (f k) (hf k) - U.val‖^2) atTop (𝓝 0) := by
    simpa only [norm_sq_smoothGraph_sub, add_zero] using hfun.add hgrad
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  change Tendsto (fun k => Real.sqrt (‖smoothGraph hb ho (f k) (hf k) - U.val‖^2)) atTop (𝓝 (Real.sqrt 0)) at ht
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using ht
end HitAndRun.Geometry
