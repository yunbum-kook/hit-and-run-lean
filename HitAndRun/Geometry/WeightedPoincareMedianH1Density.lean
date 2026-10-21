module
public import HitAndRun.Geometry.WeightedPoincareMedianMollifier
public import HitAndRun.Geometry.WeightedPoincareMedianSmooth
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory EllipticPdes EllipticPdes.H1Graph Set Filter
open scoped Topology Convolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] [μ.Regular] {Ω : Set E}

/-- Smooth restriction approximation of both genuine W12 components on a convex
body. The scalar and bump sequences only specify shrinking geometric margins;
there is no boundary regularity or abstract density assumption. -/
theorem exists_smooth_W12_component_approximation
    [IsFiniteMeasure (μ.restrict Ω)] (ho : IsOpen Ω) (hc : Convex ℝ Ω)
    {r : ℝ} (hball : Metric.ball (0 : E) r ⊆ Ω)
    {a : ℕ → ℝ} (ha0 : ∀ k, 0 < a k) (ha1 : ∀ k, a k < 1)
    (ha : Tendsto a atTop (𝓝 1)) (rho : ℕ → ContDiffBump (0 : E))
    (hrho : ∀ k, (rho k).rOut < (1 - a k) * r)
    (hr : Tendsto (fun k => (rho k).rOut) atTop (𝓝 0)) (U : W12 μ Ω) :
    ∃ f : ℕ → E → ℝ, (∀ k, ContDiff ℝ (⊤ : ℕ∞) (f k)) ∧
      Tendsto (fun k => ∫ x in Ω, ‖f k x - fnL U.val x‖^2 ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ x in Ω, ‖gradient (f k) x - gradL U.val x‖^2 ∂μ) atTop (𝓝 0) := by
  let f0 : E → ℝ := Ω.indicator (fnL U.val)
  let G0 : E → E := Ω.indicator (gradL U.val)
  have hf0 : MemLp f0 2 μ :=
    (memLp_indicator_iff_restrict ho.measurableSet.nullMeasurableSet).mpr (Lp.memLp _)
  have hG0 : MemLp G0 2 μ :=
    (memLp_indicator_iff_restrict ho.measurableSet.nullMeasurableSet).mpr (Lp.memLp _)
  let f : ℕ → E → ℝ := fun k x =>
    (f0 ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (rho k).normed μ) (a k • x)
  let G : ℕ → E → E := fun k x =>
    ((rho k).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] G0) (a k • x)
  have hfc : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (f k) := fun k =>
    (EllipticPdes.Embedding.contDiff_convolution_normed (rho k)
      (hf0.locallyIntegrable (by norm_num))).comp (contDiff_const.smul contDiff_id)
  have hft := integral_sq_zeroExtension_mollification_dilation_sub_tendsto
    ho.measurableSet (Lp.memLp (fnL U.val)) hr ha0 ha
  have hGt := integral_sq_zeroExtension_mollification_dilation_sub_tendsto
    ho.measurableSet (Lp.memLp (gradL U.val)) hr ha0 ha
  have hGL : ∀ k, MemLp (G k) 2 (μ.restrict Ω) := fun k =>
    (memLp_comp_dilation (memLp_mollification_two (rho k) hG0) (ha0 k).ne').restrict Ω
  have hGscaled := integral_sq_smul_approx_sub_tendsto
    (Lp.memLp (gradL U.val)) hGL hGt ha
  refine ⟨f, hfc, ?_, ?_⟩
  · simpa only [f, f0, EllipticPdes.Embedding.convolution_lsmul_comm f0] using hft
  · have he (k : ℕ) :
        (∫ x in Ω, ‖gradient (f k) x - gradL U.val x‖^2 ∂μ) =
        (∫ x in Ω, ‖a k • G k x - gradL U.val x‖^2 ∂μ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
      rw [show gradient (f k) x = a k • G k x from
        gradient_inward_mollified_W12 ho hc hball (ha0 k).le (ha1 k) (rho k) (hrho k) U hx]
    simpa only [he] using hGscaled
/-- Every actual W12 element on a finite-volume open convex body containing
an inner ball is approximated in both H1 components by global smooth functions. -/
theorem exists_smooth_W12_approximation
    [IsFiniteMeasure (μ.restrict Ω)] (ho : IsOpen Ω) (hc : Convex ℝ Ω)
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball (0 : E) r ⊆ Ω) (U : W12 μ Ω) :
    ∃ f : ℕ → E → ℝ, (∀ k, ContDiff ℝ (⊤ : ℕ∞) (f k)) ∧
      Tendsto (fun k => ∫ x in Ω, ‖f k x - fnL U.val x‖^2 ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ x in Ω, ‖gradient (f k) x - gradL U.val x‖^2 ∂μ) atTop (𝓝 0) := by
  let a : ℕ → ℝ := fun k => 1 - (1 / ((k : ℝ) + 1)) / 2
  let rho : ℕ → ContDiffBump (0 : E) := fun k => mollifier (show 0 < r / 4 by positivity) k
  have ha0 : ∀ k, 0 < a k := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hi : 1 / ((k : ℝ) + 1) ≤ 1 := (div_le_one hk).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
    dsimp [a]
    linarith
  have ha1 : ∀ k, a k < 1 := by
    intro k
    have hi : 0 < 1 / ((k : ℝ) + 1) := by positivity
    dsimp [a]
    linarith
  have ha : Tendsto a atTop (𝓝 1) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
    simpa [a] using h.const_sub 1
  have hmargin : ∀ k, (rho k).rOut < (1 - a k) * r := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    dsimp [rho, a]
    field_simp
    nlinarith
  exact exists_smooth_W12_component_approximation ho hc hball ha0 ha1 ha rho hmargin
    (tendsto_rOut_mollifier (show 0 < r / 4 by positivity)) U
end HitAndRun.Geometry
