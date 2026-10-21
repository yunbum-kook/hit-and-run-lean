module
public import HitAndRun.Geometry.WeightedPoincareLipschitzGraph
public import HitAndRun.Geometry.WeightedPoincareLipschitzLimit
public import HitAndRun.Geometry.WeightedPoincareMedianH1Density
public import HitAndRun.Sobolev.WeightedPoincareTransferEnergy
public import HitAndRun.Geometry.MedianL1Minimality
public import HitAndRun.External.Dikin.Probability.ProbabilityMedian
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory EllipticPdes EllipticPdes.H1Graph Set Filter HitAndRun.Sobolev
open scoped Topology ENNReal RealInnerProductSpace
variable {n : ℕ} [NeZero n]

/-- Full ambient locally-Lipschitz class transfer from a smooth weighted L1
inequality. The minimizing center is explicit for combination with median minimality. -/
theorem locallyLipschitz_center_bound_of_smooth (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball 0 r ⊆ K.carrier) {A m : ℝ}
    (hbound : ∀ u : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) u →
      ∃ z : ℝ, (∫ x in K.carrier, ‖u x - z‖ ∂K.ambient) ≤
        A * ∫ x in K.carrier, K.boundaryDistance x * ‖gradient u x‖ ∂K.ambient)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f)
    (hmin : ∀ z : ℝ, (∫ x in K.carrier, ‖f x - m‖ ∂K.ambient) ≤
      ∫ x in K.carrier, ‖f x - z‖ ∂K.ambient) :
    (∫ x in K.carrier, ‖f x - m‖ ∂K.ambient) ≤
      A * ∫ x in K.carrier, K.boundaryDistance x * ‖gradient f x‖ ∂K.ambient := by
  letI : IsProbabilityMeasure (K.ambient.restrict K.carrier) := by
    rw [K.measure_eq_uniform]
    exact uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  let U : W12 K.ambient K.carrier := locallyLipschitzH1 K.isBounded K.isOpen f hf
  obtain ⟨u, hu, huf, hug⟩ := exists_smooth_W12_approximation K.isOpen hc hr hball U
  have huf' : Tendsto (fun k => ∫ x in K.carrier, ‖u k x - f x‖ ^ 2 ∂K.ambient) atTop (𝓝 0) := by
    convert huf using 1
    funext k
    apply integral_congr_ae
    filter_upwards [locallyLipschitzGraph_fn (μ := K.ambient) K.isBounded K.isOpen f hf] with x hx
    simp only [U, locallyLipschitzH1] at *
    rw [hx]
  have hug' : Tendsto (fun k => ∫ x in K.carrier, ‖gradient (u k) x - gradient f x‖ ^ 2 ∂K.ambient)
      atTop (𝓝 0) := by
    convert hug using 1
    funext k
    apply integral_congr_ae
    filter_upwards [locallyLipschitzGraph_grad (μ := K.ambient) K.isBounded K.isOpen f hf] with x hx
    simp only [U, locallyLipschitzH1] at *
    rw [hx]
  have hfm := continuous_memLp_bounded_restrict (μ := K.ambient) K.isBounded K.isOpen.measurableSet hf.continuous
  have hum := fun k => continuous_memLp_bounded_restrict (μ := K.ambient) K.isBounded K.isOpen.measurableSet (hu k).continuous
  have he := tendsto_integral_norm_sub_of_sq hfm hum huf'
  obtain ⟨D, hD0, hD⟩ := K.boundaryDistance_bounded
  have henergy := tendsto_integral_weighted_norm_of_sq
    (locallyLipschitz_gradient_memLp (μ := K.ambient) K.isBounded K.isOpen.measurableSet hf)
    (fun k => smooth_gradient_memLp (μ := K.ambient) K.isBounded K.isOpen (u k) (hu k))
    K.boundaryDistance_memLp_top (Eventually.of_forall fun _ => Metric.infDist_nonneg)
    ((ae_restrict_mem K.isOpen.measurableSet).mono fun x hx => hD x hx) hug'
  exact minimizing_center_bound_of_L1_limit (hfm.integrable (by norm_num))
    (fun k => (hum k).integrable (by norm_num)) hmin he henergy (fun k => hbound (u k) (hu k))

/-- The source's full ambient locally-Lipschitz class follows from the smooth
center inequality, with no integrability hypothesis and with the same constant. -/
theorem locallyLipschitz_exists_center_bound_of_smooth (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball 0 r ⊆ K.carrier) {A : ℝ}
    (hbound : ∀ u : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) u →
      ∃ z : ℝ, (∫ x in K.carrier, ‖u x - z‖ ∂K.ambient) ≤
        A * ∫ x in K.carrier, K.boundaryDistance x * ‖gradient u x‖ ∂K.ambient)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f) :
    ∃ m : ℝ, (∫ x in K.carrier, ‖f x - m‖ ∂K.ambient) ≤
      A * ∫ x in K.carrier, K.boundaryDistance x * ‖gradient f x‖ ∂K.ambient := by
  letI : IsProbabilityMeasure (K.ambient.restrict K.carrier) := by
    rw [K.measure_eq_uniform]
    exact uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  obtain ⟨m, hm⟩ := DikinD2.Cheeger.exists_probability_median
    (K.ambient.restrict K.carrier) f hf.continuous.measurable
  have hi := (continuous_memLp_bounded_restrict (μ := K.ambient)
    K.isBounded K.isOpen.measurableSet hf.continuous).integrable (by norm_num)
  refine ⟨m, locallyLipschitz_center_bound_of_smooth K hc hr hball hbound f hf ?_⟩
  intro z
  simpa only [Real.norm_eq_abs] using
    IsMedian.integral_abs_sub_le (show IsMedian (K.ambient.restrict K.carrier) f m from hm) hi z
end HitAndRun.Geometry
