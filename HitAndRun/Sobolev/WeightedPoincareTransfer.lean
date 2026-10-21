module
public import HitAndRun.Sobolev.WeightedPoincareTransferEnergy
public import HitAndRun.Geometry.WeightedPoincareMedianGraphDensity
public import HitAndRun.Geometry.WeightedPoincareMedian
public import HitAndRun.External.Dikin.Probability.ProbabilityMedian
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory ProbabilityTheory EllipticPdes EllipticPdes.H1Graph Filter Set
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace BoundedOpenDomain
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

theorem weightedGradientEnergy_smooth (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    (K.weightedGradientEnergy (smoothH1 K.isBounded K.isOpen f hf)).toReal =
      ∫ x, K.boundaryDistance x ^ 2 * ‖fderiv ℝ f x‖ ^ 2
        ∂K.ambient.restrict K.carrier := by
  rw [K.weightedGradientEnergy_eq_norm, ENNReal.toReal_ofReal (sq_nonneg _),
    ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [K.boundaryMultiplier_ae (gradL (smoothH1 K.isBounded K.isOpen f hf).val),
    smoothGraph_grad (μ := K.ambient) K.isBounded K.isOpen f hf] with x hx hg
  rw [real_inner_self_eq_norm_sq, hx]
  change ‖K.boundaryDistance x • gradL (smoothGraph K.isBounded K.isOpen f hf) x‖ ^ 2 = _
  rw [hg, norm_smul, mul_pow]
  simp [gradient, Real.norm_eq_abs, sq_abs]

theorem smooth_variance_of_weightedL1 {A : ℝ}
    (hL1 : Geometry.WeightedL1Bound (K.ambient.restrict K.carrier) K.boundaryDistance A)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    variance (fnL (smoothGraph (μ := K.ambient) K.isBounded K.isOpen f hf))
      (K.ambient.restrict K.carrier) ≤
      4 * A ^ 2 * (K.weightedGradientEnergy (smoothH1 K.isBounded K.isOpen f hf)).toReal := by
  letI : IsProbabilityMeasure (K.ambient.restrict K.carrier) := by
    rw [K.measure_eq_uniform]
    exact uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  obtain ⟨m, hm⟩ := DikinD2.Cheeger.exists_probability_median
    (K.ambient.restrict K.carrier) f hf.continuous.measurable
  have hg : MemLp (fun x => K.boundaryDistance x * ‖fderiv ℝ f x‖) 2
      (K.ambient.restrict K.carrier) := by
    have hg : MemLp (fun x => K.boundaryDistance x • ‖gradient f x‖) 2
        (K.ambient.restrict K.carrier) := K.boundaryDistance_memLp_top.smul
      (smooth_gradient_memLp (μ := K.ambient) K.isBounded K.isOpen f hf).norm
    simpa [smul_eq_mul, gradient] using hg
  rw [variance_congr (smoothGraph_fn K.isBounded K.isOpen f hf),
    K.weightedGradientEnergy_smooth]
  exact Geometry.variance_bound_of_weightedL1 hL1 (hf.differentiable (by simp)) hm
    (continuous_memLp_bounded_restrict K.isBounded K.isOpen.measurableSet hf.continuous) hg

/-- Conditional transfer of a genuine weighted L1 estimate to the actual W12
inequality. Smooth density and bounded multiplication discharge the limit step. -/
theorem improvedPoincare_of_weightedL1 {A r : ℝ}
    (hc : Convex ℝ K.carrier) (hr : 0 < r) (hball : Metric.ball 0 r ⊆ K.carrier)
    (hL1 : Geometry.WeightedL1Bound (K.ambient.restrict K.carrier) K.boundaryDistance A) :
    K.IsImprovedPoincareConstant (ENNReal.ofReal (4 * A ^ 2)) := by
  intro u
  obtain ⟨f, hf, hconv⟩ := Geometry.exists_smoothGraph_tendsto_W12
    K.isBounded K.isOpen hc hr hball u
  let us : ℕ → K.H1 := fun k => smoothH1 K.isBounded K.isOpen (f k) (hf k)
  have hconv' : Tendsto (fun k => (us k).val) atTop (𝓝 u.val) := hconv
  have hvar := (K.continuous_lp_variance.tendsto (fnL u.val)).comp
    (fnL.continuous.tendsto u.val |>.comp hconv)
  have henergy := K.weightedGradientEnergy_tendsto hconv'
  have hbound : variance (fnL u.val) (K.ambient.restrict K.carrier) ≤
      4 * A ^ 2 * (K.weightedGradientEnergy u).toReal :=
    le_of_tendsto_of_tendsto hvar (tendsto_const_nhds.mul henergy)
      (Filter.Eventually.of_forall fun k => K.smooth_variance_of_weightedL1 hL1 (f k) (hf k))
  apply (ENNReal.toReal_le_toReal (K.varianceEnergy_ne_top u)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (K.weightedGradientEnergy_ne_top u))).mp
  simpa only [varianceEnergy, variance, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * A ^ 2)] using hbound

theorem improvedPoincareConstant_le_of_weightedL1 {A r : ℝ}
    (hc : Convex ℝ K.carrier) (hr : 0 < r) (hball : Metric.ball 0 r ⊆ K.carrier)
    (hL1 : Geometry.WeightedL1Bound (K.ambient.restrict K.carrier) K.boundaryDistance A) :
    K.improvedPoincareConstant ≤ ENNReal.ofReal (4 * A ^ 2) :=
  K.improvedPoincareConstant_le (K.improvedPoincare_of_weightedL1 hc hr hball hL1)
end BoundedOpenDomain
end HitAndRun.Sobolev
