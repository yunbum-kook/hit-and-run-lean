module
public import HitAndRun.Geometry.WeightedPoincareMedianGraphDensity
public import HitAndRun.Sobolev.ImprovedPoincareLimit
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory ProbabilityTheory EllipticPdes EllipticPdes.H1Graph Filter
open scoped Topology RealInnerProductSpace
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

/-- Transfer an actual global smooth PI estimate to all actual weak H1 graphs.
The analytic smooth estimate is an explicit hypothesis. -/
theorem isPoincareConstant_of_smooth_bound
    (hc : Convex ℝ K.carrier) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ K.carrier)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f →
      variance f (K.ambient.restrict K.carrier) ≤
        C * ∫ x in K.carrier, ‖fderiv ℝ f x‖ ^ 2 ∂K.ambient) :
    K.IsPoincareConstant (ENNReal.ofReal C) := by
  intro U
  obtain ⟨f, hf, hlim⟩ := HitAndRun.Geometry.exists_smoothGraph_tendsto_W12
    K.isBounded K.isOpen hc hr hball U
  let v (k : ℕ) := smoothGraph (μ := K.ambient) K.isBounded K.isOpen (f k) (hf k)
  have hb (k : ℕ) : variance (fnL (v k)) (K.ambient.restrict K.carrier) ≤
      C * ‖gradL (v k)‖ ^ 2 := by
    rw [variance_congr (smoothGraph_fn (μ := K.ambient) K.isBounded K.isOpen (f k) (hf k))]
    convert hbound (f k) (hf k) using 1
    congr 1
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [smoothGraph_grad (μ := K.ambient) K.isBounded K.isOpen (f k) (hf k)] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
    simp [gradient]
  have hreal : variance (fnL U.val) (K.ambient.restrict K.carrier) ≤
      C * ‖gradL U.val‖ ^ 2 :=
    le_of_tendsto_of_tendsto
      (K.continuous_lp_variance.tendsto _ |>.comp (fnL.continuous.tendsto _ |>.comp hlim))
      (tendsto_const_nhds.mul ((gradL.continuous.tendsto _ |>.comp hlim).norm.pow 2))
      (Filter.Eventually.of_forall hb)
  apply (ENNReal.toReal_le_toReal (K.varianceEnergy_ne_top U)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (K.gradientEnergy_ne_top U))).mp
  simpa only [varianceEnergy, variance, gradientEnergy, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC, ENNReal.toReal_ofReal (sq_nonneg _)] using hreal

/-- Finiteness follows once a finite smooth estimate has been established. -/
theorem poincareConstant_lt_top_of_smooth_bound
    (hc : Convex ℝ K.carrier) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ K.carrier)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f →
      variance f (K.ambient.restrict K.carrier) ≤
        C * ∫ x in K.carrier, ‖fderiv ℝ f x‖ ^ 2 ∂K.ambient) :
    K.poincareConstant < ⊤ :=
  lt_of_le_of_lt (K.poincareConstant_le
    (K.isPoincareConstant_of_smooth_bound hc hr hball hC hbound)) ENNReal.ofReal_lt_top
end HitAndRun.Sobolev.BoundedOpenDomain

#print axioms HitAndRun.Sobolev.BoundedOpenDomain.isPoincareConstant_of_smooth_bound
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.poincareConstant_lt_top_of_smooth_bound
