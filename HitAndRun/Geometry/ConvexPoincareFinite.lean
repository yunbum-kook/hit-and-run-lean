module
public import HitAndRun.Geometry.ConvexPoincareFiniteSmooth
public import HitAndRun.Geometry.ConvexPoincareFiniteDensity
public import HitAndRun.Geometry.CovarianceNondegenerate
public import HitAndRun.Sobolev.TranslationConstants
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n : ℕ} [NeZero n]

/-- Convex bounded domains with an inner ball have a finite actual W12 PI constant.
The proof supplies a dimension-exponential smooth estimate and passes through genuine density. -/
theorem poincareConstant_lt_top_convex_of_inner_ball (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ K.carrier) :
    K.poincareConstant < ⊤ := by
  let : IsProbabilityMeasure (K.ambient.restrict K.carrier) := by
    rw [K.measure_eq_uniform]
    exact uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  obtain ⟨R, hR, hnorm⟩ := K.isBounded.exists_pos_norm_le
  have hd : ∀ x ∈ K.carrier, ∀ y ∈ K.carrier, ‖x-y‖ ≤ 2*R := by
    intro x hx y hy
    exact (norm_sub_le x y).trans (by linarith [hnorm x hx, hnorm y hy])
  apply K.poincareConstant_lt_top_of_smooth_bound hc hr hball
    (C := 4 * (2*R)^2 * ((1/2 : ℝ)^Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))⁻¹)
    (by positivity)
  intro f hf
  exact Geometry.convex_smooth_variance_le K.ambient K.isBounded K.isOpen.measurableSet hc f
    (hf.of_le (by simp)) (by positivity) hd

/-- Every bounded nonempty open convex Euclidean domain has a finite *actual*
ordinary Poincare constant on its genuine weak Sobolev space. No PI assumption,
centroid condition, boundary smoothness, or zero-trace replacement is used. -/
theorem poincareConstant_lt_top_convex (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) : K.poincareConstant < ⊤ := by
  obtain ⟨x, hx⟩ := K.nonempty
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp K.isOpen x hx
  have h := (K.translate (-x)).poincareConstant_lt_top_convex_of_inner_ball
    (hc.translate (-x)) hr (K.translate_neg_inner_ball hball)
  simpa only [K.poincareConstant_translate] using h

/-- In particular, taking `toReal` cannot silently turn infinite CPI into zero. -/
theorem poincareConstant_ne_top_convex (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) : K.poincareConstant ≠ ⊤ :=
  (K.poincareConstant_lt_top_convex hc).ne

/-- The real-valued optimal CPI is strictly positive, as well as genuinely finite. -/
theorem poincareConstant_toReal_pos_convex (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) : 0 < K.poincareConstant.toReal := by
  obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
  have hp := K.centeredCovarianceOperator_inner_pos v hv
  have hle := K.centeredCovarianceOperator_quadratic_le (K.poincareConstant_lt_top_convex hc) v
  exact pos_of_mul_pos_left (hp.trans_le hle) (sq_nonneg ‖v‖)

end HitAndRun.Sobolev.BoundedOpenDomain
