module
import HitAndRun.Geometry.ConvexCovarianceRadius
open MeasureTheory ProbabilityTheory HitAndRun.Sobolev
open scoped ENNReal
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier)
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K.carrier)
    (hfin : K.poincareConstant < ⊤) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K.carrier) :
    ‖x‖ ≤ 6 * (n : ℝ) * Real.sqrt K.poincareConstant.toReal :=
  K.norm_le_poincare_radius hc hzero hfin hx
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K.carrier) :
    ‖x - K.barycenter‖^2 ≤ 8 * (n : ℝ)^2 * ‖K.centeredCovarianceOperator‖ :=
  K.norm_sub_barycenter_sq_le hc hx
#print axioms HitAndRun.Geometry.convex_affine_homothety_integral_le
#print axioms BoundedOpenDomain.centeredProjection_memLp
#print axioms BoundedOpenDomain.integral_centeredProjection
#print axioms BoundedOpenDomain.integral_centeredProjection_sq
#print axioms BoundedOpenDomain.integral_centeredProjection_affine_sq
#print axioms BoundedOpenDomain.centeredProjection_sq_le
#print axioms BoundedOpenDomain.norm_sub_barycenter_sq_le
#print axioms BoundedOpenDomain.norm_sub_barycenter_le
#print axioms BoundedOpenDomain.norm_le_covariance_radius
#print axioms BoundedOpenDomain.norm_le_poincare_radius
