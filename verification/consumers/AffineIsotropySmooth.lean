import HitAndRun.Geometry.CovarianceAffineTransportIsotropy
import HitAndRun.Geometry.CovarianceAffineTransportSmoothPI
noncomputable section
open MeasureTheory ProbabilityTheory HitAndRun.Sobolev
open HitAndRun.Sobolev.BoundedOpenDomain
variable {n : ℕ} [NeZero n]
example (K : BoundedOpenDomain n) (i : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), x i ∂uniformMeasure K.whitenedDomain.carrier) = 0 :=
  K.whitenedDomain_coordinate_mean i
example (K : BoundedOpenDomain n) (i j : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂uniformMeasure K.whitenedDomain.carrier) =
      if i = j then 1 else 0 := K.whitenedDomain_coordinate_secondMoment i j
example (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ (⊤ : ℕ∞) f →
      variance f (K.ambient.restrict K.carrier) ≤
        C * ∫ x in K.carrier, ‖fderiv ℝ f x‖ ^ 2 ∂K.ambient) :
    K.IsPoincareConstant (ENNReal.ofReal C) := K.isPoincareConstant_of_smooth_bound_convex hc hC hbound
#print axioms uniform_integrable_coordinate
#print axioms uniform_integrable_coordinate_product
#print axioms whitenedDomain_coordinate_mean
#print axioms whitenedDomain_coordinate_secondMoment
#print axioms isPoincareConstant_of_smooth_bound_convex
