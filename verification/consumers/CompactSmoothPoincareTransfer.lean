module
import HitAndRun.Geometry.CompactSmoothPoincareTransferConvex
open HitAndRun.Sobolev MeasureTheory ProbabilityTheory

example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) {C : ℝ}
    (h : K.CompactSmoothPoincareBound C) (hC : 0 ≤ C) (hc : Convex ℝ K.carrier) :
    K.IsPoincareConstant (ENNReal.ofReal C) := h.isPoincareConstant hC hc

example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) {C : ℝ}
    (h : K.CompactSmoothPoincareBound C) (hC : 0 ≤ C) (hc : Convex ℝ K.carrier) :
    K.poincareConstant.toReal ≤ C := h.poincareConstant_toReal_le hC hc

example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) {C : ℝ}
    (h : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      variance f (K.ambient.restrict K.carrier) ≤
        C * ∫ x in K.carrier, ‖fderiv ℝ f x‖^2 ∂K.ambient)
    (hC : 0 ≤ C) (hc : Convex ℝ K.carrier) :
    K.poincareConstant ≤ ENNReal.ofReal C :=
  BoundedOpenDomain.CompactSmoothPoincareBound.poincareConstant_le h hC hc

#print axioms HitAndRun.Geometry.exists_compactSmooth_eq_near_bounded
#print axioms BoundedOpenDomain.CompactSmoothPoincareBound
#print axioms BoundedOpenDomain.CompactSmoothPoincareBound.smooth_bound
#print axioms BoundedOpenDomain.CompactSmoothPoincareBound.isPoincareConstant_of_inner_ball
#print axioms BoundedOpenDomain.CompactSmoothPoincareBound.poincareConstant_le_of_inner_ball
#print axioms BoundedOpenDomain.CompactSmoothPoincareBound.isPoincareConstant
#print axioms BoundedOpenDomain.CompactSmoothPoincareBound.poincareConstant_le
#print axioms BoundedOpenDomain.CompactSmoothPoincareBound.poincareConstant_toReal_le
