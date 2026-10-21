module
import HitAndRun.Geometry.ConvexPoincareFinite
open HitAndRun.Sobolev

example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) : K.poincareConstant < ⊤ :=
  K.poincareConstant_lt_top_convex hc

example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) : K.IsPoincareConstant K.poincareConstant :=
  K.poincareConstant_admissible_of_lt_top (K.poincareConstant_lt_top_convex hc)

example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) :
    ‖K.centeredCovarianceOperator‖ ≤ K.poincareConstant.toReal :=
  K.norm_centeredCovarianceOperator_le (K.poincareConstant_lt_top_convex hc)

#print axioms HitAndRun.Geometry.affine_segment_sq_sub_le
#print axioms HitAndRun.Geometry.half_segment_sq_sub_le
#print axioms HitAndRun.Geometry.segment_sq_sub_le_half_energies
#print axioms HitAndRun.Geometry.convex_half_homothety_integral_le
#print axioms HitAndRun.Geometry.integrable_half_homothety_slices
#print axioms HitAndRun.Geometry.integral_convex_half_homothety_le
#print axioms HitAndRun.Geometry.convex_half_difference_integral_le
#print axioms HitAndRun.Geometry.variance_le_four_half_difference_bound
#print axioms HitAndRun.Geometry.convex_smooth_variance_le
#print axioms BoundedOpenDomain.isPoincareConstant_of_smooth_bound
#print axioms BoundedOpenDomain.poincareConstant_lt_top_of_smooth_bound
#print axioms BoundedOpenDomain.poincareConstant_lt_top_convex_of_inner_ball
#print axioms BoundedOpenDomain.poincareConstant_lt_top_convex
#print axioms BoundedOpenDomain.poincareConstant_ne_top_convex

example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) : 0 < K.poincareConstant.toReal :=
  K.poincareConstant_toReal_pos_convex hc
#print axioms BoundedOpenDomain.poincareConstant_toReal_pos_convex
