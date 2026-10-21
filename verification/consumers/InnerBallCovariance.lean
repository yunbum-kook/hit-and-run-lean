module
import HitAndRun.Geometry.InnerBallCovariance
open MeasureTheory HitAndRun.Sobolev
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ K.carrier) :
    r^2 / (8 * (n : ℝ)) ≤ ‖K.centeredCovarianceOperator‖ :=
  K.innerBall_covariance_lower hr hball
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.uniform_ball_half_le
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.innerBall_le_centered_secondMoment
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.centered_secondMoment_le
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.innerBall_covariance_lower
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ K.carrier) :
    1 ≤ 8 * (n : ℝ) * ‖K.centeredCovarianceOperator‖ / r^2 :=
  K.one_le_innerBall_covariance_scale hr hball
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.innerBall_covariance_pos
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.one_le_innerBall_covariance_scale
