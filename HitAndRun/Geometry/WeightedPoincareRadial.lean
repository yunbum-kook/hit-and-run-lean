module
public import HitAndRun.Geometry.WeightedPoincareGeometry
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The genuine radial fundamental-theorem estimate, before change of variables
and Tonelli. No weighted Poincare inequality is assumed. -/
theorem radial_norm_sub_le_integral (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (x : E) {a : ℝ} (ha : a ≤ 1) :
    ‖f x - f (a • x)‖ ≤ ∫ t in a..1, ‖x‖ * ‖fderiv ℝ f (t • x)‖ := by
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (s • x)) (fderiv ℝ f (t • x) x) t := by
    intro t
    exact ((hf.differentiable (by norm_num)) (t • x)).hasFDerivAt.comp_hasDerivAt t
      (by simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const x)
  have hB : Continuous (fun t : ℝ => ‖x‖ * ‖fderiv ℝ f (t • x)‖) :=
    continuous_const.mul ((hf.continuous_fderiv (by norm_num)).comp
      (continuous_id.smul continuous_const)).norm
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le
    (f := fun t : ℝ => f (t • x)) (B := fun t => ‖x‖ * ‖fderiv ℝ f (t • x)‖) ha
    ((hf.continuous.comp (continuous_id.smul continuous_const)).continuousOn)
    (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
    (Eventually.of_forall fun t _ => by
      rw [(hd t).deriv]
      simpa only [mul_comm] using (fderiv ℝ f (t • x)).le_opNorm x)
    (hB.intervalIntegrable a 1)
  simpa only [one_smul] using h
end HitAndRun.Geometry
