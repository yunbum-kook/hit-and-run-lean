module
public import HitAndRun.Geometry.WeightedPoincareRadial
public import HitAndRun.External.EllipticPDE.Analysis.PoincareInequality
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fundamental theorem of calculus and Cauchy--Schwarz on an affine segment. -/
theorem affine_segment_sq_sub_le (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (x y : E) {a b : ℝ} (hab : a ≤ b) :
    (f ((1-b) • y + b • x) - f ((1-a) • y + a • x)) ^ 2 ≤
      (b-a) * ‖x-y‖ ^ 2 *
        ∫ t in a..b, ‖fderiv ℝ f ((1-t) • y + t • x)‖ ^ 2 := by
  let p : ℝ → E := fun t => (1-t) • y + t • x
  have hp : Continuous p := by dsimp [p]; fun_prop
  have hd : ∀ t : ℝ, HasDerivAt (fun s => f (p s))
      (fderiv ℝ f (p t) (x-y)) t := by
    intro t
    apply ((hf.differentiable (by norm_num)) (p t)).hasFDerivAt.comp_hasDerivAt t
    convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const y).add
      ((hasDerivAt_id t).smul_const x) using 1 <;> simp [p, sub_eq_add_neg, add_comm, Pi.add_def]
  let B : ℝ → ℝ := fun t => ‖x-y‖ * ‖fderiv ℝ f (p t)‖
  have hB : Continuous B := continuous_const.mul
    (((hf.continuous_fderiv (by norm_num)).comp hp).norm)
  have hFTC : ‖f (p b) - f (p a)‖ ≤ ∫ t in a..b, B t := by
    exact norm_sub_le_integral_of_norm_deriv_le_of_le hab
      ((hf.continuous.comp hp).continuousOn)
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
      (Eventually.of_forall fun t _ => by
        change ‖deriv (fun s => f (p s)) t‖ ≤ B t
        rw [(hd t).deriv]
        simpa only [B, mul_comm] using (fderiv ℝ f (p t)).le_opNorm (x-y))
      (hB.intervalIntegrable a b)
  have hcs := EllipticPdes.Analysis.sq_intervalIntegral_le hab hB.continuousOn
  have hs : (f (p b) - f (p a)) ^ 2 ≤ (∫ t in a..b, B t) ^ 2 := by
    have hnonneg := (norm_nonneg (f (p b) - f (p a))).trans hFTC
    simpa only [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg _) hnonneg).2 hFTC
  have heq : (∫ t in a..b, B t ^ 2) = ‖x-y‖ ^ 2 *
      ∫ t in a..b, ‖fderiv ℝ f (p t)‖ ^ 2 := by
    simp only [B, mul_pow]
    exact intervalIntegral.integral_const_mul _ _
  rw [heq] at hcs
  exact hs.trans (by simpa only [mul_assoc] using hcs)

/-- Half-segment energy bound, parameterized toward the endpoint `x`. -/
theorem half_segment_sq_sub_le (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (x y : E) :
    (f x - f ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • x)) ^ 2 ≤
      (1 / 2 : ℝ) * ‖x-y‖ ^ 2 *
        ∫ t in Ioo (1 / 2 : ℝ) 1, ‖fderiv ℝ f ((1-t) • y + t • x)‖ ^ 2 := by
  have h := affine_segment_sq_sub_le f hf x y (a := (1/2 : ℝ)) (b := 1) (by norm_num)
  norm_num only [sub_self, zero_smul, one_smul, zero_add] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (1/2 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] at h
  convert h using 1

/-- Two half-segment estimates control the difference of the endpoints. -/
theorem segment_sq_sub_le_half_energies (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (x y : E) :
    (f x - f y) ^ 2 ≤ ‖x-y‖ ^ 2 *
      ((∫ t in Ioo (1 / 2 : ℝ) 1, ‖fderiv ℝ f ((1-t) • y + t • x)‖ ^ 2) +
       (∫ t in Ioo (1 / 2 : ℝ) 1, ‖fderiv ℝ f ((1-t) • x + t • y)‖ ^ 2)) := by
  have hx := half_segment_sq_sub_le f hf x y
  have hy := half_segment_sq_sub_le f hf y x
  rw [norm_sub_rev y x, add_comm ((1/2 : ℝ) • x) ((1/2 : ℝ) • y)] at hy
  nlinarith [sq_nonneg (f x + f y - 2 * f ((1/2 : ℝ) • y + (1/2 : ℝ) • x))]
end HitAndRun.Geometry
