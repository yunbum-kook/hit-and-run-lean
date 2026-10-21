module
public import HitAndRun.Geometry.WeightedPoincareMedian
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
@[expose] public section
namespace HitAndRun.Geometry
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem contDiff_signedSquare : ContDiff ℝ 1 signedSquare := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (hasDerivAt_signedSquare x).differentiableAt, ?_⟩
  have he : deriv signedSquare = fun x => 2 * |x| := funext fun x =>
    (hasDerivAt_signedSquare x).deriv
  rw [he]
  exact continuous_const.mul continuous_abs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- C1 specialization sufficient for the source locally Lipschitz estimate. -/
def C1WeightedL1Bound (μ : Measure E) (w : E → ℝ) (A : ℝ) : Prop :=
  ∀ g : E → ℝ, ContDiff ℝ 1 g → IsMedian μ g 0 → Integrable g μ →
    Integrable (fun x => w x * ‖fderiv ℝ g x‖) μ →
    (∫ x, |g x| ∂μ) ≤ A * ∫ x, w x * ‖fderiv ℝ g x‖ ∂μ

theorem variance_bound_of_C1WeightedL1 [IsProbabilityMeasure μ] {f w : E → ℝ} {m A : ℝ}
    (hweighted : C1WeightedL1Bound μ w A) (hf : ContDiff ℝ 1 f)
    (hmed : IsMedian μ f m) (hfL2 : MemLp f 2 μ)
    (hgrad : MemLp (fun x => w x * ‖fderiv ℝ f x‖) 2 μ) :
    variance f μ ≤ 4 * A ^ 2 * ∫ x, w x ^ 2 * ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  let g := fun x => signedSquare (f x - m)
  have hd : Differentiable ℝ g := fun x =>
    (hasFDerivAt_signedSquare_sub (hf.differentiable (by norm_num) x).hasFDerivAt m).differentiableAt
  have hu : MemLp (fun x => f x - m) 2 μ := hfL2.sub (memLp_const m)
  have hi : Integrable g μ := by
    apply (integrable_norm_iff hd.continuous.aestronglyMeasurable).mp
    simpa only [g, Real.norm_eq_abs, abs_signedSquare] using hu.integrable_sq
  have hp : Integrable (fun x => |f x - m| * (w x * ‖fderiv ℝ f x‖)) μ :=
    hu.abs.integrable_mul hgrad
  have he : (fun x => w x * ‖fderiv ℝ g x‖) =
      fun x => 2 * (|f x - m| * (w x * ‖fderiv ℝ f x‖)) := by
    funext x
    rw [norm_fderiv_signedSquare_sub (hf.differentiable (by norm_num) x) m]
    ring
  have hig : Integrable (fun x => w x * ‖fderiv ℝ g x‖) μ := by
    rw [he]; exact hp.const_mul 2
  have hL := hweighted g (contDiff_signedSquare.comp (hf.sub contDiff_const)) hmed.signedSquare_sub hi hig
  apply variance_bound_of_signedSquare_L1 hfL2 hgrad
  rw [he] at hL
  simpa only [g, mul_assoc] using hL
end HitAndRun.Geometry
