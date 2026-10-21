module
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic
@[expose] public section

/-! The median/sign-square conversion for S08. The weighted L1 estimate remains
an explicit hypothesis here: this module does not prove source S07 or S08. -/
namespace HitAndRun.Geometry
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

def signedSquare (t : ℝ) : ℝ := t * |t|

@[simp] theorem abs_signedSquare (t : ℝ) : |signedSquare t| = t ^ 2 := by
  simp [signedSquare, abs_mul, ← sq, sq_abs]

@[simp] theorem signedSquare_neg_iff (t : ℝ) : signedSquare t < 0 ↔ t < 0 := by
  unfold signedSquare
  constructor
  · intro h; by_contra hn; exact (not_lt_of_ge (mul_nonneg (le_of_not_gt hn) (abs_nonneg t))) h
  · intro h; exact mul_neg_of_neg_of_pos h (abs_pos.mpr h.ne)

@[simp] theorem signedSquare_pos_iff (t : ℝ) : 0 < signedSquare t ↔ 0 < t := by
  unfold signedSquare
  constructor
  · intro h; by_contra hn; exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (abs_nonneg t))) h
  · intro h; exact mul_pos h (abs_pos.mpr h.ne')

/-- Strict-tail median conditions, including measures with atoms. -/
def IsMedian {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (m : ℝ) : Prop :=
  μ {x | f x < m} ≤ (1 / 2 : ℝ≥0∞) ∧ μ {x | m < f x} ≤ (1 / 2 : ℝ≥0∞)

theorem IsMedian.signedSquare_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {m : ℝ} (hm : IsMedian μ f m) :
    IsMedian μ (fun x => signedSquare (f x - m)) 0 := by
  simpa [IsMedian, sub_neg, sub_pos] using hm

/-- Unlike absolute value, the sign-preserving square is differentiable at zero. -/
theorem hasDerivAt_signedSquare (t : ℝ) : HasDerivAt signedSquare (2 * |t|) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · convert (hasDerivAt_id t).mul (hasDerivAt_abs_neg ht) using 1
    · rfl
    · simp [abs_of_neg ht]; ring
  · rw [hasDerivAt_iff_tendsto]
    have he : (fun y : ℝ => ‖y - 0‖⁻¹ * ‖signedSquare y - signedSquare 0 - (y - 0) • (2 * |(0 : ℝ)|)‖) =
        fun y => |y| := by
      funext y
      simp only [signedSquare, abs_zero, mul_zero, sub_zero, smul_zero, Real.norm_eq_abs, abs_mul, abs_abs]
      by_cases hy : y = 0
      · simp [hy]
      · field_simp [abs_ne_zero.mpr hy]
    rw [he]
    simpa using (continuous_abs.tendsto (0 : ℝ))
  · convert (hasDerivAt_id t).mul (hasDerivAt_abs_pos ht) using 1
    · rfl
    · simp [abs_of_pos ht]; ring

theorem hasFDerivAt_signedSquare_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E}
    (hf : HasFDerivAt f f' x) (m : ℝ) :
    HasFDerivAt (fun y => signedSquare (f y - m)) ((2 * |f x - m|) • f') x := by
  simpa only [Function.comp_def] using
    (hasDerivAt_signedSquare (f x - m)).comp_hasFDerivAt x (hf.sub_const m)

/-- Actual differential norm of the median sign-square, including on the zero set. -/
theorem norm_fderiv_signedSquare_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (m : ℝ) :
    ‖fderiv ℝ (fun y => signedSquare (f y - m)) x‖ = 2 * |f x - m| * ‖fderiv ℝ f x‖ := by
  rw [(hasFDerivAt_signedSquare_sub hf.hasFDerivAt m).fderiv, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * |f x - m|)]

/-- Integrated Cauchy-Schwarz absorption, proved by integrating the nonnegative
square (|u|-2Av)^2. All integrability assumptions are genuine L2 membership. -/
theorem weighted_square_absorption {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u v : α → ℝ} {A : ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (hL1 : (∫ x, u x ^ 2 ∂μ) ≤ 2 * A * ∫ x, |u x| * v x ∂μ) :
    (∫ x, u x ^ 2 ∂μ) ≤ 4 * A ^ 2 * ∫ x, v x ^ 2 ∂μ := by
  have hiu := hu.integrable_sq
  have hiv := hv.integrable_sq
  have hip : Integrable (fun x => |u x| * v x) μ := hu.abs.integrable_mul hv
  have he : (∫ x, (|u x| - 2 * A * v x) ^ 2 ∂μ) =
      (∫ x, u x ^ 2 ∂μ) - 4 * A * (∫ x, |u x| * v x ∂μ) +
        4 * A ^ 2 * (∫ x, v x ^ 2 ∂μ) := by
    have hp : (fun x => (|u x| - 2 * A * v x) ^ 2) =
        fun x => u x ^ 2 - 4 * A * (|u x| * v x) + 4 * A ^ 2 * v x ^ 2 := by
      funext x
      nlinarith [sq_abs (u x)]
    rw [hp]
    have his : Integrable (fun x => u x ^ 2 - 4 * A * (|u x| * v x)) μ :=
      hiu.sub (hip.const_mul (4 * A))
    rw [integral_add his (hiv.const_mul (4 * A ^ 2)),
      integral_sub hiu (hip.const_mul (4 * A)), integral_const_mul, integral_const_mul]
  have hnonneg : 0 ≤ ∫ x, (|u x| - 2 * A * v x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  rw [he] at hnonneg
  linarith

/-- Conditional S08 conversion: apply a weighted L1 inequality to the actual
sign-square of f-m, then absorb its derivative factor two. The supplied L1
instance is not claimed to be source Theorem 3.1. -/
theorem variance_bound_of_signedSquare_L1 {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f w G : α → ℝ} {m A : ℝ}
    (hf : MemLp f 2 μ) (hwG : MemLp (fun x => w x * G x) 2 μ)
    (hL1 : (∫ x, |signedSquare (f x - m)| ∂μ) ≤
      A * ∫ x, 2 * |f x - m| * (w x * G x) ∂μ) :
    variance f μ ≤ 4 * A ^ 2 * ∫ x, w x ^ 2 * G x ^ 2 ∂μ := by
  have hu : MemLp (fun x => f x - m) 2 μ := hf.sub (memLp_const m)
  have hip : Integrable (fun x => |f x - m| * (w x * G x)) μ := hu.abs.integrable_mul hwG
  have hL : (∫ x, (f x - m) ^ 2 ∂μ) ≤ 2 * A * ∫ x, |f x - m| * (w x * G x) ∂μ := by
    convert hL1 using 1 <;> simp only [abs_signedSquare, mul_assoc, integral_const_mul] <;> ring
  have hb := weighted_square_absorption hu hwG hL
  have hvar := variance_le_expectation_sq hu.aestronglyMeasurable
  rw [variance_sub_const hf.aestronglyMeasurable] at hvar
  calc
    variance f μ ≤ ∫ x, (f x - m) ^ 2 ∂μ := hvar
    _ ≤ 4 * A ^ 2 * ∫ x, (w x * G x) ^ 2 ∂μ := hb
    _ = _ := by simp only [mul_pow]
section DifferentialBound
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- A generic weighted L1 bound, not an assertion that the source body satisfies it. -/
def WeightedL1Bound (μ : Measure E) (w : E → ℝ) (A : ℝ) : Prop :=
  ∀ g : E → ℝ, Differentiable ℝ g → IsMedian μ g 0 → Integrable g μ →
    Integrable (fun x => w x * ‖fderiv ℝ g x‖) μ →
    (∫ x, |g x| ∂μ) ≤ A * ∫ x, w x * ‖fderiv ℝ g x‖ ∂μ

theorem variance_bound_of_weightedL1 [IsProbabilityMeasure μ] {f w : E → ℝ} {m A : ℝ}
    (hweighted : WeightedL1Bound μ w A) (hf : Differentiable ℝ f)
    (hmed : IsMedian μ f m) (hfL2 : MemLp f 2 μ)
    (hgrad : MemLp (fun x => w x * ‖fderiv ℝ f x‖) 2 μ) :
    variance f μ ≤ 4 * A ^ 2 * ∫ x, w x ^ 2 * ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  let g := fun x => signedSquare (f x - m)
  have hd : Differentiable ℝ g := fun x =>
    (hasFDerivAt_signedSquare_sub (hf x).hasFDerivAt m).differentiableAt
  have hu : MemLp (fun x => f x - m) 2 μ := hfL2.sub (memLp_const m)
  have hi : Integrable g μ := by
    apply (integrable_norm_iff hd.continuous.aestronglyMeasurable).mp
    simpa only [g, Real.norm_eq_abs, abs_signedSquare] using hu.integrable_sq
  have hp : Integrable (fun x => |f x - m| * (w x * ‖fderiv ℝ f x‖)) μ :=
    hu.abs.integrable_mul hgrad
  have he : (fun x => w x * ‖fderiv ℝ g x‖) =
      fun x => 2 * (|f x - m| * (w x * ‖fderiv ℝ f x‖)) := by
    funext x
    rw [norm_fderiv_signedSquare_sub (hf x) m]
    ring
  have hig : Integrable (fun x => w x * ‖fderiv ℝ g x‖) μ := by
    rw [he]; exact hp.const_mul 2
  have hL := hweighted g hd hmed.signedSquare_sub hi hig
  apply variance_bound_of_signedSquare_L1 hfL2 hgrad
  rw [he] at hL
  simpa only [g, mul_assoc] using hL
end DifferentialBound
end HitAndRun.Geometry
