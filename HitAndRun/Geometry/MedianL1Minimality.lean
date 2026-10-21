module
public import HitAndRun.Geometry.WeightedPoincareMedian
public import Mathlib.MeasureTheory.Integral.Bochner.Set
@[expose] public section
namespace HitAndRun.Geometry
open MeasureTheory Set
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

lemma integral_abs_sub_le_of_upper_tail {f : α → ℝ} (hf : Integrable f μ)
    {m z : ℝ} (hm : μ {x | m < f x} ≤ (1 / 2 : ℝ≥0∞)) (hmz : m ≤ z) :
    (∫ x, |f x - m| ∂μ) ≤ ∫ x, |f x - z| ∂μ := by
  let s := {x | m < f x}
  have hs : NullMeasurableSet s μ :=
    aestronglyMeasurable_const.nullMeasurableSet_lt hf.aestronglyMeasurable
  have hi : Integrable (s.indicator (fun _ => (2 * (z - m)))) μ :=
    (integrable_const _).indicator₀ hs
  have hp : ∀ x, |f x - m| + (z - m) - s.indicator (fun _ => 2 * (z - m)) x ≤
      |f x - z| := by
    intro x
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx]
      have hx' : m < f x := hx
      rw [abs_of_nonneg (by linarith : 0 ≤ f x - m)]
      have := le_abs_self (f x - z)
      linarith
    · rw [indicator_of_notMem hx, sub_zero]
      have hx' : f x ≤ m := le_of_not_gt hx
      rw [abs_of_nonpos (by linarith : f x - m ≤ 0),
        abs_of_nonpos (by linarith : f x - z ≤ 0)]
      linarith
  have hfm : Integrable (fun x => |f x - m|) μ := (hf.sub (integrable_const m)).abs
  have hfz : Integrable (fun x => |f x - z|) μ := (hf.sub (integrable_const z)).abs
  have hsum : Integrable (fun x => |f x - m| + (z - m)) μ := hfm.add (integrable_const _)
  have hint := integral_mono (hsum.sub hi) hfz hp
  simp only [Pi.sub_apply] at hint
  rw [integral_sub hsum hi, integral_add hfm (integrable_const (z - m)),
    integral_const, probReal_univ, one_smul, integral_indicator₀ hs, integral_const] at hint
  have hhalf : μ.real s ≤ 1 / 2 := by
    have hh := ENNReal.toReal_mono (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤) hm
    simpa [Measure.real] using hh
  simp only [smul_eq_mul, Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter] at hint
  change _ - μ.real s * (2 * (z - m)) ≤ _ at hint
  nlinarith [mul_nonneg (sub_nonneg.mpr hmz) (show 0 ≤ 1 / 2 - μ.real s by linarith)]

/-- A median minimizes absolute deviation, with atoms allowed. -/
theorem IsMedian.integral_abs_sub_le {f : α → ℝ} {m : ℝ}
    (hm : IsMedian μ f m) (hf : Integrable f μ) (z : ℝ) :
    (∫ x, |f x - m| ∂μ) ≤ ∫ x, |f x - z| ∂μ := by
  rcases le_total m z with h | h
  · exact integral_abs_sub_le_of_upper_tail hf hm.2 h
  · have htail : μ {x | -m < -f x} ≤ (1 / 2 : ℝ≥0∞) := by
      simpa only [neg_lt_neg_iff] using hm.1
    have hb := integral_abs_sub_le_of_upper_tail hf.neg htail (neg_le_neg h)
    simpa only [Pi.neg_apply, neg_sub_neg, abs_sub_comm] using hb
end HitAndRun.Geometry
