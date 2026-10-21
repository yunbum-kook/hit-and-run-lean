module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
# From tail bounds to an `L¹` concentration scale

Lemma (L4) of `docs/part1/P02-NEEDLE-BLUEPRINT.md`.  If a measurable function `v` has an exponential
(or Gaussian) tail around some centre `b`, then `v` is integrable and its mean absolute deviation
from its mean is bounded by a constant multiple of the tail scale `s`.

* `integral_abs_sub_integral_le_of_exp_tail`: if
  `μ {x | t < |v x - b|} ≤ C exp(-c t / s)` for all `t ≥ 0`, then `v` is integrable and
  `∫ |v - ∫ v| ≤ (2 C / c) s`.
* `integral_abs_sub_integral_le_of_gaussian_tail`: if
  `μ {x | t < |v x - b|} ≤ C exp(-c t² / s²)` for all `t ≥ 0`, then `v` is integrable and
  `∫ |v - ∫ v| ≤ C √(π / c) s`.

Both follow from the layer-cake formula
`∫⁻ ofReal |v - b| = ∫_0^∞ μ {|v - b| > t} dt` and the elementary estimate
`∫ |v - ∫ v| ≤ 2 ∫ |v - b|` (`integral_abs_sub_integral_le`), which holds for every centre `b`.
-/

open MeasureTheory Set Real
open scoped ENNReal

namespace CvxBody

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A finite `L¹` distance to a constant `b` gives integrability, with the expected bound. -/
theorem integrable_and_integral_abs_sub_le_of_lintegral_le {v : α → ℝ} (hv : Measurable v) {b M : ℝ}
    (hM : 0 ≤ M) (h : ∫⁻ x, ENNReal.ofReal |v x - b| ∂μ ≤ ENNReal.ofReal M) :
    Integrable (fun x => v x - b) μ ∧ ∫ x, |v x - b| ∂μ ≤ M := by
  have hm : Measurable fun x => |v x - b| := (hv.sub_const b).abs
  have hint : Integrable (fun x => |v x - b|) μ := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => abs_nonneg _)]
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  refine ⟨?_, ?_⟩
  · rw [← integrable_norm_iff (hv.sub_const b).aestronglyMeasurable]
    simpa [Real.norm_eq_abs] using hint
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => abs_nonneg _)
      hm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hM h

/-- The mean absolute deviation from the mean is at most twice the mean absolute deviation from any
other centre `b`. -/
theorem integral_abs_sub_integral_le [IsProbabilityMeasure μ] {v : α → ℝ} (hv : Integrable v μ)
    (b : ℝ) (hb : Integrable (fun x => v x - b) μ) :
    ∫ x, |v x - ∫ y, v y ∂μ| ∂μ ≤ 2 * ∫ x, |v x - b| ∂μ := by
  have h1 : Integrable (fun x => |v x - b|) μ := hb.abs
  have h2 : ∀ x, |v x - ∫ y, v y ∂μ| ≤ |v x - b| + |b - ∫ y, v y ∂μ| := fun x => by
    have := abs_add_le (v x - b) (b - ∫ y, v y ∂μ)
    simpa using this
  have h3 : |b - ∫ y, v y ∂μ| ≤ ∫ x, |v x - b| ∂μ := by
    have : b - ∫ y, v y ∂μ = ∫ x, (b - v x) ∂μ := by
      rw [integral_sub (integrable_const b) hv]; simp
    rw [this]
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => abs_sub_comm _ _)
  calc ∫ x, |v x - ∫ y, v y ∂μ| ∂μ ≤ ∫ x, (|v x - b| + |b - ∫ y, v y ∂μ|) ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
          (h1.add (integrable_const _)) (Filter.Eventually.of_forall h2)
    _ = ∫ x, |v x - b| ∂μ + |b - ∫ y, v y ∂μ| := by
        rw [integral_add h1 (integrable_const _)]; simp
    _ ≤ 2 * ∫ x, |v x - b| ∂μ := by linarith

/-- Layer-cake bound: a tail bound `μ {t < |v - b|} ≤ ofReal (f t)` with `f` integrable on
`(0, ∞)` bounds the `L¹` distance to `b` by `∫_0^∞ f`. -/
theorem lintegral_abs_sub_le_of_tail {v : α → ℝ} (hv : Measurable v) {b : ℝ} {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 0)) (hf0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ f t)
    (htail : ∀ t, 0 < t → μ {x | t < |v x - b|} ≤ ENNReal.ofReal (f t)) :
    ∫⁻ x, ENNReal.ofReal |v x - b| ∂μ ≤ ENNReal.ofReal (∫ t in Ioi 0, f t) := by
  rw [lintegral_eq_lintegral_meas_lt μ (Filter.Eventually.of_forall fun x => abs_nonneg _)
    (hv.sub_const b).abs.aemeasurable]
  rw [ofReal_integral_eq_lintegral_ofReal hf
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hf0))]
  exact setLIntegral_mono' measurableSet_Ioi fun t ht => htail t ht

/-- **Exponential tail implies an `L¹` concentration scale.**  If
`μ {x | t < |v x - b|} ≤ C exp (-c t / s)` for all `t ≥ 0`, then `v` is integrable and
`∫ |v - ∫ v| ≤ (2 C / c) s`. -/
theorem integral_abs_sub_integral_le_of_exp_tail [IsProbabilityMeasure μ] {v : α → ℝ}
    (hv : Measurable v) {b C c s : ℝ} (hC : 0 < C) (hc : 0 < c) (hs : 0 < s)
    (htail : ∀ t, 0 ≤ t → μ {x | t < |v x - b|} ≤ ENNReal.ofReal (C * Real.exp (-c * t / s))) :
    Integrable v μ ∧ ∫ x, |v x - ∫ y, v y ∂μ| ∂μ ≤ 2 * C / c * s := by
  have hcs : 0 < c / s := div_pos hc hs
  have hexp : ∀ t : ℝ, C * Real.exp (-c * t / s) = C * Real.exp (-(c / s) * t) := fun t => by
    congr 2; ring
  have hfi : IntegrableOn (fun t : ℝ => C * Real.exp (-(c / s) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hcs).const_mul C
  have hI : ∫ t in Ioi (0 : ℝ), C * Real.exp (-(c / s) * t) = C * s / c := by
    rw [integral_const_mul]
    have := integral_exp_mul_Ioi (a := -(c / s)) (by linarith) 0
    rw [this]; field_simp; simp
  have hbound := lintegral_abs_sub_le_of_tail (μ := μ) hv hfi
    (fun t _ => by positivity) (fun t ht => by rw [← hexp]; exact htail t ht.le)
  rw [hI] at hbound
  obtain ⟨hb, hb2⟩ := integrable_and_integral_abs_sub_le_of_lintegral_le hv
    (by positivity) hbound
  have hvint : Integrable v μ := (Integrable.add hb (integrable_const b)).congr (Filter.Eventually.of_forall fun x => by simp)
  refine ⟨hvint, ?_⟩
  calc ∫ x, |v x - ∫ y, v y ∂μ| ∂μ ≤ 2 * ∫ x, |v x - b| ∂μ := integral_abs_sub_integral_le hvint b hb
    _ ≤ 2 * (C * s / c) := by linarith
    _ = 2 * C / c * s := by ring

/-- **Gaussian tail implies an `L¹` concentration scale.**  If
`μ {x | t < |v x - b|} ≤ C exp (-c t² / s²)` for all `t ≥ 0`, then `v` is integrable and
`∫ |v - ∫ v| ≤ C √(π / c) s`. -/
theorem integral_abs_sub_integral_le_of_gaussian_tail [IsProbabilityMeasure μ] {v : α → ℝ}
    (hv : Measurable v) {b C c s : ℝ} (hC : 0 < C) (hc : 0 < c) (hs : 0 < s)
    (htail : ∀ t, 0 ≤ t →
      μ {x | t < |v x - b|} ≤ ENNReal.ofReal (C * Real.exp (-c * t ^ 2 / s ^ 2))) :
    Integrable v μ ∧ ∫ x, |v x - ∫ y, v y ∂μ| ∂μ ≤ C * Real.sqrt (π / c) * s := by
  have hcs : 0 < c / s ^ 2 := div_pos hc (pow_pos hs 2)
  have hexp : ∀ t : ℝ, C * Real.exp (-c * t ^ 2 / s ^ 2) =
      C * Real.exp (-(c / s ^ 2) * t ^ 2) := fun t => by congr 2; ring
  have hfi : IntegrableOn (fun t : ℝ => C * Real.exp (-(c / s ^ 2) * t ^ 2)) (Ioi 0) :=
    ((integrable_exp_neg_mul_sq hcs).const_mul C).integrableOn
  have hI : ∫ t in Ioi (0 : ℝ), C * Real.exp (-(c / s ^ 2) * t ^ 2) =
      C * (s * Real.sqrt (π / c) / 2) := by
    rw [integral_const_mul, integral_gaussian_Ioi]
    have : π / (c / s ^ 2) = s ^ 2 * (π / c) := by field_simp
    rw [this, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]
  have hbound := lintegral_abs_sub_le_of_tail (μ := μ) hv hfi
    (fun t _ => by positivity) (fun t ht => by rw [← hexp]; exact htail t ht.le)
  rw [hI] at hbound
  obtain ⟨hb, hb2⟩ := integrable_and_integral_abs_sub_le_of_lintegral_le hv
    (by positivity) hbound
  have hvint : Integrable v μ := (Integrable.add hb (integrable_const b)).congr (Filter.Eventually.of_forall fun x => by simp)
  refine ⟨hvint, ?_⟩
  calc ∫ x, |v x - ∫ y, v y ∂μ| ∂μ ≤ 2 * ∫ x, |v x - b| ∂μ := integral_abs_sub_integral_le hvint b hb
    _ ≤ 2 * (C * (s * Real.sqrt (π / c) / 2)) := by linarith
    _ = C * Real.sqrt (π / c) * s := by ring

end CvxBody
