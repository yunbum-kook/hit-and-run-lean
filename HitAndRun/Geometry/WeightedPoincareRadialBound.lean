module
public import HitAndRun.Geometry.WeightedPoincareRadial
public import HitAndRun.Geometry.WeightedPoincareRadialTransport
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set Filter
open scoped Topology Pointwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

 theorem continuous_integrableOn_bounded (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {K : Set E} (hb : Bornology.IsBounded K) {g : E → ℝ} (hg : Continuous g) :
    IntegrableOn g K μ :=
  (hg.continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure

/-- The radial FTC estimate integrated on the actual bounded body. -/
theorem integral_radial_difference_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hb : Bornology.IsBounded K) (hm : MeasurableSet K)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) {a R : ℝ} (ha : a ≤ 1)
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) :
    (∫ x in K, ‖f x - f (a • x)‖ ∂μ) ≤
      R * ∫ t in Ioo a 1, ∫ x in K, ‖fderiv ℝ f (t • x)‖ ∂μ := by
  have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hjc : Continuous (fun p : ℝ × E => ‖fderiv ℝ f (p.1 • p.2)‖) :=
    (hd.comp (continuous_fst.smul continuous_snd)).norm
  have hj : Integrable (fun p : ℝ × E => ‖fderiv ℝ f (p.1 • p.2)‖)
      ((volume.restrict (Ioo a 1)).prod (μ.restrict K)) := by
    rw [Measure.prod_restrict]
    exact (hjc.continuousOn.integrableOn_compact
      (isCompact_Icc.prod hb.isCompact_closure)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self subset_closure)
  have hi : IntegrableOn (fun x => ∫ t in Ioo a 1, ‖fderiv ℝ f (t • x)‖) K μ :=
    hj.integral_prod_right
  have hleft : IntegrableOn (fun x => ‖f x - f (a • x)‖) K μ :=
    continuous_integrableOn_bounded μ hb
      (hf.continuous.sub (hf.continuous.comp (continuous_const.smul continuous_id))).norm
  have hpoint : ∀ x ∈ K, ‖f x - f (a • x)‖ ≤
      R * ∫ t in Ioo a 1, ‖fderiv ℝ f (t • x)‖ := by
    intro x hx
    have h := radial_norm_sub_le_integral f hf x ha
    rw [intervalIntegral.integral_of_le ha, integral_Ioc_eq_integral_Ioo, integral_const_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hR x hx) (integral_nonneg fun _ => norm_nonneg _))
  have h := integral_mono_ae hleft (hi.const_mul R)
    ((ae_restrict_mem hm).mono fun x hx => hpoint x hx)
  rw [integral_const_mul, ← integral_integral_swap hj] at h
  exact h

/-- Continuous radial integrands on a bounded body have integrable slices. -/
theorem integrable_radial_slices (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hb : Bornology.IsBounded K) {h : E → ℝ} (hh : Continuous h)
    {b : ℝ → ℝ} (hbcont : Continuous b) (a : ℝ) :
    IntegrableOn (fun t => b t * ∫ y in K, h (t • y) ∂μ) (Ioo a 1) volume := by
  have hjc : Continuous (fun p : ℝ × E => b p.1 * h (p.1 • p.2)) :=
    (hbcont.comp continuous_fst).mul (hh.comp (continuous_fst.smul continuous_snd))
  have hj : Integrable (fun p : ℝ × E => b p.1 * h (p.1 • p.2))
      ((volume.restrict (Ioo a 1)).prod (μ.restrict K)) := by
    rw [Measure.prod_restrict]
    exact (hjc.continuousOn.integrableOn_compact
      (isCompact_Icc.prod hb.isCompact_closure)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self subset_closure)
  change Integrable (fun t => b t * ∫ y in K, h (t • y) ∂μ) _
  convert hj.integral_prod_left using 1
  funext t
  exact (integral_const_mul (b t) (fun y => h (t • y))).symm

/-- The moving-body integral in Haar scaling is integrable, without an extra
analytic assumption on the source function. -/
theorem integrable_dilated_body_slices (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hb : Bornology.IsBounded K) {h : E → ℝ} (hh : Continuous h)
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t => ∫ y in t • K, h y ∂μ) (Ioo a 1) volume := by
  have hi := integrable_radial_slices μ hb hh (continuous_id.pow (Module.finrank ℝ E)) a
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have ht0 := ha.trans ht.1
  rw [Measure.setIntegral_comp_smul_of_pos μ h K ht0, smul_eq_mul]
  change t ^ Module.finrank ℝ E * ((t ^ Module.finrank ℝ E)⁻¹ * _) = _
  rw [mul_inv_cancel_left₀ (pow_ne_zero _ ht0.ne')]

/-- The complete radial error estimate for C1 functions on the actual body.
All integrability requirements are discharged from boundedness and continuity. -/
theorem integral_radial_difference_le_boundary (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hb : Bornology.IsBounded K) (hc : Convex ℝ K) (ho : IsOpen K)
    (hfront : (frontier K).Nonempty) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : E) r ⊆ K)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) {a R : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) :
    (∫ x in K, ‖f x - f (a • x)‖ ∂μ) ≤
      R * (a ^ Module.finrank ℝ E)⁻¹ / r *
        ∫ x in K, Metric.infDist x (frontier K) * ‖fderiv ℝ f x‖ ∂μ := by
  have hz : (0 : E) ∈ K := hball (by simpa using hr)
  have hR0 : 0 ≤ R := by simpa using hR 0 hz
  have hd : Continuous (fun x => ‖fderiv ℝ f x‖) :=
    (hf.continuous_fderiv (by norm_num)).norm
  have hg : Continuous (gauge K) := continuous_gauge hc (ho.mem_nhds hz)
  have hi : IntegrableOn (fun t => ∫ y in K, ‖fderiv ℝ f (t • y)‖ ∂μ)
      (Ioo a 1) volume := by
    simpa only [one_mul] using integrable_radial_slices μ hb hd continuous_const a (b := fun _ => 1)
  have hs := integrable_dilated_body_slices μ hb hd ha0
  have hhom := radial_homothety_integral_le μ hc ho hz
    (continuous_integrableOn_bounded μ hb hd) (fun _ => norm_nonneg _) ha0 ha1 hi hs
  have hweight := integral_radial_residence_le_boundary μ hc ho hfront hr hball
    (fun x => norm_nonneg (fderiv ℝ f x)) a
    (continuous_integrableOn_bounded μ hb (hd.mul (continuous_const.sub (continuous_const.max hg))))
    (continuous_integrableOn_bounded μ hb (hd.mul (Metric.continuous_infDist_pt _)))
  have hrad := integral_radial_difference_le μ hb ho.measurableSet f hf ha1.le hR
  have ht := hrad.trans (mul_le_mul_of_nonneg_left
    (hhom.trans (mul_le_mul_of_nonneg_left hweight (inv_nonneg.mpr (pow_nonneg ha0.le _)))) hR0)
  have he : (∫ x in K, ‖fderiv ℝ f x‖ * Metric.infDist x (frontier K) ∂μ) =
      ∫ x in K, Metric.infDist x (frontier K) * ‖fderiv ℝ f x‖ ∂μ := by
    congr 1
    funext x
    exact mul_comm _ _
  rw [he] at ht
  convert ht using 1 <;> ring
end HitAndRun.Geometry
