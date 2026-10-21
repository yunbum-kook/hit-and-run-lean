module
public import HitAndRun.Geometry.WeightedPoincareGeometry
public import HitAndRun.Geometry.WeightedPoincareResidence
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set Filter
open scoped Pointwise Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Exact radial Fubini identity on the actual body, with its actual gauge. -/
theorem integral_dilated_body_residence (μ : Measure E) [SFinite μ]
    {K : Set E} (hc : Convex ℝ K) (ho : IsOpen K) (hzero : (0 : E) ∈ K)
    {h : E → ℝ} (hh : IntegrableOn h K μ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (∫ t in Ioo a 1, ∫ y in t • K, h y ∂μ) =
      ∫ y in K, h y * (1 - max a (gauge K y)) ∂μ := by
  have hg : Continuous (gauge K) := continuous_gauge hc (ho.mem_nhds hzero)
  have hslice : ∀ t ∈ Ioo a 1,
      (∫ y in t • K, h y ∂μ) = ∫ y in K, if gauge K y < t then h y else 0 ∂μ := by
    intro t ht
    have ht0 : 0 < t := lt_of_le_of_lt ha0 ht.1
    have he : t • K = {y | gauge K y < t} := Set.ext (mem_dilation_iff_gauge_lt hc ho hzero ht0)
    have hm : MeasurableSet (t • K) := by
      rw [he]
      exact measurableSet_lt hg.measurable measurable_const
    have hsub : t • K ⊆ K := by
      rintro y ⟨x, hx, rfl⟩
      exact hc.smul_mem_of_zero_mem hzero hx ⟨ht0.le, ht.2.le⟩
    have hi := setIntegral_indicator (μ := μ) (s := K) (f := h) hm
    rw [Set.inter_eq_right.mpr hsub] at hi
    rw [← hi]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by simp [Set.indicator, he]
  calc
    _ = ∫ t in Ioo a 1, ∫ y in K, if gauge K y < t then h y else 0 ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hslice t ht
    _ = _ := integral_radial_residence (μ.restrict K) hh hg.measurable ha1
      ((ae_restrict_mem ho.measurableSet).mono fun y hy =>
        interior_subset_gauge_lt_one K (by rwa [ho.interior_eq]))
/-- Haar scaling and the exact residence identity give the radial integral
bound. Integrability hypotheses are explicit analytic bookkeeping, not PI inputs. -/
theorem radial_homothety_integral_le [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hc : Convex ℝ K) (ho : IsOpen K) (hzero : (0 : E) ∈ K)
    {h : E → ℝ} (hh : IntegrableOn h K μ) (hn : ∀ y, 0 ≤ h y)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hi : IntegrableOn (fun t => ∫ y in K, h (t • y) ∂μ) (Ioo a 1) volume)
    (hs : IntegrableOn (fun t => ∫ y in t • K, h y ∂μ) (Ioo a 1) volume) :
    (∫ t in Ioo a 1, ∫ y in K, h (t • y) ∂μ) ≤
      (a ^ Module.finrank ℝ E)⁻¹ * ∫ y in K, h y * (1 - max a (gauge K y)) ∂μ := by
  have hp : ∀ t ∈ Ioo a 1,
      (∫ y in K, h (t • y) ∂μ) ≤
        (a ^ Module.finrank ℝ E)⁻¹ * ∫ y in t • K, h y ∂μ := by
    intro t ht
    have ht0 := ha0.trans ht.1
    rw [Measure.setIntegral_comp_smul_of_pos μ h K ht0, smul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun y => hn y)
    apply (inv_le_inv₀ (pow_pos ht0 _) (pow_pos ha0 _)).mpr
    exact pow_le_pow_left₀ ha0.le ht.1.le _
  have hint := integral_mono_ae hi (hs.const_mul ((a ^ Module.finrank ℝ E)⁻¹))
    ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => hp t ht)
  rw [integral_const_mul, integral_dilated_body_residence μ hc ho hzero hh ha0.le ha1] at hint
  exact hint
/-- The radial residence weight is bounded by the genuine boundary distance. -/
theorem radial_residence_weight_le {K : Set E} (hc : Convex ℝ K) (ho : IsOpen K)
    (hfront : (frontier K).Nonempty) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : E) r ⊆ K) {y : E} (hy : y ∈ K) (a : ℝ) :
    1 - max a (gauge K y) ≤ Metric.infDist y (frontier K) / r := by
  apply le_trans (sub_le_sub_left (le_max_right a (gauge K y)) 1)
  exact (le_div_iff₀ hr).mpr (gauge_boundary_distance hc ho hfront hr hball hy)

/-- Integrating the actual residence weight against a nonnegative density
produces the boundary-distance weighted integral used in the radial argument. -/
theorem integral_radial_residence_le_boundary (μ : Measure E)
    {K : Set E} (hc : Convex ℝ K) (ho : IsOpen K)
    (hfront : (frontier K).Nonempty) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : E) r ⊆ K) {h : E → ℝ} (hn : ∀ y, 0 ≤ h y)
    (a : ℝ)
    (hi : IntegrableOn (fun y => h y * (1 - max a (gauge K y))) K μ)
    (hb : IntegrableOn (fun y => h y * Metric.infDist y (frontier K)) K μ) :
    (∫ y in K, h y * (1 - max a (gauge K y)) ∂μ) ≤
      (∫ y in K, h y * Metric.infDist y (frontier K) ∂μ) / r := by
  have hh := integral_mono_ae hi (hb.div_const r)
    ((ae_restrict_mem ho.measurableSet).mono fun y hy => by
      simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_left (radial_residence_weight_le hc ho hfront hr hball hy a) (hn y))
  simpa only [integral_div] using hh
end HitAndRun.Geometry
