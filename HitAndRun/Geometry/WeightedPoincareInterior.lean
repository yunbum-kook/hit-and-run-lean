module
public import HitAndRun.Geometry.WeightedPoincareRadialBound
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set Filter
open scoped Pointwise Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The contracted body is uniformly away from the actual boundary, converting
an ordinary gradient integral into the weighted gradient integral. -/
theorem integral_contraction_le_boundary (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hb : Bornology.IsBounded K) (hc : Convex ℝ K) (ho : IsOpen K)
    (hfront : (frontier K).Nonempty) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : E) r ⊆ K) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {h : E → ℝ} (hh : Continuous h) (hn : ∀ x, 0 ≤ h x) :
    (∫ x in K, h (a • x) ∂μ) ≤
      (a ^ Module.finrank ℝ E)⁻¹ / ((1 - a) * r) *
        ∫ x in K, Metric.infDist x (frontier K) * h x ∂μ := by
  have hz : (0 : E) ∈ K := hball (by simpa using hr)
  have hsub : a • K ⊆ K := by
    rintro y ⟨x, hx, rfl⟩
    exact hc.smul_mem_of_zero_mem hz hx ⟨ha0.le, ha1.le⟩
  have hm : MeasurableSet (a • K) := (ho.smul₀ ha0.ne').measurableSet
  have hw : IntegrableOn (fun x => Metric.infDist x (frontier K) * h x) K μ :=
    continuous_integrableOn_bounded μ hb ((Metric.continuous_infDist_pt _).mul hh)
  have hpos : 0 < (1 - a) * r := mul_pos (sub_pos.mpr ha1) hr
  have hpoint : ∀ y ∈ a • K, h y ≤ (Metric.infDist y (frontier K) * h y) / ((1 - a) * r) := by
    rintro y ⟨x, hx, rfl⟩
    apply (le_div_iff₀ hpos).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (contraction_boundary_distance hc ho hfront hball hx ha0.le ha1) (hn (a • x))
  have hsmall := integral_mono_ae
    ((continuous_integrableOn_bounded μ hb hh).mono_set hsub)
    ((hw.mono_set hsub).div_const ((1 - a) * r))
    ((ae_restrict_mem hm).mono fun x hx => hpoint x hx)
  rw [integral_div] at hsmall
  have hlarge := setIntegral_mono_set (s := a • K) hw
    (Eventually.of_forall fun x => mul_nonneg Metric.infDist_nonneg (hn x))
    (Eventually.of_forall fun x hx => hsub hx)
  rw [Measure.setIntegral_comp_smul_of_pos μ h K ha0, smul_eq_mul]
  have ht := mul_le_mul_of_nonneg_left
    (hsmall.trans (div_le_div_of_nonneg_right hlarge hpos.le))
    (show 0 ≤ (a ^ Module.finrank ℝ E)⁻¹ from inv_nonneg.mpr (pow_nonneg ha0.le _))
  convert ht using 1 <;> ring
end HitAndRun.Geometry
