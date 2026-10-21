module
public import HitAndRun.Geometry.WeightedPoincareInterior
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set Filter
open scoped Pointwise Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Conditional geometric assembly. The ordinary L1 inequality is explicitly
an input, not asserted from a Poincare constant or logconcavity. -/
theorem exists_weighted_center_of_ordinaryL1 (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hb : Bornology.IsBounded K) (hc : Convex ℝ K) (ho : IsOpen K)
    (hfront : (frontier K).Nonempty) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : E) r ⊆ K) {a R B : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hB : 0 ≤ B) (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hL1 : ∀ g : E → ℝ, ContDiff ℝ 1 g → ∃ z : ℝ,
      (∫ x in K, ‖g x - z‖ ∂μ) ≤ B * ∫ x in K, ‖fderiv ℝ g x‖ ∂μ)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) :
    ∃ z : ℝ, (∫ x in K, ‖f x - z‖ ∂μ) ≤
      (R * (a ^ Module.finrank ℝ E)⁻¹ / r +
        B * a * (a ^ Module.finrank ℝ E)⁻¹ / ((1 - a) * r)) *
        ∫ x in K, Metric.infDist x (frontier K) * ‖fderiv ℝ f x‖ ∂μ := by
  have hfc : ContDiff ℝ 1 (fun x : E => f (a • x)) :=
    hf.comp (contDiff_const.smul contDiff_id)
  obtain ⟨z, hz⟩ := hL1 (fun x => f (a • x)) hfc
  have hd : (∫ x in K, ‖fderiv ℝ (fun y : E => f (a • y)) x‖ ∂μ) =
      a * ∫ x in K, ‖fderiv ℝ f (a • x)‖ ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change ‖fderiv ℝ (fun y : E => f (a • y)) x‖ = a * ‖fderiv ℝ f (a • x)‖
      rw [fderiv_comp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ha0]
  rw [hd] at hz
  have hinner := integral_contraction_le_boundary μ hb hc ho hfront hr hball ha0 ha1
    (hf.continuous_fderiv (by norm_num)).norm (fun _ => norm_nonneg _)
  have hsecond := hz.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hinner ha0.le) hB)
  have hfirst := integral_radial_difference_le_boundary μ hb hc ho hfront hr hball f hf ha0 ha1 hR
  have htriangle : (∫ x in K, ‖f x - z‖ ∂μ) ≤
      (∫ x in K, ‖f x - f (a • x)‖ ∂μ) + (∫ x in K, ‖f (a • x) - z‖ ∂μ) := by
    have hi1 : IntegrableOn (fun x => ‖f x - f (a • x)‖) K μ := continuous_integrableOn_bounded μ hb (hf.continuous.sub hfc.continuous).norm
    have hi2 : IntegrableOn (fun x => ‖f (a • x) - z‖) K μ := continuous_integrableOn_bounded μ hb (hfc.continuous.sub continuous_const).norm
    rw [← integral_add hi1 hi2]
    apply integral_mono
      (continuous_integrableOn_bounded μ hb (hf.continuous.sub continuous_const).norm) (hi1.add hi2)
    intro x
    exact norm_sub_le_norm_sub_add_norm_sub (f x) (f (a • x)) z
  refine ⟨z, htriangle.trans ?_⟩
  have ht := add_le_add hfirst hsecond
  convert ht using 1 <;> ring
end HitAndRun.Geometry
