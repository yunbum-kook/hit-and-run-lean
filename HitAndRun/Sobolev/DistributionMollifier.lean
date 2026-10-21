module
public import HitAndRun.External.EllipticPDE.Embedding.Convolution
public import HitAndRun.External.EllipticPDE.Sobolev.Graph
public import HitAndRun.Geometry.DistanceCutoff

/-! Pointwise transport of an actual distributional divergence relation through
an interior mollifier. No boundary extension relation is assumed. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory Metric Set EllipticPdes EllipticPdes.H1Graph
open scoped Convolution BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

theorem translated_normed_support (rho : ContDiffBump (0 : E)) (x : E) :
    tsupport (fun y => rho.normed μ (x - y)) ⊆ closedBall x rho.rOut := by
  intro y hy
  have hs := tsupport_comp_subset_preimage (f := fun y : E => x - y)
    (rho.normed μ) (by fun_prop) hy
  rw [rho.tsupport_normed_eq] at hs
  change dist (x - y) 0 ≤ rho.rOut at hs
  change dist y x ≤ rho.rOut
  simpa [dist_eq_norm, norm_sub_rev] using hs

def translatedNormedTest (rho : ContDiffBump (0 : E)) (x : E)
    (hs : closedBall x rho.rOut ⊆ Ω) : testFunctions Ω :=
  ⟨fun y => rho.normed μ (x - y),
    (rho.contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) (rho.normed μ)).comp (contDiff_const.sub contDiff_id),
    rho.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x),
    (translated_normed_support rho x).trans hs⟩

theorem fderiv_translatedNormedTest (rho : ContDiffBump (0 : E)) (x : E)
    (hs : closedBall x rho.rOut ⊆ Ω) (y v : E) :
    fderiv ℝ (translatedNormedTest (μ := μ) rho x hs : E → ℝ) y v =
      -fderiv ℝ (rho.normed μ) (x - y) v := by
  have hd := (rho.contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) (rho.normed μ)).differentiable (by simp)
  change fderiv ℝ ((rho.normed μ) ∘ ((fun _ : E => x) - id)) y v = _
  rw [fderiv_comp y (hd _) ((differentiableAt_const x).sub differentiableAt_id),
    fderiv_sub (differentiableAt_const x) differentiableAt_id]
  simp

theorem fderiv_convolution_normed_apply (rho : ContDiffBump (0 : E))
    {f : E → ℝ} (hf : LocallyIntegrable f μ) (x v : E) :
    fderiv ℝ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x v =
      ∫ y, f y * fderiv ℝ (rho.normed μ) (x - y) v ∂μ := by
  have hc : ContDiff ℝ 1 (rho.normed μ) := (rho.contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) (rho.normed μ)).of_le (by simp)
  rw [(rho.hasCompactSupport_normed.hasFDerivAt_convolution_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hf hc x).fderiv]
  rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hf ((rho.hasCompactSupport_normed (μ := μ)).fderiv ℝ)
    (hc.continuous_fderiv one_ne_zero)]
  rfl

theorem mollified_distribution_pointwise {ι : Type*} [Fintype ι]
    (rho : ContDiffBump (0 : E)) (x : E) (hs : closedBall x rho.rOut ⊆ Ω)
    (h : E → ℝ) (G : ι → E → ℝ) (v : E) (b : ι → E)
    (hh : LocallyIntegrable h μ) (hG : ∀ j, LocallyIntegrable (G j) μ)
    (hrel : ∀ φ : testFunctions Ω,
      (∫ y, h y * fderiv ℝ (φ : E → ℝ) y v ∂μ) =
        ∑ j, ∫ y, G j y * fderiv ℝ (φ : E → ℝ) y (b j) ∂μ) :
    fderiv ℝ (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x v =
      ∑ j, fderiv ℝ (G j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x (b j) := by
  have hr := hrel (translatedNormedTest (μ := μ) rho x hs)
  simp only [fderiv_translatedNormedTest, mul_neg, integral_neg, Finset.sum_neg_distrib] at hr
  have he := neg_injective hr
  simpa only [fderiv_convolution_normed_apply rho hh,
    fderiv_convolution_normed_apply rho (hG _)] using he

theorem closedBall_subset_of_lt_interiorDistance (x : E) {r : ℝ}
    (hr : r < HitAndRun.Geometry.interiorDistance Ω x) : closedBall x r ⊆ Ω := by
  intro y hy
  by_contra hny
  have hd := Metric.infDist_le_dist_of_mem (x := x) (show y ∈ Ωᶜ from hny)
  have hy' : dist y x ≤ r := hy
  change r < Metric.infDist x Ωᶜ at hr
  rw [dist_comm y x] at hy'
  exact (not_lt_of_ge (hd.trans hy')) hr

end HitAndRun.Sobolev
