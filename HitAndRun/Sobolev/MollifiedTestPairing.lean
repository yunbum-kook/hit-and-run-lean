module
public import HitAndRun.Analysis.MollifiedL2
public import HitAndRun.External.EllipticPDE.Sobolev.Graph
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph EllipticPdes.Embedding HitAndRun.Analysis Filter
open scoped Convolution Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem tendsto_mollified_integral_mul {ι : Type*} {l : Filter ι}
    (rho : ι → ContDiffBump (0 : E))
    (hr : Tendsto (fun i => (rho i).rOut) l (𝓝 0))
    {h g : E → ℝ} (hh : MemLp h 2 μ) (hg : MemLp g 2 μ) :
    Tendsto (fun i => ∫ x, (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (rho i).normed μ) x * g x ∂μ)
      l (𝓝 (∫ x, h x * g x ∂μ)) := by
  have hc (i : ι) : (rho i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
      (hh.toLp h : E → ℝ) = h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (rho i).normed μ := by
    rw [convolution_lsmul_comm]
    exact convolution_congr _ hh.coeFn_toLp Filter.EventuallyEq.rfl
  have hp (i : ι) :
      (∫ x, (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (rho i).normed μ) x * g x ∂μ) =
        inner ℝ (mollifiedL2 (rho i) (hh.toLp h)) (hg.toLp g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_mollifiedL2 (rho i) (hh.toLp h), hg.coeFn_toLp] with x hx hy
    rw [hx, hy, hc]
    simp [RCLike.inner_apply, mul_comm]
  simp_rw [hp]
  have ht := ((continuous_id.inner continuous_const :
      Continuous (fun w : Lp ℝ 2 μ => inner ℝ w (hg.toLp g))).tendsto (hh.toLp h)).comp
    (tendsto_mollifiedL2 rho hr (hh.toLp h))
  simpa [Function.comp_def, inner_toLp_toLp, RCLike.inner_apply, mul_comm] using ht

theorem tendsto_mollified_test_pairing {ι : Type*} {l : Filter ι}
    (rho : ι → ContDiffBump (0 : E))
    (hr : Tendsto (fun i => (rho i).rOut) l (𝓝 0))
    {h : E → ℝ} (hh : MemLp h 2 μ) {Ω : Set E} (φ : testFunctions Ω) (v : E) :
    Tendsto (fun i => ∫ x, (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (rho i).normed μ) x *
      fderiv ℝ (φ : E → ℝ) x v ∂μ) l
      (𝓝 (∫ x, h x * fderiv ℝ (φ : E → ℝ) x v ∂μ)) :=
  tendsto_mollified_integral_mul rho hr hh
    ((continuous_fderiv_apply_of_mem φ.property v).memLp_of_hasCompactSupport
      (hasCompactSupport_fderiv_apply_of_mem φ.property v))

theorem tendsto_mollified_finite_test_pairing {ι J : Type*} [Fintype J] {l : Filter ι}
    (rho : ι → ContDiffBump (0 : E))
    (hr : Tendsto (fun i => (rho i).rOut) l (𝓝 0))
    {h : E → ℝ} (hh : MemLp h 2 μ) {Ω : Set E}
    (φ : J → testFunctions Ω) (v : J → E) :
    Tendsto (fun i => ∑ j, ∫ x, (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (rho i).normed μ) x *
      fderiv ℝ (φ j : E → ℝ) x (v j) ∂μ) l
      (𝓝 (∑ j, ∫ x, h x * fderiv ℝ (φ j : E → ℝ) x (v j) ∂μ)) := by
  exact tendsto_finset_sum _ (fun j _ => tendsto_mollified_test_pairing rho hr hh (φ j) (v j))
end HitAndRun.Sobolev
