module
public import HitAndRun.Geometry.WeightedPoincareLipschitzWeak
public import HitAndRun.Sobolev.SmoothGraph
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory EllipticPdes EllipticPdes.H1Graph Set Filter
open scoped Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

theorem locallyLipschitz_gradient_memLp (hb : Bornology.IsBounded Ω) (hΩ : MeasurableSet Ω)
    {f : E → ℝ} (hf : LocallyLipschitz f) : MemLp (gradient f) 2 (μ.restrict Ω) := by
  apply (locallyLipschitz_fderiv_memLp μ hf hb hΩ 2).of_le
    (((InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
      (measurable_fderiv ℝ f)).aestronglyMeasurable)
  exact Eventually.of_forall fun x => by simp [gradient]

def locallyLipschitzGraph (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω)
    (f : E → ℝ) (hf : LocallyLipschitz f) : H1Graph μ Ω :=
  mk ((Sobolev.continuous_memLp_bounded_restrict hb hΩ.measurableSet hf.continuous).toLp f)
    ((locallyLipschitz_gradient_memLp hb hΩ.measurableSet hf).toLp (gradient f))

theorem locallyLipschitzGraph_fn (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω)
    (f : E → ℝ) (hf : LocallyLipschitz f) :
    (fnL (locallyLipschitzGraph (μ := μ) hb hΩ f hf) : E → ℝ) =ᵐ[μ.restrict Ω] f :=
  (Sobolev.continuous_memLp_bounded_restrict hb hΩ.measurableSet hf.continuous).coeFn_toLp

theorem locallyLipschitzGraph_grad (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω)
    (f : E → ℝ) (hf : LocallyLipschitz f) :
    (gradL (locallyLipschitzGraph (μ := μ) hb hΩ f hf) : E → E) =ᵐ[μ.restrict Ω] gradient f :=
  (locallyLipschitz_gradient_memLp hb hΩ.measurableSet hf).coeFn_toLp

theorem locallyLipschitz_hasWeakFDerivOn (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω)
    {f : E → ℝ} (hf : LocallyLipschitz f) :
    HasWeakFDerivOn ⟨Ω, hΩ⟩ f (fderiv ℝ f) μ := by
  intro v
  apply hasWeakLineDerivOn_iff.mpr
  have hd : MemLp (fun x => fderiv ℝ f x v) 2 (μ.restrict Ω) := by
    apply ((locallyLipschitz_fderiv_memLp μ hf hb hΩ.measurableSet 2).mul_const ‖v‖).of_le
      ((measurable_fderiv_apply_const ℝ f v).aestronglyMeasurable)
    exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_mul, abs_norm] using (fderiv ℝ f x).le_opNorm v
  refine ⟨hf.continuous.locallyIntegrable.locallyIntegrableOn Ω,
    locallyIntegrableOn_of_locallyIntegrable_restrict (hd.locallyIntegrable (by norm_num)), ?_⟩
  intro φ hφ hc hs
  simpa only [smul_eq_mul, mul_comm] using
    locallyLipschitz_integral_fderiv_test μ hf (hφ.of_le (by simp)) hc v

theorem locallyLipschitzGraph_mem_W12 (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω)
    (f : E → ℝ) (hf : LocallyLipschitz f) :
    locallyLipschitzGraph (μ := μ) hb hΩ f hf ∈ W12 μ Ω := by
  apply (mem_W12_iff_hasWeakFDerivOn hΩ _).mpr
  apply (locallyLipschitz_hasWeakFDerivOn hb hΩ hf).congr_ae
    (locallyLipschitzGraph_fn hb hΩ f hf).symm
  filter_upwards [locallyLipschitzGraph_grad (μ := μ) hb hΩ f hf] with x hx
  rw [hx]
  ext v
  exact (InnerProductSpace.toDual_symm_apply (x := v) (y := fderiv ℝ f x)).symm

def locallyLipschitzH1 (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω)
    (f : E → ℝ) (hf : LocallyLipschitz f) : W12 μ Ω :=
  ⟨locallyLipschitzGraph hb hΩ f hf, locallyLipschitzGraph_mem_W12 hb hΩ f hf⟩
end HitAndRun.Geometry
