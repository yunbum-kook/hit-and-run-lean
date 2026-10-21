module
public import HitAndRun.External.EllipticPDE.Sobolev.Graph

/-! Genuine H1 graphs of smooth functions on bounded open domains. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

theorem continuous_memLp_bounded_restrict {F : Type*} [NormedAddCommGroup F]
    (hb : Bornology.IsBounded Ω) (hΩ : MeasurableSet Ω) {f : E → F} (hf : Continuous f) :
    MemLp f 2 (μ.restrict Ω) := by
  haveI : IsFiniteMeasure (μ.restrict Ω) := isFiniteMeasure_restrict.mpr
    (lt_of_le_of_lt (measure_mono subset_closure) hb.isCompact_closure.measure_lt_top).ne
  obtain ⟨R, hR, hbound⟩ := (hb.isCompact_closure.image hf).isBounded.exists_pos_norm_le
  exact MemLp.of_bound hf.aestronglyMeasurable R
    ((ae_restrict_mem hΩ).mono fun x hx => hbound _ ⟨x, subset_closure hx, rfl⟩)

theorem smooth_gradient_memLp (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω)
    (f : E → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    MemLp (gradient f) 2 (μ.restrict Ω) :=
  continuous_memLp_bounded_restrict hb hΩ.measurableSet
    ((InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hf.continuous_fderiv (by simp)))

def smoothGraph (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω)
    (f : E → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) : H1Graph μ Ω :=
  mk ((continuous_memLp_bounded_restrict hb hΩ.measurableSet hf.continuous).toLp f)
    ((smooth_gradient_memLp hb hΩ f hf).toLp (gradient f))

theorem smoothGraph_fn (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω)
    (f : E → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    (fnL (smoothGraph (μ := μ) hb hΩ f hf) : E → ℝ) =ᵐ[μ.restrict Ω] f :=
  (continuous_memLp_bounded_restrict hb hΩ.measurableSet hf.continuous).coeFn_toLp

theorem smoothGraph_grad (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω)
    (f : E → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    (gradL (smoothGraph (μ := μ) hb hΩ f hf) : E → E) =ᵐ[μ.restrict Ω] gradient f :=
  (smooth_gradient_memLp hb hΩ f hf).coeFn_toLp

theorem smoothGraph_mem_W12 (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω)
    (f : E → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    smoothGraph (μ := μ) hb hΩ f hf ∈ W12 μ Ω := by
  apply (mem_W12_iff_hasWeakFDerivOn hΩ _).mpr
  have hw := hasWeakFDerivOn_fderiv (μ := μ) (Ω := ⟨Ω, hΩ⟩)
    (hf.of_le (show (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) by simp)).contDiffOn
  apply hw.congr_ae (smoothGraph_fn hb hΩ f hf).symm
  filter_upwards [smoothGraph_grad (μ := μ) hb hΩ f hf] with x hx
  rw [hx]
  ext v
  exact (InnerProductSpace.toDual_symm_apply (x := v) (y := fderiv ℝ f x)).symm

def smoothH1 (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω)
    (f : E → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) : W12 μ Ω :=
  ⟨smoothGraph hb hΩ f hf, smoothGraph_mem_W12 hb hΩ f hf⟩
theorem norm_sq_smoothGraph (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω)
    (f : E → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ‖smoothGraph (μ := μ) hb hΩ f hf‖ ^ 2 =
      (∫ x in Ω, f x ^ 2 ∂μ) + ∫ x in Ω, ‖gradient f x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq, ← real_inner_self_eq_norm_sq (fnL (smoothGraph (μ := μ) hb hΩ f hf)),
    ← real_inner_self_eq_norm_sq (gradL (smoothGraph (μ := μ) hb hΩ f hf))]
  change inner ℝ _ _ + inner ℝ _ _ = _
  dsimp only [smoothGraph]
  rw [fnL_mk, gradL_mk, inner_toLp_toLp, inner_toLp_toLp]
  simp [sq]

end HitAndRun.Sobolev
