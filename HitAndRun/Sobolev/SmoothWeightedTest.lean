module
public import HitAndRun.Sobolev.SmoothWeightedGradient
public import HitAndRun.Sobolev.WeightedTestFunctional

/-! Smooth weighted gradients represent the actual finite vector-test
functional. This is the pairing needed before taking the rough-data limit. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

def smoothWeightedGradientOn (hb : Bornology.IsBounded Ω)
    (h : E → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) : Lp E 2 (μ.restrict Ω) :=
  ((weightedGradient_memLp (μ := μ) hb h hh).restrict Ω).toLp _

theorem smooth_weighted_test_pairing (hb : Bornology.IsBounded Ω)
    (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (h : E → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (φ : testFunctions Ω) (v : E) :
    inner ℝ (smoothWeightedGradientOn (μ := μ) hb h hh) (boundaryFieldClass ho hc φ v) =
      -inner ℝ (fnL (smoothGraph (μ := μ) hb ho h hh)) (partialCls μ Ω φ v) := by
  have he : inner ℝ (smoothWeightedGradientOn (μ := μ) hb h hh) (boundaryFieldClass ho hc φ v) =
      inner ℝ (gradL (smoothGraph (μ := μ) hb ho h hh)) (smulCls μ Ω φ v) := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [((weightedGradient_memLp (μ := μ) hb h hh).restrict Ω).coeFn_toLp,
      coeFn_boundaryFieldClass (μ := μ) ho hc φ v,
      smoothGraph_grad (μ := μ) hb ho h hh, coeFn_smulCls (μ := μ) φ v] with x ha hbc hg hv
    change (smoothWeightedGradientOn (μ := μ) hb h hh : E → E) x = _ at ha
    rw [ha, hbc, hg, hv]
    by_cases hx : (φ : E → ℝ) x = 0
    · simp [boundaryTest, hx]
    have hm : x ∈ Ω := φ.2.2.2 (subset_closure hx)
    have hd : interiorDistance Ω x ≠ 0 := ne_of_gt
      ((ho.isClosed_compl.notMem_iff_infDist_pos hc).mp (by simpa using hm))
    simp only [boundaryTest, real_inner_smul_left, real_inner_smul_right]
    field_simp
  rw [he]
  have hz := (mem_W12_iff _).mp (smoothGraph_mem_W12 (μ := μ) hb ho h hh) φ v
  rw [inner_constraintVec] at hz
  have hp : inner ℝ (partialCls μ Ω φ v) (fnL (smoothGraph (μ := μ) hb ho h hh)) =
      inner ℝ (fnL (smoothGraph (μ := μ) hb ho h hh)) (partialCls μ Ω φ v) := real_inner_comm _ _
  have hg : inner ℝ (smulCls μ Ω φ v) (gradL (smoothGraph (μ := μ) hb ho h hh)) =
      inner ℝ (gradL (smoothGraph (μ := μ) hb ho h hh)) (smulCls μ Ω φ v) := real_inner_comm _ _
  linarith
theorem norm_smoothWeightedGradientOn_le (hb : Bornology.IsBounded Ω)
    (h : E → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ‖smoothWeightedGradientOn (μ := μ) hb h hh‖ ≤ ‖smoothWeightedGradient (μ := μ) hb h hh‖ := by
  rw [smoothWeightedGradientOn, smoothWeightedGradient, Lp.norm_toLp, Lp.norm_toLp]
  exact ENNReal.toReal_mono (weightedGradient_memLp (μ := μ) hb h hh).eLpNorm_ne_top
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

theorem smooth_weighted_vector_pairing {ι : Type*} [Fintype ι]
    (hb : Bornology.IsBounded Ω) (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (h : E → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (b : ι → E) (φ : ι → testFunctions Ω) :
    inner ℝ (smoothWeightedGradientOn (μ := μ) hb h hh)
      (vectorTestCoefficient (μ := μ) ho hc b φ) =
      vectorTestFunctional (fnL (smoothGraph (μ := μ) hb ho h hh)) b φ := by
  simp only [vectorTestCoefficient, vectorTestFunctional, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.neg_apply,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_sum]
  change (∑ i, inner ℝ (smoothWeightedGradientOn (μ := μ) hb h hh)
    (boundaryFieldClass ho hc (φ i) (b i))) =
    -(∑ i, inner ℝ (fnL (smoothGraph (μ := μ) hb ho h hh))
      (partialL (b i) (testGraphₗ μ Ω (φ i))))
  simp_rw [partialL_testGraphₗ, smooth_weighted_test_pairing hb ho hc h hh]
  simp only [Finset.sum_neg_distrib]

theorem smooth_weighted_vector_bound {ι : Type*} [Fintype ι]
    (hb : Bornology.IsBounded Ω) (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (h : E → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (b : ι → E) (φ : ι → testFunctions Ω) :
    |vectorTestFunctional (fnL (smoothGraph (μ := μ) hb ho h hh)) b φ| ≤
      ‖smoothWeightedGradient (μ := μ) hb h hh‖ * ‖vectorTestCoefficient (μ := μ) ho hc b φ‖ := by
  rw [← smooth_weighted_vector_pairing hb ho hc h hh b φ]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_smoothWeightedGradientOn_le hb h hh) (norm_nonneg _))

end HitAndRun.Sobolev
