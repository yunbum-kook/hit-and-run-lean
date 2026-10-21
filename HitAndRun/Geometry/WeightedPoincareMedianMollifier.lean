module
public import HitAndRun.Geometry.WeightedPoincareMedianApproximation
public import HitAndRun.External.EllipticPDE.Embedding.Convolution
public import HitAndRun.External.EllipticPDE.Sobolev.Graph
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Filter Set EllipticPdes.Embedding EllipticPdes.H1Graph
open scoped Topology Convolution ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

lemma integral_norm_sq_eq_eLpNorm_toReal_sq {f : E → F} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal ^ 2 := by
  rw [← Lp.norm_toLp f hf, ← real_inner_self_eq_norm_sq]
  rw [inner_toLp_toLp]
  simp only [real_inner_self_eq_norm_sq]

lemma memLp_mollification_two (rho : ContDiffBump (0 : E))
    {f : E → F} (hf : MemLp f 2 μ) :
    MemLp (rho.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) 2 μ := by
  exact lt_of_le_of_lt
    (eLpNorm_convolution_le_of_integral_eq_one (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num) rho.nonneg_normed
      (rho.contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) (rho.normed μ)).continuous.aestronglyMeasurable
      rho.integral_normed hf.aestronglyMeasurable) hf.eLpNorm_lt_top

/-- Actual squared-L2 convergence of scalar or vector-valued mollification. -/
theorem integral_sq_mollification_sub_tendsto {f : E → F} (hf : MemLp f 2 μ)
    {rho : ℕ → ContDiffBump (0 : E)}
    (hr : Tendsto (fun k => (rho k).rOut) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖((rho k).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x - f x‖ ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have ht := tendsto_eLpNorm_normed_convolution_sub (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (by norm_num) hf hr
  have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp ht
  have he (k : ℕ) := integral_norm_sq_eq_eLpNorm_toReal_sq ((memLp_mollification_two (rho k) hf).sub hf)
  simp only [Pi.sub_apply] at he
  simp_rw [he]
  simpa using hreal.pow 2

/-- Mollify first, then move into the interior. Both actual L2 components of
an H1 graph can use this result, without assuming a regular boundary. -/
theorem integral_sq_mollification_dilation_sub_tendsto [μ.Regular]
    {K : Set E} [IsFiniteMeasure (μ.restrict K)] {f : E → F} (hf : MemLp f 2 μ)
    {rho : ℕ → ContDiffBump (0 : E)}
    (hr : Tendsto (fun k => (rho k).rOut) atTop (𝓝 0))
    {a : ℕ → ℝ} (ha0 : ∀ k, 0 < a k) (ha : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun k => ∫ x in K,
      ‖((rho k).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) (a k • x) - f x‖ ^ 2 ∂μ)
      atTop (𝓝 0) :=
  integral_sq_approx_dilation_sub_tendsto hf
    (fun k => memLp_mollification_two (rho k) hf)
    (integral_sq_mollification_sub_tendsto hf hr) ha0 ha
/-- The chain-rule dilation factor tends to one in the actual L2 error. -/
theorem integral_sq_smul_approx_sub_tendsto
    {ν : Measure E} {f : E → F} {g : ℕ → E → F}
    (hf : MemLp f 2 ν) (hg : ∀ k, MemLp (g k) 2 ν)
    (hgf : Tendsto (fun k => ∫ x, ‖g k x - f x‖ ^ 2 ∂ν) atTop (𝓝 0))
    {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun k => ∫ x, ‖a k • g k x - f x‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  have hupper : Tendsto (fun k =>
      2 * (a k)^2 * (∫ x, ‖g k x - f x‖^2 ∂ν) +
      2 * (a k - 1)^2 * (∫ x, ‖f x‖^2 ∂ν)) atTop (𝓝 0) := by
    have h1 := ((ha.pow 2).const_mul 2).mul hgf
    have h2 := (((ha.sub_const 1).pow 2).const_mul 2).mul_const (∫ x, ‖f x‖^2 ∂ν)
    simpa using h1.add h2
  apply squeeze_zero (fun k => integral_nonneg fun x => sq_nonneg _) _ hupper
  intro k
  have hi := integral_mono (((hg k).const_smul (a k)).sub hf).norm.integrable_sq
    ((((hg k).sub hf).norm.integrable_sq.const_mul (2 * (a k)^2)).add
      (hf.norm.integrable_sq.const_mul (2 * (a k - 1)^2))) (fun x => by
        have he : a k • g k x - f x = a k • (g k x - f x) + (a k - 1) • f x := by
          simp only [smul_sub, sub_smul, one_smul]; abel
        have ht := norm_add_le (a k • (g k x - f x)) ((a k - 1) • f x)
        rw [← he] at ht
        have hu : ‖a k • (g k x - f x)‖^2 = (a k)^2 * ‖g k x - f x‖^2 := by
          rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        have hv : ‖(a k - 1) • f x‖^2 = (a k - 1)^2 * ‖f x‖^2 := by
          rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at *
        nlinarith [norm_nonneg (a k • g k x - f x),
          norm_nonneg (a k • (g k x - f x)), norm_nonneg ((a k - 1) • f x),
          sq_nonneg (‖a k • (g k x - f x)‖ - ‖(a k - 1) • f x‖)])
  rw [integral_add' (((hg k).sub hf).norm.integrable_sq.const_mul (2 * (a k)^2))
    (hf.norm.integrable_sq.const_mul (2 * (a k - 1)^2)),
    integral_const_mul, integral_const_mul] at hi
  exact hi
/-- Domain-valued version uses zero extension internally and requires only
actual L2 membership on the domain. -/
theorem integral_sq_zeroExtension_mollification_dilation_sub_tendsto [μ.Regular]
    {K : Set E} [IsFiniteMeasure (μ.restrict K)] (hK : MeasurableSet K)
    {f : E → F} (hf : MemLp f 2 (μ.restrict K))
    {rho : ℕ → ContDiffBump (0 : E)}
    (hr : Tendsto (fun k => (rho k).rOut) atTop (𝓝 0))
    {a : ℕ → ℝ} (ha0 : ∀ k, 0 < a k) (ha : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun k => ∫ x in K,
      ‖((rho k).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] K.indicator f) (a k • x) - f x‖ ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have hext : MemLp (K.indicator f) 2 μ :=
    (memLp_indicator_iff_restrict hK.nullMeasurableSet).mpr hf
  have ht := integral_sq_mollification_dilation_sub_tendsto (K := K) hext hr ha0 ha
  have he (k : ℕ) :
      (∫ x in K, ‖((rho k).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] K.indicator f)
        (a k • x) - K.indicator f x‖ ^ 2 ∂μ) =
      (∫ x in K, ‖((rho k).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] K.indicator f)
        (a k • x) - f x‖ ^ 2 ∂μ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hK] with x hx
    rw [Set.indicator_of_mem hx]
  simpa only [he] using ht
end HitAndRun.Geometry
