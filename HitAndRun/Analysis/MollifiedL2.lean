module
public import HitAndRun.External.EllipticPDE.Embedding.Convolution
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Actual L2 mollifications and their strong convergence, reusing the selected
probability-kernel Young inequality rather than assuming a smoothing operator. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Analysis
open MeasureTheory EllipticPdes EllipticPdes.Embedding Filter Topology
open scoped Convolution ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem memLp_normed_convolution_two (rho : ContDiffBump (0 : E))
    (f : Lp ℝ 2 μ) :
    MemLp (rho.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (f : E → ℝ)) 2 μ := by
  exact lt_of_le_of_lt
    (eLpNorm_convolution_le_of_integral_eq_one (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num) rho.nonneg_normed
      (rho.contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) (rho.normed μ)).continuous.aestronglyMeasurable
      rho.integral_normed (Lp.memLp f).aestronglyMeasurable)
    (Lp.memLp f).eLpNorm_lt_top

def mollifiedL2 (rho : ContDiffBump (0 : E)) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (memLp_normed_convolution_two rho f).toLp _

theorem coeFn_mollifiedL2 (rho : ContDiffBump (0 : E)) (f : Lp ℝ 2 μ) :
    (mollifiedL2 rho f : E → ℝ) =ᵐ[μ]
      rho.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (f : E → ℝ) :=
  (memLp_normed_convolution_two rho f).coeFn_toLp

theorem tendsto_mollifiedL2 {ι : Type*} {l : Filter ι}
    (rho : ι → ContDiffBump (0 : E)) (hr : Tendsto (fun i => (rho i).rOut) l (𝓝 0))
    (f : Lp ℝ 2 μ) : Tendsto (fun i => mollifiedL2 (rho i) f) l (𝓝 f) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have he (i : ι) : eLpNorm ((mollifiedL2 (rho i) f : E → ℝ) - (f : E → ℝ)) 2 μ =
      eLpNorm ((rho i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (f : E → ℝ) - (f : E → ℝ)) 2 μ :=
    eLpNorm_congr_ae ((coeFn_mollifiedL2 (rho i) f).sub Filter.EventuallyEq.rfl)
  simp_rw [he]
  exact tendsto_eLpNorm_normed_convolution_sub (by norm_num) (by norm_num) (Lp.memLp f) hr
end HitAndRun.Analysis
