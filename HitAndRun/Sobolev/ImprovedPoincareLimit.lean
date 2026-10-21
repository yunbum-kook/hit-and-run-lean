module
public import HitAndRun.Sobolev.PoincareConstants
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory ProbabilityTheory EllipticPdes EllipticPdes.H1Graph Filter
open scoped Topology RealInnerProductSpace
namespace BoundedOpenDomain
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

/-- Variance on actual uniform L2 is a continuous quadratic expression. -/
theorem lp_variance_eq (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    variance f (K.ambient.restrict K.carrier) =
      ‖f‖ ^ 2 - (meanCLM K.ambient K.carrier f) ^ 2 := by
  letI : IsProbabilityMeasure (K.ambient.restrict K.carrier) := by
    rw [K.measure_eq_uniform]
    exact uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  rw [variance_eq_sub (Lp.memLp f), meanCLM_eq_integral]
  congr 1
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  simp [RCLike.inner_apply, pow_two]

theorem continuous_lp_variance :
    Continuous (fun f : Lp ℝ 2 (K.ambient.restrict K.carrier) =>
      variance f (K.ambient.restrict K.carrier)) := by
  simp_rw [K.lp_variance_eq]
  exact (continuous_norm.pow 2).sub ((meanCLM K.ambient K.carrier).continuous.pow 2)

/-- Pass the actual H1 IPI to an L2 limit with convergent weighted energies.
No global H1 assertion is made about the limiting function. -/
theorem improvedPoincare_limit (hC : K.improvedPoincareConstant < ⊤)
    (u : ℕ → K.H1) (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) (R : ℝ)
    (hu : Tendsto (fun k => fnL (u k : H1Graph K.ambient K.carrier)) atTop (𝓝 f))
    (hE : Tendsto (fun k => (K.weightedGradientEnergy (u k)).toReal) atTop (𝓝 R)) :
    variance f (K.ambient.restrict K.carrier) ≤ K.improvedPoincareConstant.toReal * R := by
  have hbound (k : ℕ) : variance (fnL (u k : H1Graph K.ambient K.carrier))
      (K.ambient.restrict K.carrier) ≤ K.improvedPoincareConstant.toReal *
        (K.weightedGradientEnergy (u k)).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hC.ne (K.weightedGradientEnergy_ne_top (u k)))
      (K.improvedPoincareConstant_admissible_of_lt_top hC (u k))
    simpa only [varianceEnergy, variance, ENNReal.toReal_mul] using h
  exact le_of_tendsto_of_tendsto (K.continuous_lp_variance.tendsto f |>.comp hu)
    (tendsto_const_nhds.mul hE) (Filter.Eventually.of_forall hbound)

/-- Centered version used for the rough appendix residual. -/
theorem improvedPoincare_centered_limit (hC : K.improvedPoincareConstant < ⊤)
    (u : ℕ → K.H1) (f : K.Target) (R : ℝ)
    (hu : Tendsto (fun k => fnL (u k : H1Graph K.ambient K.carrier)) atTop (𝓝 f.val))
    (hE : Tendsto (fun k => (K.weightedGradientEnergy (u k)).toReal) atTop (𝓝 R)) :
    ‖f‖ ^ 2 ≤ K.improvedPoincareConstant.toReal * R := by
  have h := K.improvedPoincare_limit hC u f.val R hu hE
  rw [K.lp_variance_eq] at h
  have hm : meanCLM K.ambient K.carrier f.val = 0 := f.property
  simpa only [hm, zero_pow (by decide : 2 ≠ 0), sub_zero, Submodule.norm_coe] using h
end BoundedOpenDomain
end HitAndRun.Sobolev
