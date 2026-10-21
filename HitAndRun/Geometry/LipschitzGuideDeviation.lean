module
public import HitAndRun.Geometry.WeightedPoincareLipschitzGraph
public import HitAndRun.Geometry.WeightedPoincareLipschitzLimit
public import HitAndRun.Sobolev.PoincareConstants
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory ProbabilityTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry
open scoped ENNReal NNReal
variable {n : ℕ} [NeZero n]

theorem lipschitz_guide_variance_le (K : BoundedOpenDomain n)
    (hfin : K.poincareConstant < ⊤) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : LipschitzWith 1 u) :
    variance u (uniformMeasure K.carrier) ≤ K.poincareConstant.toReal := by
  letI : IsProbabilityMeasure (K.ambient.restrict K.carrier) := by
    rw [K.measure_eq_uniform]
    exact uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  let U : K.H1 := locallyLipschitzH1 K.isBounded K.isOpen u hu.locallyLipschitz
  have he : K.gradientEnergy U ≤ 1 := by
    rw [K.gradientEnergy_eq_lintegral]
    calc
      _ ≤ ∫⁻ _x, (1 : ℝ≥0∞) ∂K.ambient.restrict K.carrier := by
        apply lintegral_mono_ae
        filter_upwards [locallyLipschitzGraph_grad (μ := K.ambient)
          K.isBounded K.isOpen u hu.locallyLipschitz] with x hx
        change ‖gradL (locallyLipschitzGraph K.isBounded K.isOpen u hu.locallyLipschitz) x‖ₑ ^ 2 ≤ 1
        rw [hx]
        have hg : ‖gradient u x‖ ≤ 1 := by
          simpa [gradient] using norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hu
        have hge : ‖gradient u x‖ₑ ≤ 1 := by
          simpa only [← ofReal_norm, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hg
        simpa using pow_le_pow_left' hge 2
      _ = 1 := by simp
  have hp := (K.poincareConstant_admissible_of_lt_top hfin U).trans
    (mul_le_mul_right he K.poincareConstant)
  rw [mul_one] at hp
  have hv : K.varianceEnergy U = evariance u (uniformMeasure K.carrier) := by
    rw [varianceEnergy]
    change evariance (fnL (locallyLipschitzGraph K.isBounded K.isOpen u hu.locallyLipschitz))
      (K.ambient.restrict K.carrier) = evariance u (uniformMeasure K.carrier)
    rw [evariance_congr (locallyLipschitzGraph_fn (μ := K.ambient)
      K.isBounded K.isOpen u hu.locallyLipschitz), K.measure_eq_uniform]
  rw [hv] at hp
  exact ENNReal.toReal_mono hfin.ne hp

theorem lipschitz_guide_mean_deviation_le (K : BoundedOpenDomain n)
    (hfin : K.poincareConstant < ⊤) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : LipschitzWith 1 u) :
    (∫ x, |u x - ∫ y, u y ∂uniformMeasure K.carrier| ∂uniformMeasure K.carrier) ≤
      Real.sqrt K.poincareConstant.toReal := by
  letI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  have hm : MemLp u 2 (uniformMeasure K.carrier) := by
    rw [← K.measure_eq_uniform]
    exact continuous_memLp_bounded_restrict K.isBounded K.isOpen.measurableSet hu.continuous
  have hs := integral_norm_le_sqrt_integral_sq
    (hm.sub (memLp_const (∫ y, u y ∂uniformMeasure K.carrier)))
  have he : (∫ x, ‖u x - ∫ y, u y ∂uniformMeasure K.carrier‖ ^ 2 ∂uniformMeasure K.carrier) =
      variance u (uniformMeasure K.carrier) := by
    rw [variance_eq_integral hm.aemeasurable]
    simp only [Real.norm_eq_abs, sq_abs]
  change (∫ x, ‖u x - ∫ y, u y ∂uniformMeasure K.carrier‖ ∂uniformMeasure K.carrier) ≤
    Real.sqrt (∫ x, ‖u x - ∫ y, u y ∂uniformMeasure K.carrier‖ ^ 2 ∂uniformMeasure K.carrier) at hs
  rw [he] at hs
  simpa only [Real.norm_eq_abs] using hs.trans
    (Real.sqrt_le_sqrt (K.lipschitz_guide_variance_le hfin u hu))
end HitAndRun.Sobolev.BoundedOpenDomain
