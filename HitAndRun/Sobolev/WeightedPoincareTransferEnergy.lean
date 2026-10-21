module
public import HitAndRun.Sobolev.ImprovedPoincareLimit
public import Mathlib.MeasureTheory.Function.Holder
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory ProbabilityTheory EllipticPdes EllipticPdes.H1Graph Filter
open scoped ENNReal NNReal Topology
namespace BoundedOpenDomain
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

/-- The actual boundary distance is an essentially bounded multiplier. -/
theorem boundaryDistance_memLp_top :
    MemLp K.boundaryDistance ⊤ (K.ambient.restrict K.carrier) := by
  obtain ⟨R, hR, hbound⟩ := K.boundaryDistance_bounded
  apply MemLp.of_bound ((Metric.continuous_infDist_pt (frontier K.carrier)).aestronglyMeasurable) R
  filter_upwards [ae_restrict_mem K.isOpen.measurableSet] with x hx
  simpa only [boundaryDistance, Real.norm_eq_abs, abs_of_nonneg Metric.infDist_nonneg]
    using hbound x hx

def boundaryWeight : Lp ℝ ⊤ (K.ambient.restrict K.carrier) :=
  K.boundaryDistance_memLp_top.toLp K.boundaryDistance

/-- Multiplication by distance to the frontier, as a genuine bounded L2 operator. -/
def boundaryMultiplier :
    Lp (EuclideanSpace ℝ (Fin n)) 2 (K.ambient.restrict K.carrier) →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin n)) 2 (K.ambient.restrict K.carrier) :=
  LinearMap.mkContinuous
    { toFun := fun g => K.boundaryWeight • g
      map_add' := fun g h => Lp.add_smul _ _ _
      map_smul' := fun c g => by simpa using (Lp.smul_comm c K.boundaryWeight g).symm }
    ‖K.boundaryWeight‖ (fun g => Lp.norm_smul_le _ _)

theorem boundaryMultiplier_ae
    (g : Lp (EuclideanSpace ℝ (Fin n)) 2 (K.ambient.restrict K.carrier)) :
    K.boundaryMultiplier g =ᵐ[K.ambient.restrict K.carrier]
      fun x => K.boundaryDistance x • g x := by
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) K.boundaryWeight g,
    K.boundaryDistance_memLp_top.coeFn_toLp] with x hx hw
  change (K.boundaryWeight • g : Lp _ 2 _) x = K.boundaryDistance x • g x
  change (K.boundaryWeight • g : Lp _ 2 _) x = K.boundaryWeight x • g x at hx
  change K.boundaryWeight x = K.boundaryDistance x at hw
  rw [hx, hw]

theorem weightedGradientEnergy_eq_norm (u : K.H1) :
    K.weightedGradientEnergy u =
      ENNReal.ofReal (‖K.boundaryMultiplier (gradL u.val)‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, Lp.enorm_def]
  have he := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    (Lp.aestronglyMeasurable (K.boundaryMultiplier (gradL u.val)))
  have he' : eLpNorm (K.boundaryMultiplier (gradL u.val)) 2 (K.ambient.restrict K.carrier) ^ (2 : ℕ) =
      ∫⁻ x, ‖K.boundaryMultiplier (gradL u.val) x‖ₑ ^ (2 : ℕ) ∂K.ambient.restrict K.carrier := by
    simpa using he
  rw [he']
  apply lintegral_congr_ae
  filter_upwards [K.boundaryMultiplier_ae (gradL u.val)] with x hx
  rw [hx, enorm_smul, mul_pow]
  congr 1
  rw [ENNReal.ofReal_pow (show 0 ≤ K.boundaryDistance x from Metric.infDist_nonneg)]
  congr 1
  rw [← ofReal_norm]
  simp only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ K.boundaryDistance x from Metric.infDist_nonneg)]


theorem weightedGradientEnergy_tendsto {u : ℕ → K.H1} {v : K.H1}
    (hu : Tendsto (fun k => (u k).val) atTop (𝓝 v.val)) :
    Tendsto (fun k => (K.weightedGradientEnergy (u k)).toReal) atTop
      (𝓝 (K.weightedGradientEnergy v).toReal) := by
  simp_rw [K.weightedGradientEnergy_eq_norm, ENNReal.toReal_ofReal (sq_nonneg _)]
  exact (((K.boundaryMultiplier.continuous.comp gradL.continuous).tendsto v.val).comp hu).norm.pow 2
end BoundedOpenDomain
end HitAndRun.Sobolev
