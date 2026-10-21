module
public import HitAndRun.Sobolev.WeightedPoincareTransferEnergy

/-! Actual weighted weak-gradient energy equals the L2 energy of its representative. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph
namespace BoundedOpenDomain
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

theorem weightedGradientEnergy_eq_ofReal_norm_sq_of_ae (u : K.H1)
    (w : Lp (EuclideanSpace ℝ (Fin n)) 2 (K.ambient.restrict K.carrier))
    (hw : (fun x => K.boundaryDistance x • gradL (u : H1Graph K.ambient K.carrier) x)
      =ᵐ[K.ambient.restrict K.carrier] (w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) :
    K.weightedGradientEnergy u = ENNReal.ofReal (‖w‖ ^ 2) := by
  have he : K.boundaryMultiplier (gradL (u : H1Graph K.ambient K.carrier)) = w :=
    Lp.ext ((K.boundaryMultiplier_ae _).trans hw)
  rw [K.weightedGradientEnergy_eq_norm, he]

theorem weightedGradientEnergy_toReal_eq_norm_sq_of_ae (u : K.H1)
    (w : Lp (EuclideanSpace ℝ (Fin n)) 2 (K.ambient.restrict K.carrier))
    (hw : (fun x => K.boundaryDistance x • gradL (u : H1Graph K.ambient K.carrier) x)
      =ᵐ[K.ambient.restrict K.carrier] (w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) :
    (K.weightedGradientEnergy u).toReal = ‖w‖ ^ 2 := by
  rw [K.weightedGradientEnergy_eq_ofReal_norm_sq_of_ae u w hw,
    ENNReal.toReal_ofReal (sq_nonneg _)]
end BoundedOpenDomain
end HitAndRun.Sobolev
