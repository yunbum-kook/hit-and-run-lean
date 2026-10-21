module
import HitAndRun.Sobolev.WeightedGradientEnergyIdentity
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Sobolev
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (u : K.H1)
    (w : Lp (EuclideanSpace ℝ (Fin n)) 2 (K.ambient.restrict K.carrier))
    (hw : (fun x => K.boundaryDistance x • gradL (u : H1Graph K.ambient K.carrier) x)
      =ᵐ[K.ambient.restrict K.carrier] (w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) :
    (K.weightedGradientEnergy u).toReal = ‖w‖ ^ 2 :=
  K.weightedGradientEnergy_toReal_eq_norm_sq_of_ae u w hw
#print axioms BoundedOpenDomain.weightedGradientEnergy_eq_ofReal_norm_sq_of_ae
#print axioms BoundedOpenDomain.weightedGradientEnergy_toReal_eq_norm_sq_of_ae
