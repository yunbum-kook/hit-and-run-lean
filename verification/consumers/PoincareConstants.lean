module
import HitAndRun.Sobolev.PoincareConstants
open MeasureTheory ProbabilityTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Sobolev
open scoped ENNReal
variable {n : ℕ} [NeZero n]
example (K : BoundedOpenDomain n) (u : K.H1) :
    K.gradientEnergy u = ∫⁻ x, ‖gradL (u : H1Graph K.ambient K.carrier) x‖ₑ ^ 2
      ∂K.ambient.restrict K.carrier := K.gradientEnergy_eq_lintegral u
example (K : BoundedOpenDomain n) (u : K.H1) :
    K.weightedGradientEnergy u =
      ∫⁻ x, ENNReal.ofReal (Metric.infDist x (frontier K.carrier) ^ 2) *
        ‖gradL (u : H1Graph K.ambient K.carrier) x‖ₑ ^ 2
          ∂K.ambient.restrict K.carrier := rfl
example (K : BoundedOpenDomain n) (h : K.poincareConstant < ⊤) (u : K.H1) :
    evariance (fnL (u : H1Graph K.ambient K.carrier)) (K.ambient.restrict K.carrier) ≤
      K.poincareConstant * ∫⁻ x, ‖gradL (u : H1Graph K.ambient K.carrier) x‖ₑ ^ 2
        ∂K.ambient.restrict K.carrier := by
  rw [← K.gradientEnergy_eq_lintegral u]
  exact K.poincareConstant_admissible_of_lt_top h u
example (K : BoundedOpenDomain n) (h : K.improvedPoincareConstant < ⊤) (u : K.H1) :
    evariance (fnL (u : H1Graph K.ambient K.carrier)) (K.ambient.restrict K.carrier) ≤
      K.improvedPoincareConstant *
        ∫⁻ x, ENNReal.ofReal (Metric.infDist x (frontier K.carrier) ^ 2) *
          ‖gradL (u : H1Graph K.ambient K.carrier) x‖ₑ ^ 2
            ∂K.ambient.restrict K.carrier := K.improvedPoincareConstant_admissible_of_lt_top h u
#print axioms BoundedOpenDomain.gradientEnergy_eq_lintegral
#print axioms BoundedOpenDomain.varianceEnergy_ne_top
#print axioms BoundedOpenDomain.gradientEnergy_ne_top
#print axioms BoundedOpenDomain.boundaryDistance_bounded
#print axioms BoundedOpenDomain.weightedGradientEnergy_ne_top
#print axioms BoundedOpenDomain.energy_bound_sInf
#print axioms BoundedOpenDomain.poincareConstant_admissible
#print axioms BoundedOpenDomain.poincareConstant_admissible_of_lt_top
#print axioms BoundedOpenDomain.improvedPoincareConstant_admissible
#print axioms BoundedOpenDomain.improvedPoincareConstant_admissible_of_lt_top
#print axioms BoundedOpenDomain.varianceEnergy_eq_uniform
