module
public import KLS15
public import UniformBridge
@[expose] public section
noncomputable section
open MeasureTheory
open HitAndRun.Sobolev
open HitAndRun.Sobolev.BoundedOpenDomain
namespace KLS15ProductionAudit
variable {n : ℕ} [NeZero n]
theorem actualUniform15 (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier) :
    OAI.LeanBlast.KLS.PoincareBound
      (OAI.LeanBlast.KLS.densityMeasure K.whitenedDomain.uniformDensity) 15 :=
  KLS15.openaiPoincare15 (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
    (K.whitenedDomain.uniformDensity_oai_logConcave (K.whitenedDomain_convex hc))
    K.whitened_uniformDensity_oai_isotropic

theorem actualSobolev15 (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier) :
    K.poincareConstant ≤ ENNReal.ofReal (15 * ‖K.centeredCovarianceOperator‖) :=
  K.poincareConstant_le_fifteen_covariance_of_oai hc (actualUniform15 K hc)

theorem actualSobolev15_real (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier) :
    K.poincareConstant.toReal ≤ 15 * ‖K.centeredCovarianceOperator‖ :=
  K.poincareConstant_toReal_le_fifteen_covariance_of_oai hc (actualUniform15 K hc)
#print axioms actualUniform15
#print axioms actualSobolev15
#print axioms actualSobolev15_real
end KLS15ProductionAudit
