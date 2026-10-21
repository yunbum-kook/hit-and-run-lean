import HitAndRun.Sobolev.LinearImagePoincareWhitening
noncomputable section
open MeasureTheory HitAndRun.Sobolev EllipticPdes EllipticPdes.H1Graph
open HitAndRun.Sobolev.BoundedOpenDomain
open scoped ENNReal
variable {n : ℕ} [NeZero n]
example (K : BoundedOpenDomain n) (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (u : (K.linearImage L).H1) : K.linearImageGraph L u.val ∈ W12 K.ambient K.carrier :=
  K.linearImageGraph_mem_W12 L u
example (K : BoundedOpenDomain n) (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {C : ℝ≥0∞} (h : K.IsPoincareConstant C) :
    (K.linearImage L).IsPoincareConstant (ENNReal.ofReal (‖L.toContinuousLinearMap‖^2) * C) :=
  h.linearImage K L
example (K : BoundedOpenDomain n) (hfin : K.whitenedDomain.poincareConstant < ⊤) :
    K.poincareConstant ≤ ENNReal.ofReal ‖K.centeredCovarianceOperator‖ *
      K.whitenedDomain.poincareConstant := K.poincareConstant_le_whitened hfin
example (K : BoundedOpenDomain n) :
    ‖K.covarianceWhiteningContinuousEquiv.symm.toContinuousLinearMap‖^2 =
      ‖K.centeredCovarianceOperator‖ := K.covarianceWhitening_inverse_norm_sq
#print axioms linearImageTest_fderiv
#print axioms linearImageGraph_mem_W12
#print axioms linearImageH1_variance
#print axioms linearImageH1_gradientEnergy
#print axioms IsPoincareConstant.linearImage
#print axioms poincareConstant_le_linearImage
#print axioms covarianceWhitening_inverse_factor
#print axioms covarianceWhitening_inverse_norm_sq
#print axioms poincareConstant_le_whitened
example (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier) :
    K.poincareConstant ≤ ENNReal.ofReal ‖K.centeredCovarianceOperator‖ *
      K.whitenedDomain.poincareConstant := K.poincareConstant_le_whitened_convex hc
#print axioms whitenedDomain_convex
#print axioms poincareConstant_le_whitened_convex
