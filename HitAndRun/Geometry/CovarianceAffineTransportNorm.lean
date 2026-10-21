module
public import HitAndRun.Geometry.CovarianceAffineTransportWhitening
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
variable {n : ℕ} [NeZero n]

theorem covarianceWhitening_inverse_factor (K : BoundedOpenDomain n) :
    K.covarianceWhiteningContinuousEquiv.symm.toContinuousLinearMap.comp
      K.covarianceWhiteningContinuousEquiv.symm.toContinuousLinearMap.adjoint =
        K.centeredCovarianceOperator := by
  let W := K.covarianceWhiteningContinuousEquiv
  have hi : W.symm.toContinuousLinearMap.comp W.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ _ := by
    apply ContinuousLinearMap.ext
    intro x
    exact W.symm_apply_apply x
  have ha : W.toContinuousLinearMap.adjoint.comp W.symm.toContinuousLinearMap.adjoint =
      ContinuousLinearMap.id ℝ _ := by
    rw [← ContinuousLinearMap.adjoint_comp, hi, ContinuousLinearMap.adjoint_id]
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg (fun A => W.symm (A (W.symm.toContinuousLinearMap.adjoint x)))
    K.covarianceWhiteningEquiv_identity
  change W.symm (W (K.centeredCovarianceOperator
      (W.toContinuousLinearMap.adjoint (W.symm.toContinuousLinearMap.adjoint x)))) = _ at h
  have hx := congrArg (fun A : _ →L[ℝ] _ => A x) ha
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hx
  rw [hx, W.symm_apply_apply] at h
  exact h.symm

theorem covarianceWhitening_inverse_norm_sq (K : BoundedOpenDomain n) :
    ‖K.covarianceWhiteningContinuousEquiv.symm.toContinuousLinearMap‖^2 =
      ‖K.centeredCovarianceOperator‖ := by
  have h := ContinuousLinearMap.norm_adjoint_comp_self
    K.covarianceWhiteningContinuousEquiv.symm.toContinuousLinearMap.adjoint
  rw [ContinuousLinearMap.adjoint_adjoint, K.covarianceWhitening_inverse_factor,
    LinearIsometryEquiv.norm_map] at h
  simpa only [pow_two] using h.symm
end HitAndRun.Sobolev.BoundedOpenDomain
