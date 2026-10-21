module
public import HitAndRun.Geometry.CovarianceNondegenerate
public import Mathlib.Analysis.Matrix.Order
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open Matrix
open scoped MatrixOrder
variable {n : ℕ} [NeZero n]

/-- Matrix representation of the actual centered covariance in Euclidean coordinates. -/
def centeredCovarianceMatrix (K : BoundedOpenDomain n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.toEuclideanLin.symm K.centeredCovarianceOperator.toLinearMap

@[simp] theorem toEuclideanLin_centeredCovarianceMatrix (K : BoundedOpenDomain n) :
    K.centeredCovarianceMatrix.toEuclideanLin = K.centeredCovarianceOperator.toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply _

theorem centeredCovarianceMatrix_posDef (K : BoundedOpenDomain n) :
    K.centeredCovarianceMatrix.PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · rw [← Matrix.isSymmetric_toEuclideanLin_iff, K.toEuclideanLin_centeredCovarianceMatrix]
    exact K.centeredCovarianceOperator_positive.isSymmetric
  · intro x hx
    have hne : WithLp.toLp 2 x ≠ (0 : EuclideanSpace ℝ (Fin n)) := by
      simpa using hx
    have hp := K.centeredCovarianceOperator_inner_pos (WithLp.toLp 2 x) hne
    change 0 < inner ℝ (K.centeredCovarianceOperator.toLinearMap (WithLp.toLp 2 x))
      (WithLp.toLp 2 x) at hp
    rw [← K.toEuclideanLin_centeredCovarianceMatrix] at hp
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply] at hp
    simpa [PiLp.inner_apply, dotProduct, mul_comm] using hp

/-- The positive square root of the centered covariance matrix. -/
def covarianceSqrtMatrix (K : BoundedOpenDomain n) : Matrix (Fin n) (Fin n) ℝ :=
  CFC.sqrt K.centeredCovarianceMatrix

theorem covarianceSqrtMatrix_mul_self (K : BoundedOpenDomain n) :
    K.covarianceSqrtMatrix * K.covarianceSqrtMatrix = K.centeredCovarianceMatrix :=
  CFC.sqrt_mul_sqrt_self _ K.centeredCovarianceMatrix_posDef.posSemidef.nonneg

theorem covarianceSqrtMatrix_isUnit (K : BoundedOpenDomain n) :
    IsUnit K.covarianceSqrtMatrix :=
  (CFC.isUnit_sqrt_iff _ K.centeredCovarianceMatrix_posDef.posSemidef.nonneg).mpr
    K.centeredCovarianceMatrix_posDef.isUnit

/-- Concrete inverse square root, not an assumed whitening map. -/
def covarianceWhiteningMatrix (K : BoundedOpenDomain n) : Matrix (Fin n) (Fin n) ℝ :=
  K.covarianceSqrtMatrix⁻¹

theorem covarianceWhiteningMatrix_transpose (K : BoundedOpenDomain n) :
    K.covarianceWhiteningMatrix.transpose = K.covarianceWhiteningMatrix := by
  have h := (CFC.sqrt_nonneg K.centeredCovarianceMatrix).posSemidef.inv.isHermitian.eq
  change K.covarianceWhiteningMatrix.conjTranspose = K.covarianceWhiteningMatrix at h
  simpa using h

theorem covarianceWhiteningMatrix_mul_sqrt (K : BoundedOpenDomain n) :
    K.covarianceWhiteningMatrix * K.covarianceSqrtMatrix = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp K.covarianceSqrtMatrix_isUnit)

theorem covarianceSqrtMatrix_mul_whitening (K : BoundedOpenDomain n) :
    K.covarianceSqrtMatrix * K.covarianceWhiteningMatrix = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp K.covarianceSqrtMatrix_isUnit)

/-- Exact whitening identity for the actual centered covariance. -/
theorem covarianceWhiteningMatrix_identity (K : BoundedOpenDomain n) :
    K.covarianceWhiteningMatrix * K.centeredCovarianceMatrix *
      K.covarianceWhiteningMatrix.transpose = 1 := by
  rw [K.covarianceWhiteningMatrix_transpose, ← K.covarianceSqrtMatrix_mul_self,
    ← Matrix.mul_assoc, K.covarianceWhiteningMatrix_mul_sqrt, Matrix.one_mul,
    K.covarianceSqrtMatrix_mul_whitening]

/-- An explicit linear equivalence, with the covariance square root as its inverse. -/
def covarianceWhiteningEquiv (K : BoundedOpenDomain n) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearEquiv.ofLinearMap K.covarianceWhiteningMatrix.toEuclideanLin
    K.covarianceSqrtMatrix.toEuclideanLin
    (by rw [← Matrix.toLpLin_mul_same, K.covarianceWhiteningMatrix_mul_sqrt,
      Matrix.toLpLin_one])
    (by rw [← Matrix.toLpLin_mul_same, K.covarianceSqrtMatrix_mul_whitening,
      Matrix.toLpLin_one])

@[simp] theorem covarianceWhiteningEquiv_toLinearMap (K : BoundedOpenDomain n) :
    K.covarianceWhiteningEquiv.toLinearMap = K.covarianceWhiteningMatrix.toEuclideanLin := rfl

/-- Operator-level whitening, expressed with the genuine Euclidean adjoint. -/
theorem covarianceWhiteningEquiv_identity (K : BoundedOpenDomain n) :
    K.covarianceWhiteningEquiv.toLinearMap ∘ₗ K.centeredCovarianceOperator.toLinearMap ∘ₗ
      K.covarianceWhiteningEquiv.toLinearMap.adjoint = LinearMap.id := by
  rw [K.covarianceWhiteningEquiv_toLinearMap,
    ← K.toEuclideanLin_centeredCovarianceMatrix,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  have hm : K.covarianceWhiteningMatrix.conjTranspose =
      K.covarianceWhiteningMatrix.transpose := by simp
  rw [hm, ← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same,
    ← Matrix.mul_assoc, K.covarianceWhiteningMatrix_identity, Matrix.toLpLin_one]

/-- Finite-dimensional continuity upgrades the whitening equivalence for transport. -/
def covarianceWhiteningContinuousEquiv (K : BoundedOpenDomain n) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  K.covarianceWhiteningEquiv.toContinuousLinearEquiv

@[simp] theorem covarianceWhiteningContinuousEquiv_toLinearMap (K : BoundedOpenDomain n) :
    K.covarianceWhiteningContinuousEquiv.toLinearEquiv.toLinearMap =
      K.covarianceWhiteningEquiv.toLinearMap := rfl

end HitAndRun.Sobolev.BoundedOpenDomain
