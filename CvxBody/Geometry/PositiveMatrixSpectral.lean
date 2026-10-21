module
public import CvxBody.Geometry.PositiveMatrixContinuous

@[expose] public section


/-! Exact determinant and inverse-quadratic formulas in the canonical
orthonormal eigenbasis of the source positive semidefinite matrix. -/
noncomputable section
open Matrix
open scoped RealInnerProductSpace
namespace CvxBody.Geometry
variable {d : ℕ}

private lemma positiveMatrix_eigenvector_action_aux (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) (i : Fin d) :
    A.toEuclideanLin (hA.isHermitian.eigenvectorBasis i) =
      (hA.isHermitian.eigenvalues i) • (hA.isHermitian.eigenvectorBasis i) := by
  apply PiLp.ext
  intro j
  change (A *ᵥ (hA.isHermitian.eigenvectorBasis i).ofLp) j =
    (hA.isHermitian.eigenvalues i) * (hA.isHermitian.eigenvectorBasis i) j
  exact congrFun (hA.isHermitian.mulVec_eigenvectorBasis i) j

private lemma positiveMatrix_shifted_eigenvector_action_aux (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) (i : Fin d) :
    (1+A).toEuclideanLin (hA.isHermitian.eigenvectorBasis i) =
      (1+hA.isHermitian.eigenvalues i) • (hA.isHermitian.eigenvectorBasis i) := by
  calc
    _ = (hA.isHermitian.eigenvectorBasis i) +
        A.toEuclideanLin (hA.isHermitian.eigenvectorBasis i) := by
      rw [map_add,LinearMap.add_apply]
      change (Matrix.toLpLin 2 2 1) _+_ = _
      rw [Matrix.toLpLin_one,LinearMap.id_apply]
    _ = _ := by rw [positiveMatrix_eigenvector_action_aux A hA i]; module

private lemma positiveMatrix_repr_shifted_action_aux (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) (ξ : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    hA.isHermitian.eigenvectorBasis.repr ((1+A).toEuclideanLin ξ) i =
      (1+hA.isHermitian.eigenvalues i) * hA.isHermitian.eigenvectorBasis.repr ξ i := by
  let b := hA.isHermitian.eigenvectorBasis
  have hsymm := isSymmetric_toEuclideanLin_iff.mpr (positiveMatrix_one_add_posDef A hA).isHermitian
  rw [OrthonormalBasis.repr_apply_apply,← hsymm (b i) ξ,
    positiveMatrix_shifted_eigenvector_action_aux A hA i,real_inner_smul_left,
    ← OrthonormalBasis.repr_apply_apply]

/-- The determinant has precisely the product normalization used in the actual
one-dimensional Gaussian factors. -/
theorem positiveMatrix_half_one_add_det_spectral (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) :
    ((1/2:ℝ) • (1+A)).det = ∏ i, (1+hA.isHermitian.eigenvalues i)/2 := by
  let b := hA.isHermitian.eigenvectorBasis
  let M := (1/2:ℝ) • (1+A)
  have heigen (j : Fin d) : M.toEuclideanLin (b j) =
      ((1+hA.isHermitian.eigenvalues j)/2) • b j := by
    dsimp only [M]
    rw [map_smul,LinearMap.smul_apply,positiveMatrix_shifted_eigenvector_action_aux A hA j,smul_smul]
    congr 1
    ring
  have hdiag : LinearMap.toMatrix b.toBasis b.toBasis M.toEuclideanLin =
      Matrix.diagonal (fun i => (1+hA.isHermitian.eigenvalues i)/2) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change b.repr (M.toEuclideanLin (b j)) i = _
    rw [heigen,b.repr.map_smul]
    simp only [OrthonormalBasis.repr_self,PiLp.smul_apply,PiLp.single_apply,
      Matrix.diagonal_apply,smul_eq_mul]
    split_ifs with hij
    · subst j
      simp
    · simp
  calc
    _ = M.toEuclideanLin.det := (LinearMap.det_toLpLin 2 M).symm
    _ = (LinearMap.toMatrix b.toBasis b.toBasis M.toEuclideanLin).det :=
      (LinearMap.det_toMatrix b.toBasis M.toEuclideanLin).symm
    _ = _ := by rw [hdiag,Matrix.det_diagonal]

/-- The inverse quadratic form has the exact source eigenvalue denominators,
with no assumed diagonalization or inverse identity. -/
theorem positiveMatrix_inverse_quadratic_spectral (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) (ξ : EuclideanSpace ℝ (Fin d)) :
    inner ℝ ξ ((1+A)⁻¹.toEuclideanLin ξ) =
      ∑ i, ((hA.isHermitian.eigenvectorBasis.repr ξ i)^2)/(1+hA.isHermitian.eigenvalues i) := by
  let b := hA.isHermitian.eigenvectorBasis
  let M := 1+A
  let ζ := M⁻¹.toEuclideanLin ξ
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr (positiveMatrix_one_add_posDef A hA).det_pos.ne'
  have hMζ : M.toEuclideanLin ζ = ξ := by
    apply PiLp.ext
    intro i
    change (M *ᵥ (M⁻¹ *ᵥ ξ.ofLp)) i = ξ i
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hdet,Matrix.one_mulVec]
  have hrepr (i : Fin d) : b.repr ζ i = b.repr ξ i/(1+hA.isHermitian.eigenvalues i) := by
    have hi := congrArg (fun v => b.repr v i) hMζ
    change b.repr ((1+A).toEuclideanLin ζ) i = b.repr ξ i at hi
    rw [positiveMatrix_repr_shifted_action_aux A hA ζ i] at hi
    have hα : 0 < 1+hA.isHermitian.eigenvalues i := by
      linarith [hA.eigenvalues_nonneg i]
    apply (eq_div_iff hα.ne').mpr
    exact (mul_comm _ _).trans hi
  calc
    _ = inner ℝ (b.repr ξ) (b.repr ζ) := (b.repr.inner_map_map ξ ζ).symm
    _ = _ := by
      change (b.repr ζ).ofLp ⬝ᵥ (b.repr ξ).ofLp = _
      apply Finset.sum_congr rfl
      intro i _
      change b.repr ζ i * b.repr ξ i = _
      rw [hrepr]
      ring
end CvxBody.Geometry
