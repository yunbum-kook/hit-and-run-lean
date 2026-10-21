module
public import CvxBody.Geometry.PositiveMatrixSpectral

@[expose] public section


/-! The literal log-determinant inequalities used for Fatou in the nonsmooth
transport argument. Both are proved from the actual Hermitian eigenvalues. -/
noncomputable section
namespace CvxBody.Geometry
/-- The source P10.6 uniform lower bound, valid even for a singular Hessian. -/
theorem positiveMatrix_logDet_half_one_add_lower (d : ℕ)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) :
    -(d : ℝ) * Real.log 2 ≤ Real.log (((1/2:ℝ) • (1+A)).det) := by
  rw [positiveMatrix_half_one_add_det_spectral A hA, Real.log_prod]
  · calc
      -(d : ℝ)*Real.log 2 = ∑ _i : Fin d, -(Real.log 2) := by simp
      _ ≤ ∑ i : Fin d, Real.log ((1+hA.isHermitian.eigenvalues i)/2) := by
        apply Finset.sum_le_sum
        intro i _
        have he := hA.eigenvalues_nonneg i
        have hlog := Real.log_le_log (by norm_num : (0:ℝ)<1/2)
          (show (1/2:ℝ) ≤ (1+hA.isHermitian.eigenvalues i)/2 by linarith)
        simpa using hlog
  · intro i _
    have he := hA.eigenvalues_nonneg i
    positivity
/-- P10.6 log-determinant comparison at the positive definite Alexandrov Hessian. -/
theorem positiveMatrix_logDet_le_twice_half_one_add (d : ℕ)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) :
    Real.log A.det ≤ 2 * Real.log (((1/2:ℝ) • (1+A)).det) := by
  have hs := hA.posSemidef
  rw [hA.isHermitian.det_eq_prod_eigenvalues,
    positiveMatrix_half_one_add_det_spectral A hs, Real.log_prod, Real.log_prod,
    Finset.mul_sum]
  · apply Finset.sum_le_sum
    intro i _
    have hi := hA.eigenvalues_pos i
    have hb : 0 < (1+hA.isHermitian.eigenvalues i)/2 := by positivity
    have hsq : hA.isHermitian.eigenvalues i ≤ ((1+hA.isHermitian.eigenvalues i)/2)^2 := by
      nlinarith [sq_nonneg (hA.isHermitian.eigenvalues i-1)]
    have hlog := Real.log_le_log hi hsq
    rw [Real.log_pow] at hlog
    simpa using hlog
  · intro i _
    have hi := hs.eigenvalues_nonneg i
    positivity
  · intro i _
    exact (hA.eigenvalues_pos i).ne'
end CvxBody.Geometry
