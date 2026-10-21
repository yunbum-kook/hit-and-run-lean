module
public import CvxBody.Geometry.PositiveMatrixLogDet
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

open CvxBody.Geometry Filter Matrix
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace CvxBody.Geometry
/-- Literal matrix in the standard real Euclidean coordinates. -/
def operatorEuclideanMatrix {d : ℕ}
    (H : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ := Matrix.toEuclideanLin.symm H.toLinearMap

theorem operatorEuclideanMatrix_apply {d : ℕ}
    (H : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (v : EuclideanSpace ℝ (Fin d)) : (operatorEuclideanMatrix H).toEuclideanLin v = H v := by
  simp [operatorEuclideanMatrix]

theorem operatorEuclideanMatrix_det {d : ℕ}
    (H : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    (operatorEuclideanMatrix H).det = H.det := by
  have h := LinearMap.det_toLpLin 2 (operatorEuclideanMatrix H)
  simpa only [operatorEuclideanMatrix,LinearEquiv.apply_symm_apply] using h.symm

theorem operatorEuclideanMatrix_posSemidef {d : ℕ}
    (H : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hH : H.IsPositive) : (operatorEuclideanMatrix H).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    simpa only [operatorEuclideanMatrix,LinearEquiv.apply_symm_apply] using hH.isSymmetric
  · intro u
    have hn := hH.inner_nonneg_right (WithLp.toLp 2 u)
    rw [← operatorEuclideanMatrix_apply H] at hn
    simpa only [Matrix.toLpLin_apply,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
      star_trivial,WithLp.ofLp_toLp,dotProduct,mul_comm] using hn

theorem operatorEuclideanMatrix_posDef {d : ℕ}
    (H : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hH : H.IsPositive) (hdet : 0 < H.det) : (operatorEuclideanMatrix H).PosDef := by
  have hs := operatorEuclideanMatrix_posSemidef H hH
  apply hs.isHermitian.posDef_iff_eigenvalues_pos.mpr
  intro i
  have hp : (∏ j, hs.isHermitian.eigenvalues j) ≠ 0 := by
    have heq : (operatorEuclideanMatrix H).det = ∏ j, hs.isHermitian.eigenvalues j :=
      by simpa using hs.isHermitian.det_eq_prod_eigenvalues
    rw [← heq,operatorEuclideanMatrix_det H]
    exact hdet.ne'
  exact lt_of_le_of_ne (hs.eigenvalues_nonneg i)
    (Ne.symm ((Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)))

theorem continuous_operatorEuclideanMatrix (d : ℕ) :
    Continuous (operatorEuclideanMatrix (d:=d)) := by
  let e : Matrix (Fin d) (Fin d) ℝ ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :=
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv
  have he : operatorEuclideanMatrix (d:=d) = e.symm := by
    funext H
    apply (Matrix.toEuclideanLin).injective
    simp only [operatorEuclideanMatrix,LinearEquiv.apply_symm_apply]
    have hh := e.apply_symm_apply H
    exact (congrArg ContinuousLinearMap.toLinearMap hh).symm
  rw [he]
  exact e.symm.toContinuousLinearEquiv.continuous

theorem tendsto_operatorEuclideanMatrix {d : ℕ} {ι : Type*} (l : Filter ι)
    (F : ι → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (H : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hlim : Tendsto F l (𝓝 H)) :
    Tendsto (fun j => operatorEuclideanMatrix (F j)) l (𝓝 (operatorEuclideanMatrix H)) := by
  exact ((continuous_operatorEuclideanMatrix d).tendsto H).comp hlim

theorem tendsto_logDet_half_one_add_operatorEuclideanMatrix {d : ℕ} {ι : Type*}
    (l : Filter ι) (F : ι → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (H : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hH : H.IsPositive) (hlim : Tendsto F l (𝓝 H)) :
    Tendsto (fun j => Real.log (((1/2:ℝ) • (1+operatorEuclideanMatrix (F j))).det)) l
      (𝓝 (Real.log (((1/2:ℝ) • (1+operatorEuclideanMatrix H)).det))) := by
  have hA := operatorEuclideanMatrix_posSemidef H hH
  have hdet := positiveMatrix_half_one_add_det_pos (operatorEuclideanMatrix H) hA
  have hm : Continuous (fun J : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) =>
      ((1/2:ℝ) • (1+operatorEuclideanMatrix J))) :=
    (continuous_const.add (continuous_operatorEuclideanMatrix d)).const_smul (1/2:ℝ)
  exact (Real.continuousAt_log hdet.ne').tendsto.comp ((hm.matrix_det.tendsto H).comp hlim)
end CvxBody.Geometry
