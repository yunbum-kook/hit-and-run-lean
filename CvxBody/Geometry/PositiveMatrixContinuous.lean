module
public import CvxBody.Geometry.PositiveMatrix

@[expose] public section


/-! Continuous positive precision, inverse, and logarithmic normalization for
continuous source positive semidefinite matrix fields. -/
noncomputable section
open Matrix
open scoped RealInnerProductSpace
namespace CvxBody.Geometry
variable {d : ℕ}

theorem continuous_positiveMatrix_shiftedInverse {X : Type*} [TopologicalSpace X]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (hA : Continuous A)
    (hPSD : ∀ x, (A x).PosSemidef) : Continuous (fun x => (1+A x)⁻¹) := by
  have hM : Continuous (fun x => 1+A x) := continuous_const.add hA
  apply continuous_iff_continuousAt.mpr
  intro x
  have hd : (1+A x).det ≠ 0 := (positiveMatrix_one_add_posDef (A x) (hPSD x)).det_pos.ne'
  exact (continuousAt_matrix_inv (1+A x)
    (by simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hd)).comp (f := fun y : X => 1+A y) hM.continuousAt

theorem continuous_positiveMatrix_logDet {X : Type*} [TopologicalSpace X]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (hA : Continuous A)
    (hPSD : ∀ x, (A x).PosSemidef) :
    Continuous (fun x => Real.log (((1/2:ℝ) • (1+A x)).det)) := by
  have hdet : Continuous (fun x => ((1/2:ℝ) • (1+A x)).det) :=
    ((continuous_const.add hA).const_smul (1/2:ℝ)).matrix_det
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (Real.continuousAt_log (positiveMatrix_half_one_add_det_pos (A x) (hPSD x)).ne').comp
    (f := fun y : X => ((1/2:ℝ) • (1+A y)).det) hdet.continuousAt

theorem continuous_positiveMatrix_inverseQuadratic {X : Type*} [TopologicalSpace X]
    (A : X → Matrix (Fin d) (Fin d) ℝ) (hA : Continuous A)
    (hPSD : ∀ x, (A x).PosSemidef)
    (ξ : X → EuclideanSpace ℝ (Fin d)) (hξ : Continuous ξ) :
    Continuous (fun x => inner ℝ (ξ x) ((1+A x)⁻¹.toEuclideanLin (ξ x))) := by
  have hI := continuous_positiveMatrix_shiftedInverse A hA hPSD
  have haction : Continuous (fun x => (1+A x)⁻¹.toEuclideanLin (ξ x)) := by
    change Continuous (fun x => WithLp.toLp 2 ((1+A x)⁻¹ *ᵥ (ξ x).ofLp))
    exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
      (hI.matrix_mulVec ((PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).comp hξ))
  exact hξ.inner haction
end CvxBody.Geometry
