module
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Normed.Lp.Matrix

@[expose] public section


/-! Positive semidefinite source matrices give the nonsingular precision and
inverse quadratic estimate used in the Gaussian completion of the square. -/
noncomputable section
open Matrix
open scoped RealInnerProductSpace
namespace CvxBody.Geometry
variable {d : ℕ}

/-- The identity supplies strict positivity even when the source Hessian is singular. -/
theorem positiveMatrix_one_add_posDef (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) :
    (1+A).PosDef := Matrix.PosDef.one.add_posSemidef hA

/-- The precision in the actual Gaussian integral has exactly the source factor one half. -/
theorem positiveMatrix_half_one_add_posDef (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) :
    ((1/2:ℝ) • (1+A)).PosDef :=
  (positiveMatrix_one_add_posDef A hA).smul (by norm_num)

/-- The determinant in the literal source logarithm is strictly positive. -/
theorem positiveMatrix_half_one_add_det_pos (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) :
    0 < ((1/2:ℝ) • (1+A)).det := (positiveMatrix_half_one_add_posDef A hA).det_pos

private lemma positiveMatrix_inverse_dotProduct_le_aux
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) (x : Fin d → ℝ) :
    x ⬝ᵥ ((1+A)⁻¹ *ᵥ x) ≤ x ⬝ᵥ x := by
  let M := 1+A
  let y := M⁻¹ *ᵥ x
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr (positiveMatrix_one_add_posDef A hA).det_pos.ne'
  have hMy : M *ᵥ y = x := by
    dsimp only [y]
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hdet,Matrix.one_mulVec]
  have hx : x = y+A *ᵥ y := by
    rw [← hMy]
    exact Matrix.add_mulVec 1 A y |>.trans (by rw [Matrix.one_mulVec])
  have hAy : 0 ≤ y ⬝ᵥ (A *ᵥ y) := by
    simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg y
  have hsq : 0 ≤ (A *ᵥ y) ⬝ᵥ (A *ᵥ y) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg ((A *ᵥ y) i))
  have hid : x ⬝ᵥ x-x ⬝ᵥ y = y ⬝ᵥ (A *ᵥ y)+(A *ᵥ y) ⬝ᵥ (A *ᵥ y) := by
    rw [hx]
    simp only [add_dotProduct,dotProduct_add]
    ring
  change x ⬝ᵥ y ≤ x ⬝ᵥ x
  linarith

/-- The exact inverse quadratic term is bounded by the squared Euclidean norm,
without an assumed inverse or spectral estimate. -/
theorem positiveMatrix_inverse_quadratic_le (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    inner ℝ ξ ((1+A)⁻¹.toEuclideanLin ξ) ≤ ‖ξ‖^2 := by
  change ((1+A)⁻¹ *ᵥ ξ.ofLp) ⬝ᵥ ξ.ofLp ≤ ‖ξ‖^2
  rw [dotProduct_comm]
  calc
    _ ≤ ξ.ofLp ⬝ᵥ ξ.ofLp := positiveMatrix_inverse_dotProduct_le_aux A hA ξ.ofLp
    _ = ‖ξ‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [dotProduct,pow_two]
end CvxBody.Geometry
