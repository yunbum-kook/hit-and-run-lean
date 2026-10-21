module
public import HitAndRun.Geometry.SphereMomentsTensor
public import Mathlib.LinearAlgebra.Matrix.Trace
@[expose] public section
namespace HitAndRun.Geometry
open MeasureTheory
variable {n : ℕ} [NeZero n]

/-- A real matrix's quadratic form on a unit direction; symmetry is not assumed. -/
def sphereQuadratic (M : Matrix (Fin n) (Fin n) ℝ) (θ : UnitDirection n) : ℝ :=
  ∑ i, ∑ j, M i j * θ.val i * θ.val j

/-- The three Kronecker pairings contract into trace, Frobenius and transpose-pair terms. -/
theorem fourth_tensor_contraction (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, M i j * M k l *
      ((if i = j ∧ k = l then (1 : ℝ) else 0) +
       (if i = k ∧ j = l then (1 : ℝ) else 0) +
       (if i = l ∧ j = k then (1 : ℝ) else 0))) =
      (Matrix.trace M)^2 + (∑ i, ∑ j, (M i j)^2) + (∑ i, ∑ j, M i j * M j i) := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp only [ite_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
  rw [Matrix.trace]
  simp_rw [sq, ← Finset.mul_sum, ← Finset.sum_mul]
  rfl

/-- Exact second moment of an arbitrary matrix quadratic form on the uniform sphere. -/
theorem uniformSphere_integral_quadratic_sq (M : Matrix (Fin n) (Fin n) ℝ) :
    (∫ θ : UnitDirection n, (sphereQuadratic M θ)^2 ∂uniformSphere n) =
      ((Matrix.trace M)^2 + (∑ i, ∑ j, (M i j)^2) + (∑ i, ∑ j, M i j * M j i)) /
        ((n : ℝ) * (n + 2)) := by
  have hpoly (θ : UnitDirection n) : (sphereQuadratic M θ)^2 =
      ∑ i, ∑ j, ∑ k, ∑ l, (M i j * M k l) * (θ.val i * θ.val j * θ.val k * θ.val l) := by
    simp only [sphereQuadratic, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [hpoly]
  simp (disch := intro a ha; exact uniformSphere_integrable (by fun_prop)) only
    [integral_finsetSum, integral_const_mul, uniformSphere_integral_four]
  simp_rw [← mul_div_assoc, ← Finset.sum_div]
  rw [fourth_tensor_contraction]

/-- Twice the squared Frobenius norm of the symmetric part is the two matrix-pair terms. -/
theorem symmetrized_frobenius_identity (M : Matrix (Fin n) (Fin n) ℝ) :
    2 * (∑ i, ∑ j, ((M i j + M j i) / 2)^2) =
      (∑ i, ∑ j, (M i j)^2) + (∑ i, ∑ j, M i j * M j i) := by
  have hswap : (∑ i, ∑ j, (M j i)^2) = ∑ i, ∑ j, (M i j)^2 := Finset.sum_comm
  have hpoly (a b : ℝ) : 2 * ((a+b)/2)^2 = a^2/2 + a*b + b^2/2 := by ring
  simp_rw [Finset.mul_sum, hpoly, Finset.sum_add_distrib, ← Finset.sum_div]
  rw [hswap]
  ring

/-- Source-faithful fourth moment: trace squared plus twice the symmetric Frobenius square. -/
theorem uniformSphere_integral_quadratic_sq_sym (M : Matrix (Fin n) (Fin n) ℝ) :
    (∫ θ : UnitDirection n, (sphereQuadratic M θ)^2 ∂uniformSphere n) =
      ((Matrix.trace M)^2 + 2 * (∑ i, ∑ j, ((M i j + M j i) / 2)^2)) /
        ((n : ℝ) * (n + 2)) := by
  rw [uniformSphere_integral_quadratic_sq, symmetrized_frobenius_identity]
  congr 1
  ring
end HitAndRun.Geometry
