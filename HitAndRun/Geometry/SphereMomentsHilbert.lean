module
public import HitAndRun.Geometry.SphereMomentsTensor
@[expose] public section
namespace HitAndRun.Geometry
open MeasureTheory
open scoped InnerProductSpace
variable {n : ℕ} [NeZero n]

/-- Tensor contraction with arbitrary scalar four-index coefficients. -/
theorem fourth_tensor_contraction_general (A : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, A i j k l *
      ((if i = j ∧ k = l then (1 : ℝ) else 0) +
       (if i = k ∧ j = l then (1 : ℝ) else 0) +
       (if i = l ∧ j = k then (1 : ℝ) else 0))) =
      (∑ i, ∑ k, A i i k k) + (∑ i, ∑ j, A i j i j) + (∑ i, ∑ j, A i j j i) := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp only [ite_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]

/-- Sphere quadratic tensor with coefficients in any real inner product space. -/
def sphereHilbertQuadratic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Fin n → Fin n → H) (θ : UnitDirection n) : H :=
  ∑ i, ∑ j, (θ.val i * θ.val j) • C i j

/-- Hilbert-valued fourth-moment identity, usable directly for L² weak-derivative coefficients. -/
theorem uniformSphere_integral_hilbert_quadratic_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Fin n → Fin n → H) :
    (∫ θ : UnitDirection n, ‖sphereHilbertQuadratic C θ‖^2 ∂uniformSphere n) =
      (‖∑ i, C i i‖^2 + (∑ i, ∑ j, ‖C i j‖^2) +
        (∑ i, ∑ j, ⟪C i j, C j i⟫_ℝ)) / ((n : ℝ) * (n + 2)) := by
  have hpoly (θ : UnitDirection n) : ‖sphereHilbertQuadratic C θ‖^2 =
      ∑ i, ∑ j, ∑ k, ∑ l, ⟪C i j, C k l⟫_ℝ *
        (θ.val i * θ.val j * θ.val k * θ.val l) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sphereHilbertQuadratic, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [real_inner_comm (C k l) (C i j)]
    ring
  simp_rw [hpoly]
  simp (disch := intro a ha; exact uniformSphere_integrable (by fun_prop)) only
    [integral_finsetSum, integral_const_mul, uniformSphere_integral_four]
  simp_rw [← mul_div_assoc, ← Finset.sum_div]
  rw [fourth_tensor_contraction_general]
  simp only [real_inner_self_eq_norm_sq]
  congr 2
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum]
  congr 1
  exact Finset.sum_comm

/-- The expected Hilbert quadratic tensor is the diagonal sum divided by dimension. -/
theorem uniformSphere_integral_hilbert_quadratic
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Fin n → Fin n → H) :
    (∫ θ : UnitDirection n, sphereHilbertQuadratic C θ ∂uniformSphere n) =
      (1 / (n : ℝ)) • ∑ i, C i i := by
  have hInt (f : UnitDirection n → H) (hf : Continuous f) : Integrable f (uniformSphere n) := by
    letI := uniformSphere_probability n
    letI : CompactSpace (UnitDirection n) :=
      isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    exact integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)
  unfold sphereHilbertQuadratic
  simp (disch := intro a ha; exact hInt _ (by fun_prop)) only [integral_finsetSum]
  simp only [integral_smul_const, uniformSphere_integral_mul, ite_smul, zero_smul]
  simp [← Finset.smul_sum]

end HitAndRun.Geometry
