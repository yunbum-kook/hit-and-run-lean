module
public import HitAndRun.Geometry.SphereMomentsMatrix
public import HitAndRun.Geometry.SphereMomentsHilbert
@[expose] public section
open MeasureTheory HitAndRun.Geometry
open scoped InnerProductSpace
example (n : ℕ) [NeZero n] (M : Matrix (Fin n) (Fin n) ℝ) :
    (∫ θ : UnitDirection n, (sphereQuadratic M θ)^2 ∂uniformSphere n) =
      ((Matrix.trace M)^2 + 2 * (∑ i, ∑ j, ((M i j + M j i) / 2)^2)) /
        ((n : ℝ) * (n + 2)) := uniformSphere_integral_quadratic_sq_sym M
example (n : ℕ) [NeZero n] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Fin n → Fin n → H) :
    (∫ θ : UnitDirection n, ‖sphereHilbertQuadratic C θ‖^2 ∂uniformSphere n) =
      (‖∑ i, C i i‖^2 + (∑ i, ∑ j, ‖C i j‖^2) + (∑ i, ∑ j, ⟪C i j, C j i⟫_ℝ)) /
        ((n : ℝ) * (n + 2)) := uniformSphere_integral_hilbert_quadratic_sq C
example (n : ℕ) [NeZero n] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (C : Fin n → Fin n → H) :
    (∫ θ : UnitDirection n, sphereHilbertQuadratic C θ ∂uniformSphere n) =
      (1 / (n : ℝ)) • ∑ i, C i i := uniformSphere_integral_hilbert_quadratic C
#print axioms uniformSphere_integral_four
#print axioms uniformSphere_integral_quadratic_sq_sym
#print axioms uniformSphere_integral_hilbert_quadratic_sq
#print axioms uniformSphere_integral_hilbert_quadratic
