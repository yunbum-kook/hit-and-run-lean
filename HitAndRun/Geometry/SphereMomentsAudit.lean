module
public import HitAndRun.Geometry.SphereMomentsFourth
@[expose] public section
open MeasureTheory HitAndRun.Geometry
example (n : ℕ) [NeZero n]
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (sphereAction U) (uniformSphere n) (uniformSphere n) :=
  sphereAction_uniform_measurePreserving U
example (n : ℕ) [NeZero n] (i j : Fin n) :
    (∫ θ : UnitDirection n, θ.val i * θ.val j ∂uniformSphere n) =
      if i = j then 1 / (n : ℝ) else 0 := uniformSphere_integral_mul i j
example (n : ℕ) [NeZero n] (i : Fin n) :
    (∫ θ : UnitDirection n, (θ.val i)^4 ∂uniformSphere n) =
      3 / ((n : ℝ) * (n + 2)) := uniformSphere_integral_fourth i
example (n : ℕ) [NeZero n] (i j : Fin n) (hij : i ≠ j) :
    (∫ θ : UnitDirection n, (θ.val i)^2 * (θ.val j)^2 ∂uniformSphere n) =
      1 / ((n : ℝ) * (n + 2)) := uniformSphere_integral_sq_mul_sq i j hij
#print axioms sphereAction_uniform_measurePreserving
#print axioms uniformSphere_integral_mul
#print axioms sphereFourth_isometry
#print axioms sphereFourth_eq_of_norm_eq
#print axioms uniformSphere_fourth_eq_three_mixed
#print axioms uniformSphere_integral_fourth
#print axioms uniformSphere_integral_sq_mul_sq
