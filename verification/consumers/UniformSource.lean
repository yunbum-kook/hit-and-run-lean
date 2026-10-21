import HitAndRun.Sobolev.UniformSource
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Sobolev HitAndRun.Analysis
open scoped ENNReal BigOperators InnerProduct
variable {n : ℕ} [NeZero n]
example (K : BoundedOpenDomain n) (h : K.constant < ⊤) (f : K.Target) :
    ∃ u : Fin n → H01 K.ambient K.carrier,
      K.div (vectorFieldOfGraph K.isBounded u) = f ∧
      (∑ i : Fin n, ‖gradL (u i : H1Graph K.ambient K.carrier)‖ ^ 2) ≤
        K.constant.toReal * ‖f‖ ^ 2 := K.attained_graph_solver h f
example (K : BoundedOpenDomain n) {C : ℝ} (hC : 0 < C) :
    (∀ f : K.Target, ∃ u : K.Field, K.div u = f ∧ ‖u‖ ^ 2 ≤ C * ‖f‖ ^ 2) ↔
    (∀ f : K.Target, ‖f‖ ^ 2 ≤ C * (sSup (divergenceDualQuotients K.div f)) ^ 2) :=
  K.duality hC
example (K : BoundedOpenDomain n) (f : K.Target) :
    ∃! u : K.Field,
      (∀ v : K.Field, inner ℝ f (K.div v) = inner ℝ u v) ∧
      ‖u‖ = sSup (divergenceDualQuotients K.div f) := K.riesz_full f
#print axioms vectorFieldOfGraph_graphOfVectorField
#print axioms graphOfVectorField_vectorFieldOfGraph
#print axioms graphOfVectorField_energy
#print axioms BoundedOpenDomain.measure_eq_uniform
#print axioms BoundedOpenDomain.attained_solver
#print axioms BoundedOpenDomain.attained_graph_solver
#print axioms BoundedOpenDomain.duality
#print axioms BoundedOpenDomain.riesz
#print axioms BoundedOpenDomain.riesz_norm
#print axioms BoundedOpenDomain.riesz_full
