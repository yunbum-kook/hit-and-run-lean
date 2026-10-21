import HitAndRun.Sobolev.SourceDuality
import HitAndRun.Sobolev.Nontrivial
import HitAndRun.Sobolev.UniformMeasure
open MeasureTheory HitAndRun.Sobolev HitAndRun.Analysis
open scoped ENNReal InnerProduct
variable {n : ℕ} [NeZero n]
variable {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]
variable {Ω : Set (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure (μ.restrict Ω)]
example (hb : Bornology.IsBounded Ω) (h : babuskaAzizConstant (μ := μ) (Ω := Ω) < ⊤) :
    ∀ f : centeredL2 (μ := μ) (Ω := Ω), ∃ u : VectorField μ Ω,
      centeredDivergence u = f ∧
      ‖u‖ ^ 2 ≤ (babuskaAzizConstant (μ := μ) (Ω := Ω)).toReal * ‖f‖ ^ 2 :=
  divergence_solver_at_babuskaAziz hb h
example (hb : Bornology.IsBounded Ω) (f : centeredL2 (μ := μ) (Ω := Ω)) :
    ∃! u : VectorField μ Ω, ∀ v : VectorField μ Ω,
      inner ℝ f (centeredDivergence v) = inner ℝ u v :=
  existsUnique_divergence_riesz hb f
example (hb : Bornology.IsBounded Ω) (ho : IsOpen Ω) (hne : Ω.Nonempty) {C : ℝ}
    (hC : 0 < C) :
    (∀ f : centeredL2 (μ := μ) (Ω := Ω), ∃ u : VectorField μ Ω,
      centeredDivergence u = f ∧ ‖u‖ ^ 2 ≤ C * ‖f‖ ^ 2) ↔
    (∀ f : centeredL2 (μ := μ) (Ω := Ω), ‖f‖ ^ 2 ≤
      C * (sSup (divergenceDualQuotients centeredDivergence f)) ^ 2) := by
  letI := vectorField_nontrivial (μ := μ) ho hne hb
  exact divergence_duality_sup hb hC
example (ho : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω) :
    IsProbabilityMeasure (uniformMeasure Ω) := uniformMeasure_isProbabilityMeasure ho hne hb
#print axioms babuskaAzizConstant_eq_source
#print axioms vectorField_norm_sq
#print axioms vectorField_graph_energy
#print axioms divergence_solver_at_babuskaAziz
#print axioms existsUnique_divergence_riesz
#print axioms divergence_duality
#print axioms divergence_duality_sup
#print axioms divergence_riesz_norm
#print axioms h01_nontrivial
#print axioms gradientSpace_nontrivial
#print axioms vectorField_nontrivial
#print axioms normalizedAmbient_restrict
#print axioms domain_volume_bounds
#print axioms normalizedAmbient_isAddHaarMeasure
#print axioms uniformMeasure_isProbabilityMeasure
#print axioms normalizedAmbient_restrict_finite
