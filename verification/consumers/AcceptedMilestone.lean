module
public import HitAndRun.Sobolev.ZeroMean
public import HitAndRun.Analysis.DualCertificate
public import HitAndRun.Analysis.AdjointRiesz
public import HitAndRun.Analysis.MinimumNormPreimage
public import HitAndRun.Markov.CoordinateAverage
public import HitAndRun.Analysis.PositiveContraction
public import HitAndRun.Markov.ChiSquareContraction
public import HitAndRun.Geometry.InnerBall
public import HitAndRun.Markov.ConditionalProjection
public import HitAndRun.External.EllipticPDE.GradientSpace
public import HitAndRun.Analysis.Duality
public import HitAndRun.Analysis.MinimumEnergy
public import HitAndRun.Sobolev.SourceDuality
public import HitAndRun.Sobolev.Nontrivial
public import HitAndRun.Sobolev.UniformMeasure
public import HitAndRun.Sobolev.UniformSource
public import HitAndRun.Sobolev.CurlUniform
@[expose] public section
namespace AuditPacket0
open MeasureTheory HitAndRun.Sobolev
open scoped NNReal
example {n : ℕ} [NeZero n] (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (u : VectorField μ Ω) :
    ‖divergence μ Ω u‖ ≤ Real.sqrt n * ‖u‖ := norm_divergence_le u
example {n : ℕ} [NeZero n] (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    (Ω : Set (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure (μ.restrict Ω)]
    (u : VectorField μ Ω) : (∫ x in Ω, divergence μ Ω u x ∂μ) = 0 := by
  rw [← meanCLM_eq_integral]
  exact divergence_mean_zero u
#print axioms HitAndRun.Sobolev.norm_diagonalDerivative_le
#print axioms HitAndRun.Sobolev.norm_divergence_sq_le
#print axioms HitAndRun.Sobolev.norm_divergence_le
#print axioms HitAndRun.Sobolev.meanCLM_eq_integral
#print axioms HitAndRun.Sobolev.integral_test_partial_zero
#print axioms HitAndRun.Sobolev.h01_partial_mean_zero
#print axioms HitAndRun.Sobolev.gradient_partial_mean_zero
#print axioms HitAndRun.Sobolev.divergence_mean_zero
#print axioms HitAndRun.Sobolev.centeredDivergence
end AuditPacket0

namespace AuditPacket1
#print axioms HitAndRun.norm_sq_le_of_dual_certificate
#check HitAndRun.norm_sq_le_of_dual_certificate
end AuditPacket1

namespace AuditPacket2

open HitAndRun.Analysis

variable {V Q : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]

example (D : V →L[ℝ] Q) (f : Q) :
    ∃! u : V, ∀ v : V, inner ℝ f (D v) = inner ℝ u v :=
  existsUnique_riesz_field D f

example [Nontrivial V] (D : V →L[ℝ] Q) (f : Q) :
    ‖D.adjoint f‖ = sSup {r : ℝ | ∃ v : V, v ≠ 0 ∧ r = inner ℝ f (D v) / ‖v‖} :=
  adjoint_norm_eq_sSup D f

example (D : V →L[ℝ] Q) (f : Q) (hf : ∃ v : V, D v = f) :
    ∃ u : V, D u = f ∧ ∀ v : V, D v = f → ‖u‖ ≤ ‖v‖ :=
  exists_minimum_norm_preimage D f hf

example (D : V →L[ℝ] Q) (f : Q) (hf : ∃ v : V, D v = f) :
    ∃ u : V, D u = f ∧ ∀ v : V, D v = f → ‖u‖ ^ 2 ≤ ‖v‖ ^ 2 :=
  exists_minimum_energy_preimage D f hf

#print axioms HitAndRun.Analysis.existsUnique_riesz_field
#print axioms HitAndRun.Analysis.adjoint_norm_isLUB
#print axioms HitAndRun.Analysis.adjoint_norm_eq_sSup
#print axioms HitAndRun.Analysis.exists_minimum_norm_preimage
#print axioms HitAndRun.Analysis.exists_minimum_energy_preimage
end AuditPacket2

namespace AuditPacket3
#print axioms HitAndRun.Markov.coordinateAverage_positive
#print axioms HitAndRun.Markov.coordinateAverage_symmetric
#print axioms HitAndRun.Markov.coordinateAverage_energy
#print axioms HitAndRun.Analysis.norm_le_one_sub_gap
#print axioms HitAndRun.Analysis.iterate_sq_le_exp
#print axioms HitAndRun.Analysis.iterate_sq_le_exp_on_submodule
open MeasureTheory
example {α ι : Type*} [Fintype ι] [Nonempty ι] {m0 : MeasurableSpace α}
    {μ : @Measure α m0} (m : ι → MeasurableSpace α) (hm : ∀ i, m i ≤ m0)
    (f : Lp ℝ 2 μ) :
    inner ℝ f (f - HitAndRun.Markov.coordinateAverage m hm f) =
    (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖f - HitAndRun.Markov.conditionalProjection (hm i) f‖ ^ 2 :=
  HitAndRun.Markov.coordinateAverage_energy m hm f
end AuditPacket3

namespace AuditPacket4
open MeasureTheory ProbabilityTheory DikinD2 DikinD2.NativeL2
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]
variable {κ : Kernel α α} [IsMarkovKernel κ]
variable {π ν : Measure α} [IsProbabilityMeasure π] [IsProbabilityMeasure ν]
example
    (hκ : ReversibleSupport.JointReversible κ π)
    (hp : (operator κ π (ReversibleSupport.stationary hκ)).IsPositive)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hgap : ∀ x ∈ meanZero π, lam * ‖x‖ ^ 2 ≤
      inner ℝ x (x - operator κ π (ReversibleSupport.stationary hκ) x))
    (N : ℕ) :
    ChiSquareDensity.chiSquare (lawOrbit κ ν N) π ≤
      ChiSquareDensity.chiSquare ν π * ENNReal.ofReal (Real.exp (-2 * lam * N)) := HitAndRun.Markov.chiSquare_lawOrbit_le_exp_of_gap hκ hp lam h0 h1 hgap N
#print axioms HitAndRun.Markov.chiSquare_lawOrbit_le_exp_of_gap
#print axioms DikinD2.NativeL2.lawOrbit_density
#print axioms DikinD2.NativeL2.centered_densityOrbit
#print axioms DikinD2.ChiSquareDensity.finite_density_package
#print axioms HitAndRun.Geometry.ball_subset_at_contraction
end AuditPacket4

namespace AuditPacket5
open MeasureTheory
example {α : Type*} {m m0 : MeasurableSpace α} {μ : @Measure α m0}
  (hm : m ≤ m0) (f : Lp ℝ 2 μ) :
  inner ℝ f (f - HitAndRun.Markov.conditionalProjection hm f) =
  ‖f - HitAndRun.Markov.conditionalProjection hm f‖ ^ 2 :=
  HitAndRun.Markov.conditionalProjection_residual_energy hm f
#print axioms HitAndRun.Markov.conditionalProjection_idempotent
#print axioms HitAndRun.Markov.conditionalProjection_symmetric
#print axioms HitAndRun.Markov.conditionalProjection_positive
#print axioms HitAndRun.Markov.conditionalProjection_residual_energy
end AuditPacket5

namespace AuditPacket6
#print axioms EllipticPdes.H1Graph.mem_W12_iff_hasWeakFDerivOn
#print axioms EllipticPdes.H1Graph.H01_le_W12
#print axioms EllipticPdes.H1Graph.exists_seq_testGraphₗ_tendsto
#print axioms EllipticPdes.H1Graph.poincare_H01_of_bounded
#print axioms HitAndRun.Sobolev.h01_complete
#print axioms HitAndRun.Sobolev.h01_weak
#print axioms HitAndRun.Sobolev.graph_norm_sq_le_gradient
#print axioms HitAndRun.Sobolev.gradient_injective
#print axioms HitAndRun.Sobolev.gradientSpace_closed
#print axioms HitAndRun.Sobolev.gradientSpace_complete
#print axioms HitAndRun.Sobolev.gradientEquiv
#print axioms HitAndRun.Sobolev.gradientEquiv_norm
end AuditPacket6

namespace AuditPacket7
open HitAndRun.Analysis
variable {V Q : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
example (D : V →L[ℝ] Q) {C : ℝ} (hC : 0 < C) :
    (∀ f : Q, ∃ v : V, D v = f ∧ ‖v‖ ^ 2 ≤ C * ‖f‖ ^ 2) ↔
      (∀ f : Q, ‖f‖ ^ 2 ≤ C * ‖D.adjoint f‖ ^ 2) :=
  right_inverse_bound_iff_adjoint_lower_bound D hC
example [Nontrivial V] (D : V →L[ℝ] Q) {C : ℝ} (hC : 0 < C) :
    (∀ f : Q, ∃ v : V, D v = f ∧ ‖v‖ ^ 2 ≤ C * ‖f‖ ^ 2) ↔
      (∀ f : Q, ‖f‖ ^ 2 ≤ C * (sSup (divergenceDualQuotients D f)) ^ 2) :=
  right_inverse_bound_iff_dual_sup D hC
example (D : V →L[ℝ] Q) (f : Q) :
    minimumEnergy D f < ⊤ ↔ ∃ v : V, D v = f := minimumEnergy_lt_top_iff D f
example (D : V →L[ℝ] Q) {C : ℝ} (hC : 0 ≤ C) :
    rightInverseEnergyConstant D ≤ ENNReal.ofReal C ↔
      (∀ f : Q, ∃ v : V, D v = f ∧ ‖v‖ ^ 2 ≤ C * ‖f‖ ^ 2) :=
  energyConstant_le_iff_right_inverse_bound D hC
example (D : V →L[ℝ] Q) (h : rightInverseEnergyConstant D < ⊤) :
    ∀ f : Q, ∃ v : V, D v = f ∧
      ‖v‖ ^ 2 ≤ (rightInverseEnergyConstant D).toReal * ‖f‖ ^ 2 :=
  right_inverse_bound_at_energyConstant D h
#print axioms adjoint_lower_bound_of_right_inverse_bound
#print axioms right_inverse_bound_of_adjoint_lower_bound
#print axioms right_inverse_bound_iff_adjoint_lower_bound
#print axioms right_inverse_bound_iff_dual_sup
#print axioms minimumEnergy_lt_top_iff
#print axioms minimumEnergy_attained
#print axioms surjective_of_energyConstant_lt_top
#print axioms right_inverse_bound_of_energyConstant_le
#print axioms energyConstant_le_of_right_inverse_bound
#print axioms energyConstant_le_iff_right_inverse_bound
#print axioms right_inverse_bound_at_energyConstant
end AuditPacket7

namespace AuditPacket8
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
end AuditPacket8

namespace AuditPacket9
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
end AuditPacket9

namespace AuditPacket10
open MeasureTheory HitAndRun.Sobolev EllipticPdes EllipticPdes.H1Graph
open scoped BigOperators RealInnerProductSpace
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
    (u : Fin n → H01 K.ambient K.carrier) :
    (∑ i, ‖gradL (u i : H1Graph K.ambient K.carrier)‖ ^ 2) =
      ‖K.div (vectorFieldOfGraph K.isBounded u)‖ ^ 2 +
      ∑ i, ∑ j, if i < j then
        ‖weakPartial (vectorFieldOfGraph K.isBounded u) i j -
          weakPartial (vectorFieldOfGraph K.isBounded u) j i‖ ^ 2 else 0 :=
  K.graph_curl_energy u
#print axioms BoundedOpenDomain.curl_energy
#print axioms BoundedOpenDomain.graph_curl_energy
end AuditPacket10
