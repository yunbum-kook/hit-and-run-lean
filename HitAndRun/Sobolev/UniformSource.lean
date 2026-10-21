module
public import HitAndRun.Sobolev.VectorGraph
public import HitAndRun.Sobolev.Nontrivial
public import HitAndRun.Sobolev.UniformMeasure
@[expose] public section

/-! Source-facing uniform-domain statements. Convexity is not needed for these
three Hilbert lemmas; boundedness, openness and nonemptiness suffice. -/
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Analysis
open scoped ENNReal BigOperators InnerProduct

structure BoundedOpenDomain (n : ℕ) where
  carrier : Set (EuclideanSpace ℝ (Fin n))
  isOpen : IsOpen carrier
  nonempty : carrier.Nonempty
  isBounded : Bornology.IsBounded carrier

namespace BoundedOpenDomain
variable {n : ℕ} [NeZero n]
def ambient (K : BoundedOpenDomain n) := normalizedAmbient K.carrier
instance (K : BoundedOpenDomain n) : K.ambient.IsAddHaarMeasure :=
  normalizedAmbient_isAddHaarMeasure K.isOpen K.nonempty K.isBounded
instance (K : BoundedOpenDomain n) : IsFiniteMeasure (K.ambient.restrict K.carrier) :=
  normalizedAmbient_restrict_finite K.isOpen K.nonempty K.isBounded
instance (K : BoundedOpenDomain n) : CompleteSpace (gradientSpace K.ambient K.carrier) :=
  gradientSpace_complete K.isBounded
instance (K : BoundedOpenDomain n) : Nontrivial (VectorField K.ambient K.carrier) :=
  vectorField_nontrivial K.isOpen K.nonempty K.isBounded
abbrev Field (K : BoundedOpenDomain n) := VectorField K.ambient K.carrier
abbrev Target (K : BoundedOpenDomain n) := centeredL2 (μ := K.ambient) (Ω := K.carrier)
abbrev div (K : BoundedOpenDomain n) : K.Field →L[ℝ] K.Target := centeredDivergence
abbrev constant (K : BoundedOpenDomain n) := babuskaAzizConstant (μ := K.ambient) (Ω := K.carrier)

/-- The actual measure of every source-facing norm is uniform probability. -/
theorem measure_eq_uniform (K : BoundedOpenDomain n) :
    K.ambient.restrict K.carrier = uniformMeasure K.carrier :=
  normalizedAmbient_restrict K.carrier

/-- Lemma 1.3, with finite optimal constant and actual zero-trace weak divergence. -/
theorem attained_solver (K : BoundedOpenDomain n) (h : K.constant < ⊤) :
    ∀ f : K.Target, ∃ u : K.Field, K.div u = f ∧
      ‖u‖ ^ 2 ≤ K.constant.toReal * ‖f‖ ^ 2 :=
  divergence_solver_at_babuskaAziz K.isBounded h

/-- The solver is an actual H01 vector graph, not only an abstract Hilbert vector. -/
theorem attained_graph_solver (K : BoundedOpenDomain n) (h : K.constant < ⊤)
    (f : K.Target) : ∃ u : Fin n → H01 K.ambient K.carrier,
      K.div (vectorFieldOfGraph K.isBounded u) = f ∧
      (∑ i : Fin n, ‖gradL (u i : H1Graph K.ambient K.carrier)‖ ^ 2) ≤
        K.constant.toReal * ‖f‖ ^ 2 := by
  obtain ⟨v, hv, he⟩ := K.attained_solver h f
  refine ⟨graphOfVectorField K.isBounded v, ?_, ?_⟩
  · simpa only [vectorFieldOfGraph_graphOfVectorField] using hv
  · simpa only [graphOfVectorField_energy] using he

/-- Lemma B.1's exact signed nonzero-test supremum, without an extra nontriviality premise. -/
theorem duality (K : BoundedOpenDomain n) {C : ℝ} (hC : 0 < C) :
    (∀ f : K.Target, ∃ u : K.Field, K.div u = f ∧ ‖u‖ ^ 2 ≤ C * ‖f‖ ^ 2) ↔
    (∀ f : K.Target, ‖f‖ ^ 2 ≤ C * (sSup (divergenceDualQuotients K.div f)) ^ 2) :=
  divergence_duality_sup K.isBounded hC

/-- Lemma B.2: the actual field's unique Riesz representative. -/
theorem riesz (K : BoundedOpenDomain n) (f : K.Target) :
    ∃! u : K.Field, ∀ v : K.Field, inner ℝ f (K.div v) = inner ℝ u v :=
  existsUnique_divergence_riesz K.isBounded f

/-- Lemma B.2's exact norm equality, including the zero representative. -/
theorem riesz_norm (K : BoundedOpenDomain n) (f : K.Target) :
    ‖ContinuousLinearMap.adjoint K.div f‖ = sSup (divergenceDualQuotients K.div f) :=
  divergence_riesz_norm f
/-- Both conclusions of Lemma B.2 for the same unique representative. -/
theorem riesz_full (K : BoundedOpenDomain n) (f : K.Target) :
    ∃! u : K.Field,
      (∀ v : K.Field, inner ℝ f (K.div v) = inner ℝ u v) ∧
      ‖u‖ = sSup (divergenceDualQuotients K.div f) := by
  refine ⟨ContinuousLinearMap.adjoint K.div f, ⟨?_, K.riesz_norm f⟩, ?_⟩
  · intro v
    exact (K.div.adjoint_inner_left v f).symm
  · intro u hu
    apply ext_inner_right ℝ
    intro v
    exact (hu.1 v).symm.trans (K.div.adjoint_inner_left v f).symm
end BoundedOpenDomain
end HitAndRun.Sobolev
