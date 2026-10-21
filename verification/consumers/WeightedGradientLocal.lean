module
import HitAndRun.Sobolev.WeightedGradientLocal
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry HitAndRun.Sobolev Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}
example (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty) {q : E → E}
    (hq : MemLp q 2 (μ.restrict Ω)) {K : Set E} (hK : K ⊆ Ω) (hcompact : IsCompact K) :
    IntegrableOn (fun x => (interiorDistance Ω x)⁻¹ • q x) K μ :=
  (locallyIntegrableOn_unweightedGradient ho hc hq).integrableOn_compact_subset hK hcompact
example (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    {h : E → ℝ} {q : E → E} (hh : MemLp h 2 (μ.restrict Ω))
    (hq : MemLp q 2 (μ.restrict Ω))
    (hp : ∀ φ : testFunctions Ω, ∀ v : E,
      (∫ x in Ω, h x * fderiv ℝ (φ : E → ℝ) x v ∂μ) =
        -∫ x in Ω, boundaryTest φ x * inner ℝ (q x) v ∂μ) :
    HasWeakFDerivOn ⟨Ω, ho⟩ h
      (fun x => innerSL ℝ ((interiorDistance Ω x)⁻¹ • q x)) μ :=
  hasWeakFDerivOn_of_weighted_test_pairing ho hc hh hq hp
#print axioms continuousOn_inv_interiorDistance
#print axioms locallyIntegrableOn_unweightedGradient
#print axioms hasWeakFDerivOn_of_weighted_test_pairing
