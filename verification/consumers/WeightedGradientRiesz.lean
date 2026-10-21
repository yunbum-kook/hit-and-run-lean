module
import HitAndRun.Sobolev.WeightedGradientRiesz
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry HitAndRun.Sobolev
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E} {ι : Type*} [Fintype ι]
example (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (h : Lp ℝ 2 (μ.restrict Ω)) (q : Lp E 2 (μ.restrict Ω)) (b : Module.Basis ι ℝ E)
    (hp : ∀ Φ, inner ℝ q (vectorTestCoefficient (μ := μ) ho hc b Φ) =
      vectorTestFunctional h b Φ) (φ : testFunctions Ω) (v : E) :
    (∫ x in Ω, h x * fderiv ℝ (φ : E → ℝ) x v ∂μ) =
      -∫ x in Ω, boundaryTest φ x * inner ℝ (q x) v ∂μ :=
  weighted_integral_pairing_of_riesz ho hc h q b hp φ v
example (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (h : Lp ℝ 2 (μ.restrict Ω)) (b : Module.Basis ι ℝ E) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ Φ, |vectorTestFunctional h b Φ| ≤
      R * ‖vectorTestCoefficient (μ := μ) ho hc b Φ‖) :
    ∃ q : Lp E 2 (μ.restrict Ω),
      HasWeakFDerivOn ⟨Ω, ho⟩ h
        (fun x => innerSL ℝ ((interiorDistance Ω x)⁻¹ • q x)) μ ∧ ‖q‖ ≤ R :=
  exists_weak_gradient_of_test_bound ho hc h b hR hb
#print axioms riesz_weighted_pairing_all_directions
#print axioms weighted_integral_pairing_of_riesz
#print axioms hasWeakFDerivOn_of_riesz
#print axioms exists_weak_gradient_of_test_bound
