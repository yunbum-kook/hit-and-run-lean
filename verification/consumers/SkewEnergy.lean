module
import HitAndRun.Sobolev.CutoffSkew
open HitAndRun.Analysis HitAndRun.Sobolev MeasureTheory EllipticPdes
open scoped BigOperators
example {n : ℕ} (a b : Fin n → ℝ) (G : Fin n → Fin n → ℝ)
    (hG : ∀ i j, G i j = -G j i) (ha : (∑ i, a i ^ 2) ≤ 1) :
    (∑ i, ∑ j, a j * b i * G i j) ^ 2 ≤
      (∑ i, b i ^ 2) * (∑ i, ∑ j, if i < j then G i j ^ 2 else 0) :=
  skew_contraction_sq_le a b G hG ha
#print axioms upper_wedge_energy
#print axioms upper_wedge_energy_le
#print axioms upper_wedge_energy_le_of_energy_le_one
#print axioms symmetric_skew_contraction
#print axioms skew_contraction_upper
#print axioms skew_contraction_sq_le
#print axioms cutoffDerivativeTest
#print axioms fderiv_cutoffDerivativeTest
#print axioms cutoff_weak_identity

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Set E} {ι : Type*} [Fintype ι] {μ : Measure E} [μ.IsAddHaarMeasure]
    (eta : testFunctions Ω) (h : E → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (v : E) (b : ι → E) (G : ι → E → ℝ)
    (hrel : ∀ φ : testFunctions Ω,
      (∫ x, h x * fderiv ℝ (φ : E → ℝ) x v ∂μ) =
        ∑ j, ∫ x, G j x * fderiv ℝ (φ : E → ℝ) x (b j) ∂μ) :
    (∫ x, ((eta : E → ℝ) x) ^ 2 * (fderiv ℝ h x v) ^ 2 ∂μ) =
      -∑ j, ∫ x, G j x *
        (2 * (eta : E → ℝ) x * fderiv ℝ (eta : E → ℝ) x (b j) * fderiv ℝ h x v +
          ((eta : E → ℝ) x) ^ 2 * fderiv ℝ (fun y => fderiv ℝ h y v) x (b j)) ∂μ :=
  cutoff_weak_identity eta h hh v b G hrel
