module
import HitAndRun.Sobolev.CutoffEnergy
import HitAndRun.External.EllipticPDE.Analysis.Mollifier
open HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Set E} {μ : Measure E} [μ.IsAddHaarMeasure]

example {n : ℕ}
    (eta : testFunctions Ω) (h : E → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (b : Fin n → E) (G : Fin n → Fin n → E → ℝ)
    (hGc : ∀ i j, Continuous (G i j))
    (hG : ∀ x i j, G i j x = -G j i x)
    (hrel : ∀ i, ∀ φ : testFunctions Ω,
      (∫ x, h x * fderiv ℝ (φ : E → ℝ) x (b i) ∂μ) =
        ∑ j, ∫ x, G i j x * fderiv ℝ (φ : E → ℝ) x (b j) ∂μ) :
    (∫ x, (eta : E → ℝ) x ^ 2 * ∑ i, (fderiv ℝ h x (b i)) ^ 2 ∂μ) =
      -2 * ∫ x, (eta : E → ℝ) x *
        ∑ i, ∑ j, fderiv ℝ (eta : E → ℝ) x (b j) * fderiv ℝ h x (b i) * G i j x ∂μ := cutoff_energy_identity eta h hh b G hGc hG hrel
#print axioms cutoff_energy_identity
#print axioms smooth_mixed_comm
#print axioms integrable_cutoff_mul
#print axioms EllipticPdes.contDiff_normed_convolution
#print axioms EllipticPdes.tsupport_normed_convolution_subset
#print axioms EllipticPdes.norm_normed_convolution_le
