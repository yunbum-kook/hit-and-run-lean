module
public import HitAndRun.Geometry.SmoothDistanceCutoff
public import HitAndRun.Sobolev.CutoffEstimate

/-! The compact-cutoff estimate instantiated with actual distance mollifiers.
The rough-data approximation and weighted limiting integral are separate. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry
open scoped BigOperators
variable {n : ℕ}
variable {Ω : Set (EuclideanSpace ℝ (Fin n))} {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]

def distanceCutoffTest (hb : Bornology.IsBounded Ω) (k : ℕ) : testFunctions Ω :=
  ⟨distanceCutoffSequence (μ := μ) Ω k,
    distanceCutoffSequence_smooth Ω k,
    distanceCutoffSequence_compact hb k,
    distanceCutoffSequence_support hb k⟩

theorem distanceCutoffTest_energy (hb : Bornology.IsBounded Ω) (k : ℕ)
    (h : (EuclideanSpace ℝ (Fin n)) → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (G : Fin n → Fin n → (EuclideanSpace ℝ (Fin n)) → ℝ)
    (hGc : ∀ i j, Continuous (G i j))
    (hG : ∀ x i j, G i j x = -G j i x)
    (hGi : Integrable (fun x => ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0) μ)
    (hrel : ∀ i, ∀ φ : testFunctions Ω,
      (∫ x, h x * fderiv ℝ (φ : (EuclideanSpace ℝ (Fin n)) → ℝ) x (EuclideanSpace.basisFun (Fin n) ℝ i) ∂μ) =
        ∑ j, ∫ x, G i j x * fderiv ℝ (φ : (EuclideanSpace ℝ (Fin n)) → ℝ) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∂μ) :
    (∫ x, distanceCutoffSequence (μ := μ) Ω k x ^ 2 *
      ∑ i, (fderiv ℝ h x (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2 ∂μ) ≤
      4 * ∫ x, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂μ := by
  exact cutoff_energy_le (distanceCutoffTest hb k) h hh
    (EuclideanSpace.basisFun (Fin n) ℝ) G hGc hG hGi
    (distanceCutoffSequence_gradient_energy (EuclideanSpace.basisFun (Fin n) ℝ) Ω k) hrel
end HitAndRun.Sobolev
