module
public import HitAndRun.Sobolev.DistanceCutoffEstimate
public import HitAndRun.Analysis.FatouBound

/-! The distance-weighted estimate for globally smooth data. This closes the
cutoff limit, but does not replace the source's rough L2 distributional data. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry HitAndRun.Analysis
open scoped BigOperators
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]

theorem smooth_distance_energy_le (hb : Bornology.IsBounded Ω)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (G : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hGc : ∀ i j, Continuous (G i j))
    (hG : ∀ x i j, G i j x = -G j i x)
    (hGi : Integrable (fun x => ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0) μ)
    (hrel : ∀ i, ∀ φ : testFunctions Ω,
      (∫ x, h x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) ∂μ) =
        ∑ j, ∫ x, G i j x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∂μ) :
    (∫ x, interiorDistance Ω x ^ 2 *
      ∑ i, (fderiv ℝ h x (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2 ∂μ) ≤
      4 * ∫ x, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂μ := by
  let D (x : EuclideanSpace ℝ (Fin n)) :=
    ∑ i, (fderiv ℝ h x (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2
  have hD : Continuous D := continuous_finsetSum Finset.univ
    (fun i _ => (contDiff_directional hh (EuclideanSpace.basisFun (Fin n) ℝ i)).continuous.pow 2)
  have hDn (x) : 0 ≤ D x := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  apply integral_bound_of_nonnegative_approximation
    (F := fun k x => distanceCutoffSequence (μ := μ) Ω k x ^ 2 * D x)
  · positivity
  · intro k
    convert integrable_cutoff_mul (μ := μ) (distanceCutoffTest (μ := μ) hb k)
      ((distanceCutoffSequence_smooth (μ := μ) Ω k).continuous.mul hD) using 1
    ext x
    dsimp [distanceCutoffTest]
    ring
  · intro k x
    exact mul_nonneg (sq_nonneg _) (hDn x)
  · intro x
    exact mul_nonneg (sq_nonneg _) (hDn x)
  · exact (((interiorDistance_lipschitz Ω).continuous.pow 2).mul hD).aestronglyMeasurable
  · intro x
    exact ((distanceCutoffSequence_tendsto Ω x).pow 2).mul_const (D x)
  · intro k
    exact distanceCutoffTest_energy hb k h hh G hGc hG hGi hrel
end HitAndRun.Sobolev
