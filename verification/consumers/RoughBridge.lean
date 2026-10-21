module
import HitAndRun.Sobolev.DistanceCutoffLimit
import HitAndRun.Analysis.BoundedPreimageLimit
import HitAndRun.External.EllipticPDE.Embedding.Convolution
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry HitAndRun.Analysis HitAndRun.Sobolev
open scoped BigOperators
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]
example (hb : Bornology.IsBounded Ω)
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
      4 * ∫ x, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂μ := smooth_distance_energy_le hb h hh G hGc hG hGi hrel
example {V Q : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
    (T : V →L[ℝ] Q) (u : ℕ → V) (y : Q) {R : ℝ} (hR : 0 ≤ R)
    (hu : ∀ k, ‖u k‖ ≤ R)
    (hy : Filter.Tendsto (fun k => T (u k)) Filter.atTop (nhds y)) :
    ∃ x : V, T x = y ∧ ‖x‖ ≤ R := exists_bounded_preimage_of_tendsto T u y hR hu hy
#print axioms smooth_distance_energy_le
#print axioms exists_bounded_preimage_of_adjoint_pairing
#print axioms exists_bounded_preimage_of_tendsto
#print axioms EllipticPdes.Embedding.eLpNorm_convolution_le_of_integral_eq_one
#print axioms EllipticPdes.Embedding.tendsto_eLpNorm_normed_convolution_sub
