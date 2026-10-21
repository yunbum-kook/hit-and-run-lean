module
public import HitAndRun.Sobolev.DistanceCutoffLimit
public import HitAndRun.Sobolev.SmoothGraph

/-! Actual distance-weighted smooth gradients as L2 classes, with the exact
upper-triangle skew energy bound. This remains a smooth-data lemma. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry Set
open scoped BigOperators
section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

theorem interiorDistance_compact (hb : Bornology.IsBounded Ω) :
    HasCompactSupport (interiorDistance Ω) := by
  apply hb.isCompact_closure.of_isClosed_subset (isClosed_tsupport _)
  apply closure_mono
  intro x hx
  by_contra hn
  exact hx (interiorDistance_zero_outside hn)

theorem weightedGradient_memLp (hb : Bornology.IsBounded Ω)
    (h : E → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    MemLp (fun x => interiorDistance Ω x • gradient h x) 2 μ :=
  ((interiorDistance_lipschitz Ω).continuous.smul
    ((InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hh.continuous_fderiv (by simp)))).memLp_of_hasCompactSupport
    (interiorDistance_compact hb).smul_right

def smoothWeightedGradient (hb : Bornology.IsBounded Ω)
    (h : E → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) : Lp E 2 μ :=
  (weightedGradient_memLp hb h hh).toLp _

theorem norm_sq_smoothWeightedGradient (hb : Bornology.IsBounded Ω)
    (h : E → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ‖smoothWeightedGradient (μ := μ) hb h hh‖ ^ 2 =
      ∫ x, interiorDistance Ω x ^ 2 * ‖gradient h x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, smoothWeightedGradient, inner_toLp_toLp]
  simp only [real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
end General

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
  {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]

theorem smoothWeightedGradient_energy_le (hb : Bornology.IsBounded Ω)
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
    ‖smoothWeightedGradient (μ := μ) hb h hh‖ ^ 2 ≤
      4 * ∫ x, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂μ := by
  rw [norm_sq_smoothWeightedGradient]
  have he (x) : ‖gradient h x‖ ^ 2 =
      ∑ i, (fderiv ℝ h x (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2 := by
    rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_sq_inner_right]
    simp only [EllipticPdes.inner_gradient_right]
  simp_rw [he]
  exact smooth_distance_energy_le hb h hh G hGc hG hGi hrel
end HitAndRun.Sobolev
