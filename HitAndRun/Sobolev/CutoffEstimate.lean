module
public import HitAndRun.Sobolev.CutoffEnergy

/-! Sharp smooth compact-cutoff estimate. Finite Cauchy–Schwarz and Young's
inequality are integrated directly, avoiding unnecessary square-root carriers.
The actual distance cutoff and rough-data limits are still separate. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Set E} {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The exact constant4 squared-energy estimate for a genuine compact cutoff. -/
theorem cutoff_energy_le {n : ℕ}
    (eta : testFunctions Ω) (h : E → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (b : Fin n → E) (G : Fin n → Fin n → E → ℝ)
    (hGc : ∀ i j, Continuous (G i j))
    (hG : ∀ x i j, G i j x = -G j i x)
    (hGi : Integrable (fun x => ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0) μ)
    (heta : ∀ x, (∑ i, (fderiv ℝ (eta : E → ℝ) x (b i)) ^ 2) ≤ 1)
    (hrel : ∀ i, ∀ φ : testFunctions Ω,
      (∫ x, h x * fderiv ℝ (φ : E → ℝ) x (b i) ∂μ) =
        ∑ j, ∫ x, G i j x * fderiv ℝ (φ : E → ℝ) x (b j) ∂μ) :
    (∫ x, (eta : E → ℝ) x ^ 2 * ∑ i, (fderiv ℝ h x (b i)) ^ 2 ∂μ) ≤
      4 * ∫ x, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂μ := by
  let A (x : E) := (eta : E → ℝ) x ^ 2 * ∑ i, (fderiv ℝ h x (b i)) ^ 2
  let C (x : E) := (eta : E → ℝ) x *
    ∑ i, ∑ j, fderiv ℝ (eta : E → ℝ) x (b j) * fderiv ℝ h x (b i) * G i j x
  let D (x : E) := ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0
  have iA : Integrable A μ := by
    convert integrable_cutoff_mul (μ := μ) eta
      (eta.2.1.continuous.mul (continuous_finsetSum Finset.univ
        (fun i _ => (contDiff_directional hh (b i)).continuous.pow 2))) using 1
    ext x; dsimp [A]; ring
  have iC : Integrable C μ := integrable_cutoff_mul eta
    (continuous_finsetSum Finset.univ (fun i _ => continuous_finsetSum Finset.univ (fun j _ =>
      ((contDiff_directional eta.2.1 (b j)).continuous.mul
        (contDiff_directional hh (b i)).continuous).mul (hGc i j))))
  have hp (x : E) : -2 * C x ≤ A x / 2 + 2 * D x := by
    simpa only [A, C, D, mul_assoc] using
      HitAndRun.Analysis.weighted_skew_young ((eta : E → ℝ) x)
      (fun j => fderiv ℝ (eta : E → ℝ) x (b j))
      (fun i => fderiv ℝ h x (b i)) (fun i j => G i j x) (hG x) (heta x)
  have hi := integral_mono (iC.const_mul (-2)) ((iA.div_const 2).add (hGi.const_mul 2)) hp
  simp only [Pi.add_apply] at hi
  rw [integral_add (iA.div_const 2) (hGi.const_mul 2), integral_div,
    integral_const_mul, integral_const_mul] at hi
  have he := cutoff_energy_identity (μ := μ) eta h hh b G hGc hG hrel
  change (∫ x, A x ∂μ) = -2 * ∫ x, C x ∂μ at he
  change (∫ x, A x ∂μ) ≤ 4 * ∫ x, D x ∂μ
  linarith
end HitAndRun.Sobolev
