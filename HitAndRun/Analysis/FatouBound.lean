module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! A direct finite-energy Fatou bound for nonnegative real approximants. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Analysis
open MeasureTheory Filter Topology
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem lintegral_bound_of_nonnegative_approximation
    {F : ℕ → α → ℝ} {f : α → ℝ} {C : ℝ}
    (hFi : ∀ n, Integrable (F n) μ)
    (hFn : ∀ n x, 0 ≤ F n x)
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hbound : ∀ n, ∫ x, F n x ∂μ ≤ C) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
  have he : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
      ∫⁻ x, liminf (fun n => ENNReal.ofReal (F n x)) atTop ∂μ := by
    apply lintegral_congr
    intro x
    exact (ENNReal.tendsto_ofReal (hlim x)).liminf_eq.symm
  rw [he]
  apply (lintegral_liminf_le' (fun n => (hFi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)).trans
  apply liminf_le_of_frequently_le'
  apply Filter.Eventually.frequently
  exact Filter.Eventually.of_forall fun n => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hFi n) (Filter.Eventually.of_forall (hFn n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)

theorem integral_bound_of_nonnegative_approximation
    {F : ℕ → α → ℝ} {f : α → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hFi : ∀ n, Integrable (F n) μ)
    (hFn : ∀ n x, 0 ≤ F n x) (hfn : ∀ x, 0 ≤ f x)
    (hfm : AEStronglyMeasurable f μ)
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hbound : ∀ n, ∫ x, F n x ∂μ ≤ C) :
    (∫ x, f x ∂μ) ≤ C := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hfn) hfm]
  have he := lintegral_bound_of_nonnegative_approximation hFi hFn hlim hbound
  simpa only [ENNReal.toReal_ofReal hC] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top he
end HitAndRun.Analysis
