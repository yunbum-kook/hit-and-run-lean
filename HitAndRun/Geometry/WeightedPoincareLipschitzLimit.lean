module
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Sqrt
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
  {μ : Measure X} [IsProbabilityMeasure μ]

 theorem integral_norm_le_sqrt_integral_sq {f : X → F} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  have hv := variance_nonneg (fun x => ‖f x‖) μ
  rw [variance_eq_sub hf.norm] at hv
  apply (Real.le_sqrt (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => sq_nonneg _)).mpr
  change 0 ≤ (∫ x, ‖f x‖ ^ 2 ∂μ) - (∫ x, ‖f x‖ ∂μ) ^ 2 at hv
  linarith

 theorem tendsto_integral_norm_sub_of_sq {f : X → F} {u : ℕ → X → F}
    (hf : MemLp f 2 μ) (hu : ∀ k, MemLp (u k) 2 μ)
    (hs : Tendsto (fun k => ∫ x, ‖u k x - f x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖u k x - f x‖ ∂μ) atTop (𝓝 0) := by
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [Real.sqrt_zero] at ht
  apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_) ht
  exact integral_norm_le_sqrt_integral_sq ((hu k).sub hf)

 theorem abs_integral_norm_sub_le {f g : X → F} (hf : Integrable f μ) (hg : Integrable g μ) :
    |(∫ x, ‖f x‖ ∂μ) - ∫ x, ‖g x‖ ∂μ| ≤ ∫ x, ‖f x - g x‖ ∂μ := by
  rw [← integral_sub hf.norm hg.norm, ← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono (hf.norm.sub hg.norm).norm (hf.sub hg).norm
  intro x
  change ‖‖f x‖ - ‖g x‖‖ ≤ ‖f x - g x‖
  simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (f x) (g x)

 theorem tendsto_integral_norm_of_sq {f : X → F} {u : ℕ → X → F}
    (hf : MemLp f 2 μ) (hu : ∀ k, MemLp (u k) 2 μ)
    (hs : Tendsto (fun k => ∫ x, ‖u k x - f x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖u k x‖ ∂μ) atTop (𝓝 (∫ x, ‖f x‖ ∂μ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun k => ?_) (tendsto_integral_norm_sub_of_sq hf hu hs)
  simpa only [Real.norm_eq_abs] using abs_integral_norm_sub_le
    ((hu k).integrable (by norm_num)) (hf.integrable (by norm_num))

 theorem tendsto_integral_weighted_norm_of_sq [NormedSpace ℝ F]
    {f : X → F} {u : ℕ → X → F} {w : X → ℝ} {D : ℝ}
    (hf : MemLp f 2 μ) (hu : ∀ k, MemLp (u k) 2 μ) (hw : MemLp w ∞ μ)
    (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x) (hD : ∀ᵐ x ∂μ, w x ≤ D)
    (hs : Tendsto (fun k => ∫ x, ‖u k x - f x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, w x * ‖u k x‖ ∂μ) atTop (𝓝 (∫ x, w x * ‖f x‖ ∂μ)) := by
  have hs' : Tendsto (fun k => ∫ x, ‖w x • u k x - w x • f x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have hupper := hs.const_mul (D ^ 2)
    simp only [mul_zero] at hupper
    apply squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun k => ?_) hupper
    rw [← integral_const_mul]
    apply integral_mono_ae ((hw.smul (hu k)).sub (hw.smul hf)).norm.integrable_sq
      (((hu k).sub hf).norm.integrable_sq.const_mul (D ^ 2))
    filter_upwards [hw0, hD] with x hx0 hxD
    change ‖w x • u k x - w x • f x‖ ^ 2 ≤ D ^ 2 * ‖u k x - f x‖ ^ 2
    simp only [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hx0, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx0 hxD 2) (sq_nonneg _)
  have ht := tendsto_integral_norm_of_sq (hw.smul hf) (fun k => hw.smul (hu k)) hs'
  change Tendsto (fun k => ∫ x, ‖w x • u k x‖ ∂μ) atTop (𝓝 (∫ x, ‖w x • f x‖ ∂μ)) at ht
  have he : ∀ g : X → F, (∫ x, ‖w x • g x‖ ∂μ) = ∫ x, w x * ‖g x‖ ∂μ := by
    intro g
    apply integral_congr_ae
    filter_upwards [hw0] with x hx
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx]
  simpa only [he] using ht

 theorem minimizing_center_bound_of_L1_limit {f : X → ℝ} {u : ℕ → X → ℝ}
    {m A E : ℝ} {energy : ℕ → ℝ}
    (hf : Integrable f μ) (hu : ∀ k, Integrable (u k) μ)
    (hmin : ∀ z : ℝ, (∫ x, ‖f x - m‖ ∂μ) ≤ ∫ x, ‖f x - z‖ ∂μ)
    (he : Tendsto (fun k => ∫ x, ‖u k x - f x‖ ∂μ) atTop (𝓝 0))
    (henergy : Tendsto energy atTop (𝓝 E))
    (hbound : ∀ k, ∃ z : ℝ, (∫ x, ‖u k x - z‖ ∂μ) ≤ A * energy k) :
    (∫ x, ‖f x - m‖ ∂μ) ≤ A * E := by
  have ht := he.add (henergy.const_mul A)
  simp only [zero_add] at ht
  apply ge_of_tendsto ht
  exact Eventually.of_forall fun k => by
    obtain ⟨z, hz⟩ := hbound k
    apply (hmin z).trans
    have htri : (∫ x, ‖f x - z‖ ∂μ) ≤
        (∫ x, ‖u k x - f x‖ ∂μ) + ∫ x, ‖u k x - z‖ ∂μ := by
      have hi1 : Integrable (fun x => ‖u k x - f x‖) μ := ((hu k).sub hf).norm
      have hi2 : Integrable (fun x => ‖u k x - z‖) μ := ((hu k).sub (integrable_const z)).norm
      rw [← integral_add hi1 hi2]
      apply integral_mono (hf.sub (integrable_const z)).norm
        (((hu k).sub hf).norm.add ((hu k).sub (integrable_const z)).norm)
      intro x
      change ‖f x - z‖ ≤ ‖u k x - f x‖ + ‖u k x - z‖
      simpa only [norm_sub_rev (f x) (u k x)] using norm_sub_le_norm_sub_add_norm_sub (f x) (u k x) z
    exact htri.trans (add_le_add le_rfl hz)
end HitAndRun.Geometry
