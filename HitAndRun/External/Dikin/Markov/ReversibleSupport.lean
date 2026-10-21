module
public import HitAndRun.External.Dikin.Markov.KernelIntegralLp
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.Probability.Kernel.Composition.WithDensity
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace DikinD2.ReversibleSupport
variable {α : Type*} [MeasurableSpace α]
variable {κ : Kernel α α} [IsMarkovKernel κ] {π : Measure α} [IsProbabilityMeasure π]

/-- Detailed balance as symmetry of the actual one-step joint law. -/
def JointReversible (κ : Kernel α α) (π : Measure α) : Prop :=
  (π ⊗ₘ κ).map Prod.swap = π ⊗ₘ κ

theorem stationary (h : JointReversible κ π) : κ ∘ₘ π = π := by
  have hh := congrArg Measure.snd h
  simpa only [Measure.snd_map_swap, Measure.snd_compProd, Measure.fst_compProd] using hh.symm

omit [IsMarkovKernel κ] [IsProbabilityMeasure π] in
theorem lintegral_swap (h : JointReversible κ π) {F : α × α → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ z, F z ∂(π ⊗ₘ κ) = ∫⁻ z, F z.swap ∂(π ⊗ₘ κ) := by
  conv_lhs => rw [← h]
  exact lintegral_map hF measurable_swap

/-- Density propagation for arbitrary measurable nonnegative extended densities. -/
theorem density_evolution (h : JointReversible κ π) {f : α → ℝ≥0∞}
    (hf : Measurable f) :
    κ ∘ₘ (π.withDensity f) = π.withDensity (fun x => ∫⁻ y, f y ∂κ x) := by
  apply Measure.ext_of_lintegral
  intro g hg
  calc
    ∫⁻ y, g y ∂(κ ∘ₘ π.withDensity f) =
        ∫⁻ x, ∫⁻ y, g y ∂κ x ∂π.withDensity f :=
      Measure.lintegral_bind κ.aemeasurable hg.aemeasurable
    _ = ∫⁻ x, f x * ∫⁻ y, g y ∂κ x ∂π :=
      lintegral_withDensity_eq_lintegral_mul _ hf hg.lintegral_kernel
    _ = ∫⁻ z, f z.1 * g z.2 ∂(π ⊗ₘ κ) := by
      rw [Measure.lintegral_compProd (by fun_prop)]
      congr 1; funext x
      exact (lintegral_const_mul _ hg).symm
    _ = ∫⁻ z, f z.2 * g z.1 ∂(π ⊗ₘ κ) := lintegral_swap h (by fun_prop)
    _ = ∫⁻ x, (∫⁻ y, f y ∂κ x) * g x ∂π := by
      rw [Measure.lintegral_compProd (by fun_prop)]
      congr 1; funext x
      simpa using (lintegral_mul_const (μ := κ x) (g x) hf)
    _ = ∫⁻ y, g y ∂π.withDensity (fun x => ∫⁻ y, f y ∂κ x) :=
      (lintegral_withDensity_eq_lintegral_mul _ hf.lintegral_kernel hg).symm

/-- Real integrable densities evolve by the genuine Bochner kernel integral. -/
theorem real_density_evolution (h : JointReversible κ π) {f : α → ℝ}
    (hf : Measurable f) (hi : Integrable f π) (hn : ∀ x, 0 ≤ f x) :
    κ ∘ₘ (π.withDensity (fun x => ENNReal.ofReal (f x))) =
      π.withDensity (fun x => ENNReal.ofReal (∫ y, f y ∂κ x)) := by
  rw [density_evolution h (by fun_prop)]
  apply withDensity_congr_ae
  have hi' : Integrable f (κ ∘ₘ π) := by rw [stationary h]; exact hi
  filter_upwards [Measure.ae_integrable_of_integrable_comp hi'] with x hx
  exact (ofReal_integral_eq_lintegral_ofReal hx (Filter.Eventually.of_forall hn)).symm

theorem integral_preserved (h : JointReversible κ π) {f : α → ℝ}
    (hf : Integrable f π) : (∫ x, ∫ y, f y ∂κ x ∂π) = ∫ y, f y ∂π := by
  have hi : Integrable f (κ ∘ₘ π) := by rw [stationary h]; exact hf
  have hj := (Measure.integrable_compProd_snd_iff hi.aestronglyMeasurable).mpr hi
  rw [← Measure.integral_compProd hj]
  have hm : AEStronglyMeasurable f ((π ⊗ₘ κ).map Prod.snd) := by
    change AEStronglyMeasurable f (Measure.snd (π ⊗ₘ κ))
    rw [Measure.snd_compProd, stationary h]
    exact hf.aestronglyMeasurable
  rw [← integral_map measurable_snd.aemeasurable hm]
  change (∫ y, f y ∂Measure.snd (π ⊗ₘ κ)) = _
  rw [Measure.snd_compProd, stationary h]

/-- Mean-zero real L2 is preserved and nonexpanded; no gap is asserted. -/
theorem meanZero_L2 (h : JointReversible κ π) {f : α → ℝ}
    (hf : MemLp f 2 π) (hz : ∫ x, f x ∂π = 0) :
    MemLp (fun x => ∫ y, f y ∂κ x) 2 π ∧
    (∫ x, ∫ y, f y ∂κ x ∂π) = 0 ∧
    eLpNorm (fun x => ∫ y, f y ∂κ x) 2 π ≤ eLpNorm f 2 π := by
  have hc := DikinD2.invariant_markovKernel_L2 (stationary h) hf
  exact ⟨hc.2, (integral_preserved h (hf.integrable (by norm_num))).trans hz, hc.1⟩

/-- Centered density propagation is represented by the same real kernel operator. -/
theorem centered_kernel_ae (h : JointReversible κ π) {f : α → ℝ}
    (hf : Integrable f π) :
    (fun x => (∫ y, f y ∂κ x) - 1) =ᵐ[π]
      (fun x => ∫ y, (f y - 1) ∂κ x) := by
  have hi : Integrable f (κ ∘ₘ π) := by rw [stationary h]; exact hf
  filter_upwards [Measure.ae_integrable_of_integrable_comp hi] with x hx
  rw [integral_sub hx (integrable_const 1)]
  simp

/-- Nonexpansion of the true centered L2 density, without a strict mixing rate. -/
theorem centered_L2 (h : JointReversible κ π) {f : α → ℝ}
    (hf : MemLp f 2 π) :
    eLpNorm (fun x => (∫ y, f y ∂κ x) - 1) 2 π ≤
      eLpNorm (fun x => f x - 1) 2 π := by
  rw [eLpNorm_congr_ae (centered_kernel_ae h (hf.integrable (by norm_num)))]
  exact (DikinD2.invariant_markovKernel_L2 (stationary h)
    (hf.sub (memLp_const (1 : ℝ)))).1

end DikinD2.ReversibleSupport
