/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
/-
Modified 2026-10-20: minimal dependency extraction for Dikin's pinned Mathlib.
Original: scottnarmstrong/MarkovProcess@666cda029098a1106914fc9fa7abd1727573284a.
Sources: Kernel/Basic.lean, Kernel/Integral.lean, Kernel/LpFinite.lean.
Retains original real-valued, sub-Markov, subinvariant, finite-p hypotheses.
No strict contraction, invariance, or reversibility is asserted.
-/
module

public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace MarkovProcess
variable {α : Type*} [MeasurableSpace α]

/-- A kernel is sub-Markov if each of its measures has total mass at most one. -/
def IsSubMarkovKernel {β : Type*} [MeasurableSpace β] (κ : ProbabilityTheory.Kernel α β) : Prop :=
  ∀ x, κ x Set.univ ≤ 1

namespace IsSubMarkovKernel
variable {κ : Kernel α α}

/-- A sub-Markov kernel is a finite kernel. -/
theorem isFiniteKernel (hκ : IsSubMarkovKernel κ) : IsFiniteKernel κ :=
  ⟨⟨1, ENNReal.one_lt_top, hκ⟩⟩

/-- Every Markov kernel is sub-Markov. -/
theorem of_isMarkovKernel (κ : Kernel α α) [IsMarkovKernel κ] : IsSubMarkovKernel κ := by
  intro x
  exact le_of_eq measure_univ

end IsSubMarkovKernel

/-- The raw real-valued integral of `f` against the measure `κ x`. -/
noncomputable def kernelIntegral (κ : Kernel α α) (f : α → ℝ) (x : α) : ℝ :=
  ∫ y, f y ∂κ x

/-- Under subinvariance, integrating an almost-everywhere strongly measurable
function against `κ x` gives an almost-everywhere strongly measurable function
of `x`. -/
theorem AEStronglyMeasurable.kernelIntegral {μ : Measure α} {κ : Kernel α α}
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (hκμ : κ ∘ₘ μ ≤ μ) :
    AEStronglyMeasurable (kernelIntegral κ f) μ := by
  let hfComp : AEStronglyMeasurable f (κ ∘ₘ μ) :=
    hf.mono_ac (Measure.absolutelyContinuous_of_le hκμ)
  refine ⟨fun x ↦ MarkovProcess.kernelIntegral κ (hfComp.mk f) x, ?_, ?_⟩
  · exact hfComp.stronglyMeasurable_mk.integral_kernel
  · filter_upwards [Measure.ae_ae_of_ae_comp hfComp.ae_eq_mk] with x hx
    exact integral_congr_ae hx

/-- On a finite measure of mass at most one, the `L¹` seminorm is bounded by
every finite `Lᵖ` seminorm with `p ≥ 1`. -/
theorem eLpNorm_one_le_of_measure_univ_le_one {ν : Measure α} {f : α → ℝ}
    [IsFiniteMeasure ν] {p : NNReal} (hp : 1 ≤ p) (hν : ν Set.univ ≤ 1)
    (hf : AEStronglyMeasurable f ν) :
    eLpNorm f 1 ν ≤ eLpNorm f p ν := by
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := ν) (f := f) (p := (1 : ℝ≥0∞)) (q := (p : ℝ≥0∞))
    (by exact_mod_cast hp) hf
  calc
    eLpNorm f 1 ν
        ≤ eLpNorm f p ν * ν Set.univ ^ (1 - 1 / (p : ℝ)) := by
          simpa using hcompare
    _ ≤ eLpNorm f p ν * 1 := by
          gcongr
          calc
            ν Set.univ ^ (1 - 1 / (p : ℝ))
                ≤ (1 : ℝ≥0∞) ^ (1 - 1 / (p : ℝ)) := by
                  exact ENNReal.rpow_le_rpow hν (by
                    rw [sub_nonneg, div_le_one (by exact_mod_cast zero_lt_one.trans_le hp)]
                    exact_mod_cast hp)
            _ = 1 := ENNReal.one_rpow _
    _ = eLpNorm f p ν := mul_one _

/-- Jensen's power estimate for a finite subprobability measure.  This form is
well suited to fibrewise use because both sides take values in `ℝ≥0∞`. -/
theorem enorm_integral_rpow_le_lintegral_enorm_rpow
    {ν : Measure α} [IsFiniteMeasure ν] {f : α → ℝ} {p : NNReal}
    (hp : 1 ≤ p) (hν : ν Set.univ ≤ 1) (hf : MemLp f p ν) :
    ‖∫ y, f y ∂ν‖ₑ ^ (p : ℝ) ≤ ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂ν := by
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
  have hnorm : ‖∫ y, f y ∂ν‖ₑ ≤ eLpNorm f p ν := by
    calc
      ‖∫ y, f y ∂ν‖ₑ ≤ ∫⁻ y, ‖f y‖ₑ ∂ν := enorm_integral_le_lintegral_enorm f
      _ = eLpNorm f 1 ν := (eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable).symm
      _ ≤ eLpNorm f p ν := eLpNorm_one_le_of_measure_univ_le_one hp hν hf.aestronglyMeasurable
  calc
    ‖∫ y, f y ∂ν‖ₑ ^ (p : ℝ) ≤ eLpNorm f p ν ^ (p : ℝ) := by
      exact ENNReal.rpow_le_rpow hnorm (by positivity)
    _ = ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂ν :=
      eLpNorm_nnreal_pow_eq_lintegral hp0 hf.aestronglyMeasurable

/-- The integrated fibrewise power estimate for a sub-Markov kernel. -/
theorem lintegral_enorm_kernelIntegral_rpow_le
    {μ : Measure α} {κ : Kernel α α} (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) {f : α → ℝ} {p : NNReal}
    (hp : 1 ≤ p) (hf : MemLp f p μ) :
    ∫⁻ x, ‖kernelIntegral κ f x‖ₑ ^ (p : ℝ) ∂μ
      ≤ ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂μ := by
  let : IsFiniteKernel κ := hκ.isFiniteKernel
  have hfComp : MemLp f p (κ ∘ₘ μ) := hf.mono_measure hκμ
  have hfFiber : ∀ᵐ x ∂μ, MemLp f p (κ x) := by
    have hFiberEq := Measure.ae_ae_of_ae_comp hfComp.aestronglyMeasurable.ae_eq_mk
    have hp0 : (p : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast ne_of_gt (zero_lt_one.trans_le hp)
    have hpowInt := hfComp.integrable_norm_rpow hp0 ENNReal.coe_ne_top
    have hFiberInt := Measure.ae_integrable_of_integrable_comp hpowInt
    filter_upwards [hFiberEq, hFiberInt] with x hxEq hxInt
    have hxEq' : f =ᵐ[κ x] hfComp.aestronglyMeasurable.mk f := hxEq
    have hxMeas : AEStronglyMeasurable f (κ x) :=
      hfComp.aestronglyMeasurable.stronglyMeasurable_mk.aestronglyMeasurable.congr hxEq'.symm
    exact (integrable_norm_rpow_iff hxMeas hp0 ENNReal.coe_ne_top).mp hxInt
  calc
    ∫⁻ x, ‖kernelIntegral κ f x‖ₑ ^ (p : ℝ) ∂μ
        ≤ ∫⁻ x, ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂κ x ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hfFiber] with x hx
          exact enorm_integral_rpow_le_lintegral_enorm_rpow hp (hκ x) hx
    _ = ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂(κ ∘ₘ μ) := by
          symm
          exact Measure.lintegral_bind (Kernel.aemeasurable κ)
            (hfComp.aestronglyMeasurable.enorm.pow_const (p : ℝ))
    _ ≤ ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂μ :=
      lintegral_mono' hκμ le_rfl

/-- A sub-Markov kernel which is subinvariant for `μ` is contractive on every
finite `Lᵖ` seminorm, `1 ≤ p < ∞`. -/
theorem eLpNorm_kernelIntegral_le
    {μ : Measure α} {κ : Kernel α α} (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) {f : α → ℝ} {p : NNReal}
    (hp : 1 ≤ p) (hf : MemLp f p μ) :
    eLpNorm (kernelIntegral κ f) p μ ≤ eLpNorm f p μ := by
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
  rw [eLpNorm_nnreal_eq_lintegral hp0
      (AEStronglyMeasurable.kernelIntegral hf.aestronglyMeasurable hκμ),
    eLpNorm_nnreal_eq_lintegral hp0 hf.aestronglyMeasurable]
  apply ENNReal.rpow_le_rpow
  · exact lintegral_enorm_kernelIntegral_rpow_le hκ hκμ hp hf
  · positivity

/-- The kernel integral of an `Lᵖ` function is again in `Lᵖ` for every finite
exponent `p ≥ 1`. -/
theorem MemLp.kernelIntegral
    {μ : Measure α} {κ : Kernel α α} (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) {f : α → ℝ} {p : NNReal}
    (hp : 1 ≤ p) (hf : MemLp f p μ) :
    MemLp (kernelIntegral κ f) p μ := by
  exact (eLpNorm_kernelIntegral_le hκ hκμ hp hf).trans_lt hf.eLpNorm_lt_top

end MarkovProcess
