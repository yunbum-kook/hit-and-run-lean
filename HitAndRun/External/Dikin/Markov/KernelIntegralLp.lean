module
public import HitAndRun.External.Dikin.Markov.MarkovLp
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace DikinD2
variable {α : Type*} [MeasurableSpace α]

/-- The bridge uses Mathlib's kernel directly, with pointwise subprobability mass
and subinvariance supplied as explicit mathematical hypotheses. -/
theorem kernelIntegral_finiteLp {κ : Kernel α α} {μ : Measure α}
    (hκ : ∀ x, κ x Set.univ ≤ 1) (hκμ : κ ∘ₘ μ ≤ μ)
    {p : NNReal} (hp : 1 ≤ p) {f : α → ℝ} (hf : MemLp f p μ) :
    eLpNorm (fun x => ∫ y, f y ∂κ x) p μ ≤ eLpNorm f p μ ∧
      MemLp (fun x => ∫ y, f y ∂κ x) p μ :=
  ⟨MarkovProcess.eLpNorm_kernelIntegral_le hκ hκμ hp hf,
    MarkovProcess.MemLp.kernelIntegral hκ hκμ hp hf⟩

/-- Nonexpansion and closure at p=2, not a positive spectral gap. -/
theorem kernelIntegral_L2 {κ : Kernel α α} {μ : Measure α}
    (hκ : ∀ x, κ x Set.univ ≤ 1) (hκμ : κ ∘ₘ μ ≤ μ)
    {f : α → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm (fun x => ∫ y, f y ∂κ x) 2 μ ≤ eLpNorm f 2 μ ∧
      MemLp (fun x => ∫ y, f y ∂κ x) 2 μ := by
  exact kernelIntegral_finiteLp (p := (2 : NNReal)) hκ hκμ (by norm_num) hf

/-- The Markov interface already used in Dikin requires no representation conversion.
Invariance is a premise, not something supplied by the nonexpansion theorem. -/
theorem invariant_markovKernel_L2 {κ : Kernel α α} [IsMarkovKernel κ]
    {μ : Measure α} (hκμ : κ ∘ₘ μ = μ) {f : α → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm (fun x => ∫ y, f y ∂κ x) 2 μ ≤ eLpNorm f 2 μ ∧
      MemLp (fun x => ∫ y, f y ∂κ x) 2 μ :=
  kernelIntegral_L2 (MarkovProcess.IsSubMarkovKernel.of_isMarkovKernel κ) hκμ.le hf
end DikinD2
