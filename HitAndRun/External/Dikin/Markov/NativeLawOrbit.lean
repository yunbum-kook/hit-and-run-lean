module
public import HitAndRun.External.Dikin.Markov.NativeOperator
public import HitAndRun.External.Dikin.Probability.ChiSquareDensity
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace DikinD2.NativeL2
variable {α : Type*} [MeasurableSpace α]
variable {κ Q : Kernel α α} [IsMarkovKernel κ] [IsMarkovKernel Q]
variable {π ν : Measure α} [IsProbabilityMeasure π] [IsProbabilityMeasure ν]

/-- Iteration of the actual Markov transition on measures. -/
noncomputable def lawOrbit (κ : Kernel α α) (ν : Measure α) : ℕ → Measure α
  | 0 => ν
  | n + 1 => κ ∘ₘ lawOrbit κ ν n

/-- Measurable raw densities under the actual kernel action, not L2 representatives. -/
noncomputable def densityOrbit (κ : Kernel α α) (f : α → ℝ) : ℕ → α → ℝ
  | 0 => f
  | n + 1 => fun x => ∫ y, densityOrbit κ f n y ∂κ x

instance lawOrbit_probability (n : ℕ) : IsProbabilityMeasure (lawOrbit κ ν n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure ν)
  | succ n ih =>
    letI := ih
    change IsProbabilityMeasure (κ ∘ₘ lawOrbit κ ν n)
    infer_instance

theorem densityOrbit_measurable {f : α → ℝ} (hm : Measurable f) (n : ℕ) :
    Measurable (densityOrbit κ f n) := by
  induction n with
  | zero => exact hm
  | succ n ih => exact ih.stronglyMeasurable.integral_kernel.measurable

theorem densityOrbit_nonneg {f : α → ℝ} (hn : ∀ x, 0 ≤ f x) (n : ℕ) :
    ∀ x, 0 ≤ densityOrbit κ f n x := by
  induction n with
  | zero => exact hn
  | succ n ih => exact fun x => integral_nonneg ih

theorem densityOrbit_memLp (hκ : ReversibleSupport.JointReversible κ π)
    {f : α → ℝ} (hf : MemLp f 2 π) (n : ℕ) : MemLp (densityOrbit κ f n) 2 π := by
  induction n with
  | zero => exact hf
  | succ n ih => exact (DikinD2.invariant_markovKernel_L2 (ReversibleSupport.stationary hκ) ih).2

/-- Existing one-step density evolution iterates to the actual measure orbit. -/
theorem lawOrbit_density (hκ : ReversibleSupport.JointReversible κ π)
    {f : α → ℝ} (hm : Measurable f) (hn : ∀ x, 0 ≤ f x) (hf : MemLp f 2 π)
    (hr : ν = π.withDensity (fun x => ENNReal.ofReal (f x))) (n : ℕ) :
    lawOrbit κ ν n = π.withDensity (fun x => ENNReal.ofReal (densityOrbit κ f n x)) := by
  induction n with
  | zero => exact hr
  | succ n ih =>
    change κ ∘ₘ lawOrbit κ ν n = _
    rw [ih]
    exact ReversibleSupport.real_density_evolution hκ (densityOrbit_measurable hm n)
      ((densityOrbit_memLp hκ hf n).integrable (by norm_num)) (densityOrbit_nonneg hn n)

/-- Centering a raw L2 density and acting agrees with centering its actual successor. -/
theorem centered_toLp_step (hκ : ReversibleSupport.JointReversible κ π)
    {f : α → ℝ} (hf : MemLp f 2 π) :
    operator κ π (ReversibleSupport.stationary hκ)
      ((hf.sub (memLp_const (1 : ℝ))).toLp (fun x => f x - 1)) =
      (((DikinD2.invariant_markovKernel_L2 (ReversibleSupport.stationary hκ) hf).2).sub
        (memLp_const (1 : ℝ))).toLp (fun x => (∫ y, f y ∂κ x) - 1) := by
  apply Lp.ext
  refine (operator_ae _ _).trans ?_
  have he := MemLp.coeFn_toLp (hf.sub (memLp_const (1 : ℝ)))
  refine (MarkovProcess.kernelIntegral_congr_ae (ReversibleSupport.stationary hκ).le he).trans ?_
  exact (ReversibleSupport.centered_kernel_ae hκ (hf.integrable (by norm_num))).symm.trans
    (MemLp.coeFn_toLp _).symm

/-- The centered-density orbit is exactly the native L2 operator orbit. -/
theorem centered_densityOrbit (hκ : ReversibleSupport.JointReversible κ π)
    {f : α → ℝ} (hf : MemLp f 2 π) (n : ℕ) :
    (operator κ π (ReversibleSupport.stationary hκ) : Lp ℝ 2 π → Lp ℝ 2 π)^[n]
      ((hf.sub (memLp_const (1 : ℝ))).toLp (fun x => f x - 1)) =
      (((densityOrbit_memLp hκ hf n).sub (memLp_const (1 : ℝ))).toLp
        (fun x => densityOrbit κ f n x - 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    exact centered_toLp_step hκ (densityOrbit_memLp hκ hf n)

theorem centered_toLp_meanZero {f : α → ℝ} (hf : MemLp f 2 π)
    (h1 : ∫ x, f x ∂π = 1) :
    (hf.sub (memLp_const (1 : ℝ))).toLp (fun x => f x - 1) ∈ meanZero π := by
  rw [mem_meanZero, integral_congr_ae (MemLp.coeFn_toLp _),
    integral_sub (hf.integrable (by norm_num)) (integrable_const (1 : ℝ)), h1]
  simp


end DikinD2.NativeL2
