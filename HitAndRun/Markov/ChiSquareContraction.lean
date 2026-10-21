module
public import HitAndRun.External.Dikin.Markov.NativeLawOrbit
public import HitAndRun.Analysis.PositiveContraction
@[expose] public section

/-! Reuse of the Dikin actual-law transport, without artificial lazification.
Positivity and the gap remain genuine obligations for each concrete chord kernel. -/
namespace HitAndRun.Markov
open MeasureTheory ProbabilityTheory DikinD2 DikinD2.NativeL2
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]
variable {κ : Kernel α α} [IsMarkovKernel κ]
variable {π ν : Measure α} [IsProbabilityMeasure π] [IsProbabilityMeasure ν]

theorem chiSquare_lawOrbit_le_exp_of_gap
    (hκ : ReversibleSupport.JointReversible κ π)
    (hp : (operator κ π (ReversibleSupport.stationary hκ)).IsPositive)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hgap : ∀ x ∈ meanZero π, lam * ‖x‖ ^ 2 ≤
      inner ℝ x (x - operator κ π (ReversibleSupport.stationary hκ) x))
    (N : ℕ) :
    ChiSquareDensity.chiSquare (lawOrbit κ ν N) π ≤
      ChiSquareDensity.chiSquare ν π * ENNReal.ofReal (Real.exp (-2 * lam * N)) := by
  by_cases hc : ChiSquareDensity.chiSquare ν π = ∞
  · rw [hc, ENNReal.top_mul (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))]
    exact le_top
  obtain ⟨hm, hn, hr, hf, hmass⟩ := ChiSquareDensity.finite_density_package hc
  let f := ChiSquareDensity.density ν π
  let e := (hf.sub (memLp_const (1 : ℝ))).toLp (fun x => f x - 1)
  have he : e ∈ meanZero π := centered_toLp_meanZero hf hmass
  have hdec := HitAndRun.Analysis.iterate_sq_le_exp_on_submodule
    (operator κ π (ReversibleSupport.stationary hκ)) hp (meanZero π)
    (meanZero_invariant hκ) lam h0 h1 hgap N e he
  have hstart := ChiSquareDensity.chiSquare_eq_centered_norm_sq hm hn hf hr
  have hend := ChiSquareDensity.chiSquare_eq_centered_norm_sq
    (densityOrbit_measurable hm N) (densityOrbit_nonneg hn N)
    (densityOrbit_memLp hκ hf N) (lawOrbit_density hκ hm hn hf hr N)
  rw [hend, hstart, ← centered_densityOrbit hκ hf N]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-2 * lam * N) * ‖e‖ ^ 2) := ENNReal.ofReal_le_ofReal hdec
    _ = _ := by rw [ENNReal.ofReal_mul (Real.exp_pos _).le]; exact mul_comm _ _
end HitAndRun.Markov
