import HitAndRun.Markov.ChiSquareContraction
import HitAndRun.Geometry.InnerBall
open MeasureTheory ProbabilityTheory DikinD2 DikinD2.NativeL2
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]
variable {κ : Kernel α α} [IsMarkovKernel κ]
variable {π ν : Measure α} [IsProbabilityMeasure π] [IsProbabilityMeasure ν]
example
    (hκ : ReversibleSupport.JointReversible κ π)
    (hp : (operator κ π (ReversibleSupport.stationary hκ)).IsPositive)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hgap : ∀ x ∈ meanZero π, lam * ‖x‖ ^ 2 ≤
      inner ℝ x (x - operator κ π (ReversibleSupport.stationary hκ) x))
    (N : ℕ) :
    ChiSquareDensity.chiSquare (lawOrbit κ ν N) π ≤
      ChiSquareDensity.chiSquare ν π * ENNReal.ofReal (Real.exp (-2 * lam * N)) := HitAndRun.Markov.chiSquare_lawOrbit_le_exp_of_gap hκ hp lam h0 h1 hgap N
#print axioms HitAndRun.Markov.chiSquare_lawOrbit_le_exp_of_gap
#print axioms DikinD2.NativeL2.lawOrbit_density
#print axioms DikinD2.NativeL2.centered_densityOrbit
#print axioms DikinD2.ChiSquareDensity.finite_density_package
#print axioms HitAndRun.Geometry.ball_subset_at_contraction
