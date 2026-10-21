module
public import HitAndRun.Markov.BodyChordKernel
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
@[expose] public section

namespace HitAndRun.Markov
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Uniform finite mixture of kernels, with the literal inverse-cardinality weight. -/
noncomputable def finiteAverageKernel {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι] (κ : ι → Kernel α β) : Kernel α β where
  toFun x := (Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, κ i x
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
    exact measurable_const.mul (Finset.measurable_fun_sum _ (fun i _ => (κ i).measurable_coe hA))

theorem finiteAverageKernel_markov {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι] [Nonempty ι] (κ : ι → Kernel α β) (hp : ∀ i, IsMarkovKernel (κ i)) :
    IsMarkovKernel (finiteAverageKernel κ) := by
  constructor
  intro x
  constructor
  have hu : ∀ i, κ i x univ = 1 := by
    intro i
    letI := hp i
    exact measure_univ
  change ((Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, κ i x) univ = 1
  simp only [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul, hu,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel
    (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)) (ENNReal.natCast_ne_top _)

variable {n : ℕ} [NeZero n]

/-- Coordinate Hit-and-Run's actual uniform-chord kernel on the body. -/
noncomputable def coordinateHitAndRun (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : MeasurableSet K) : Kernel K K :=
  finiteAverageKernel (fun i : Fin n => directionKernel K hK
    (EuclideanSpace.basisFun (Fin n) ℝ i) ((EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i))

theorem coordinateHitAndRun_markov {K : Set (EuclideanSpace ℝ (Fin n))}
    (ho : IsOpen K) (hb : Bornology.IsBounded K) :
    IsMarkovKernel (coordinateHitAndRun K ho.measurableSet) := by
  apply finiteAverageKernel_markov
  intro i
  exact directionKernel_markov ho hb _ _
end HitAndRun.Markov
