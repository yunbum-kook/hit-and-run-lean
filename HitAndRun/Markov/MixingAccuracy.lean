module
public import HitAndRun.Markov.MixingBudget
public import HitAndRun.Markov.HitAndRunOperatorMixing
public import HitAndRun.Markov.CoordinateKernelIdentificationMixing
@[expose] public section
namespace HitAndRun.Markov
open MeasureTheory ProbabilityTheory HitAndRun.Sobolev DikinD2
open scoped ENNReal ProbabilityTheory
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

/-- Finite optimal divergence energy is strictly positive on the actual nontrivial source carrier. -/
theorem finite_constant_toReal_pos (hC : K.constant < ⊤) : 0 < K.constant.toReal := by
  letI := target_nontrivial K
  obtain ⟨f, hf⟩ := exists_ne (0 : K.Target)
  have he := coordinateHeatBath_energy_bound K hC f
  have hp : 0 < ‖f‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
  by_contra h
  have hz : K.constant.toReal = 0 := le_antisymm (le_of_not_gt h) ENNReal.toReal_nonneg
  rw [hz, mul_zero, zero_mul] at he
  exact not_le_of_gt hp he

theorem coordinateHitAndRun_accuracy (hC : K.constant < ⊤)
    (ν : Measure K.carrier) [IsProbabilityMeasure ν]
    (hM : ChiSquareDensity.chiSquare ν K.bodyUniform < ⊤)
    (accuracy : ℝ) (hε : 0 < accuracy) (N : ℕ)
    (hN : mixingBudget (1 / ((n : ℝ) * K.constant.toReal))
      (ChiSquareDensity.chiSquare ν K.bodyUniform).toReal accuracy ≤ N) :
    ChiSquareDensity.chiSquare
      (NativeL2.lawOrbit (coordinateHitAndRun K.carrier K.isOpen.measurableSet) ν N) K.bodyUniform ≤
      ENNReal.ofReal accuracy := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  exact ennreal_error_le_accuracy (by have := finite_constant_toReal_pos K hC; positivity) hε
    _ _ hM N hN (coordinateHitAndRun_chiSquare K hC ν N)

theorem hitAndRun_accuracy (hC : K.constant < ⊤)
    (ν : Measure K.carrier) [IsProbabilityMeasure ν]
    (hM : ChiSquareDensity.chiSquare ν K.bodyUniform < ⊤)
    (accuracy : ℝ) (hε : 0 < accuracy) (N : ℕ)
    (hN : mixingBudget (((n : ℝ) + 2) / ((n : ℝ) * (2 + K.constant.toReal)))
      (ChiSquareDensity.chiSquare ν K.bodyUniform).toReal accuracy ≤ N) :
    ChiSquareDensity.chiSquare
      (NativeL2.lawOrbit (hitAndRun K.carrier K.isOpen K.isBounded) ν N) K.bodyUniform ≤
      ENNReal.ofReal accuracy := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  exact ennreal_error_le_accuracy (by positivity) hε _ _ hM N hN (hitAndRun_chiSquare K hC ν N)
end HitAndRun.Markov
