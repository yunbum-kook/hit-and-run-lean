module
public import HitAndRun.Markov.HitAndRunOperatorEnergy
public import HitAndRun.Markov.SpectralGap
@[expose] public section
namespace HitAndRun.Markov
open MeasureTheory HitAndRun.Sobolev
open scoped RealInnerProductSpace
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

/-- Exact source Proposition 2.1 Rayleigh bound for the actual HAR operator. -/
theorem hitAndRunOperator_rayleigh_bound (hC : K.constant < ⊤)
    (f : K.Target) (hf : f ≠ 0) :
    ((n : ℝ) + 2) / ((n : ℝ) * (2 + K.constant.toReal)) ≤
      inner ℝ (f : Lp ℝ 2 (K.ambient.restrict K.carrier))
        ((f : Lp ℝ 2 (K.ambient.restrict K.carrier)) - hitAndRunOperator K f) / ‖f‖ ^ 2 := by
  have he := directional_energy_comparison K hC f (directionalResidual_memLp K f)
  rw [← hitAndRunOperator_energy K] at he
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hn2 : 0 < (n : ℝ) + 2 := by positivity
  have hC2 : 0 < 2 + K.constant.toReal := by positivity
  have hc : 0 < (n : ℝ) / (n + 2) * (2 + K.constant.toReal) :=
    mul_pos (div_pos hn hn2) hC2
  have hp : 0 < ‖f‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
  have hr : 1 / ((n : ℝ) / (n + 2) * (2 + K.constant.toReal)) ≤
      inner ℝ (f : Lp ℝ 2 (K.ambient.restrict K.carrier))
        ((f : Lp ℝ 2 (K.ambient.restrict K.carrier)) - hitAndRunOperator K f) / ‖f‖ ^ 2 := by
    apply (div_le_div_iff₀ hc hp).2
    simpa only [one_mul, mul_comm] using he
  convert hr using 1 <;> field_simp <;> ring

/-- Proposition 2.1 with the literal nonempty centered Rayleigh infimum,
for the native operator of the actual uniform-sphere/chord transition. -/
theorem hitAndRun_source_gap (hC : K.constant < ⊤) :
    ((n : ℝ) + 2) / ((n : ℝ) * (2 + K.constant.toReal)) ≤
      spectralGap K (hitAndRunOperator K) :=
  le_spectralGap K (hitAndRunOperator K) _ (hitAndRunOperator_rayleigh_bound K hC)
end HitAndRun.Markov
