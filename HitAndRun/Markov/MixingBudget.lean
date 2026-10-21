module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Tactic
@[expose] public section

namespace HitAndRun.Markov
open scoped ENNReal

/-- Integer-time convention: no step is needed when the initial error is already small.
Otherwise round the positive logarithmic sufficient time upward. -/
noncomputable def mixingBudget (rate initialError accuracy : ℝ) : ℕ :=
  if initialError ≤ accuracy then 0 else
    Nat.ceil (Real.log (initialError / accuracy) / (2 * rate))

@[simp] theorem mixingBudget_zero_step {rate initialError accuracy : ℝ}
    (h : initialError ≤ accuracy) : mixingBudget rate initialError accuracy = 0 := by
  simp [mixingBudget, h]

/-- The source logarithmic time bound, including zero initial error and the zero-step branch. -/
theorem exp_error_le_accuracy {rate initialError accuracy : ℝ}
    (hr : 0 < rate) (hM : 0 ≤ initialError) (hε : 0 < accuracy)
    (N : ℕ) (hN : mixingBudget rate initialError accuracy ≤ N) :
    initialError * Real.exp (-2 * rate * N) ≤ accuracy := by
  by_cases hsmall : initialError ≤ accuracy
  · have he : Real.exp (-2 * rate * N) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hr.le (Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
    exact (mul_le_of_le_one_right hM he).trans hsmall
  · have hMp : 0 < initialError := lt_trans hε (lt_of_not_ge hsmall)
    have htime : Real.log (initialError / accuracy) / (2 * rate) ≤ (N : ℝ) := by
      apply Nat.le_of_ceil_le
      simpa only [mixingBudget, ite_eq_right hsmall] using hN
    have hlog := (div_le_iff₀ (show 0 < 2 * rate by positivity)).1 htime
    have he : Real.exp (-2 * rate * N) ≤ Real.exp (-Real.log (initialError / accuracy)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc
      _ ≤ initialError * Real.exp (-Real.log (initialError / accuracy)) := mul_le_mul_of_nonneg_left he hM
      _ = accuracy := by
        rw [Real.exp_neg, Real.exp_log (div_pos hMp hε)]
        field_simp

/-- A finite extended-real error bound inherits the exact integer accuracy budget.
Infinite initial error is not turned into a finite guarantee. -/
theorem ennreal_error_le_accuracy {rate accuracy : ℝ} (hr : 0 < rate) (hε : 0 < accuracy)
    (initialError error : ℝ≥0∞) (hM : initialError < ⊤) (N : ℕ)
    (hN : mixingBudget rate initialError.toReal accuracy ≤ N)
    (herror : error ≤ initialError * ENNReal.ofReal (Real.exp (-2 * rate * N))) :
    error ≤ ENNReal.ofReal accuracy := by
  apply herror.trans
  rw [← ENNReal.ofReal_toReal hM.ne, ← ENNReal.ofReal_mul (ENNReal.toReal_nonneg)]
  exact ENNReal.ofReal_le_ofReal (exp_error_le_accuracy hr ENNReal.toReal_nonneg hε N hN)

/-- An infinite initial chi-square bound remains vacuous at every finite time. -/
theorem infinite_initial_error_vacuous (rate : ℝ) (N : ℕ) (error : ℝ≥0∞) :
    error ≤ ⊤ * ENNReal.ofReal (Real.exp (-2 * rate * N)) := by
  rw [ENNReal.top_mul (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))]
  exact le_top

end HitAndRun.Markov
