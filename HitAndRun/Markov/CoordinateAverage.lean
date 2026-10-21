module
public import HitAndRun.Markov.ConditionalProjection
public import Mathlib.Tactic.FieldSimp
@[expose] public section

/-! Finite uniform averaging of actual conditional projections.
The coordinate sigma-algebras and chord-kernel realization remain separate obligations. -/
namespace HitAndRun.Markov
open MeasureTheory
variable {α ι : Type*} [Fintype ι]
variable {m0 : MeasurableSpace α} {μ : @Measure α m0}

noncomputable def coordinateAverage (m : ι → MeasurableSpace α)
    (hm : ∀ i, m i ≤ m0) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ i, conditionalProjection (hm i) f

theorem coordinateAverage_positive (m : ι → MeasurableSpace α)
    (hm : ∀ i, m i ≤ m0) (f : Lp ℝ 2 μ) :
    0 ≤ inner ℝ f (coordinateAverage m hm f) := by
  unfold coordinateAverage
  rw [inner_smul_right, inner_sum]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i _ => conditionalProjection_positive (hm i) f)

theorem coordinateAverage_symmetric (m : ι → MeasurableSpace α)
    (hm : ∀ i, m i ≤ m0) (f g : Lp ℝ 2 μ) :
    inner ℝ (coordinateAverage m hm f) g = inner ℝ f (coordinateAverage m hm g) := by
  simp only [coordinateAverage, inner_smul_left, inner_smul_right, inner_sum, sum_inner,
    conj_trivial, conditionalProjection_symmetric]

theorem coordinateAverage_energy [Nonempty ι] (m : ι → MeasurableSpace α)
    (hm : ∀ i, m i ≤ m0) (f : Lp ℝ 2 μ) :
    inner ℝ f (f - coordinateAverage m hm f) =
    (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖f - conditionalProjection (hm i) f‖ ^ 2 := by
  simp_rw [← conditionalProjection_residual_energy, inner_sub_right]
  simp only [coordinateAverage, inner_smul_right, inner_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  field_simp
end HitAndRun.Markov
