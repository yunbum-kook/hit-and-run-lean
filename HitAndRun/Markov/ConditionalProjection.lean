import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.Tactic.Linarith

/-! Actual L² conditional expectations: source equation (1.1).
Identifying these projections with uniform chord kernels is a separate obligation. -/
namespace HitAndRun.Markov
open MeasureTheory
variable {α : Type*} {m m0 : MeasurableSpace α} {μ : @Measure α m0}

noncomputable def conditionalProjection (hm : m ≤ m0) (f : Lp ℝ 2 μ) :
    Lp ℝ 2 μ := condExpL2 ℝ ℝ hm f

theorem conditionalProjection_idempotent (hm : m ≤ m0) (f : Lp ℝ 2 μ) :
    conditionalProjection hm (conditionalProjection hm f) = conditionalProjection hm f := by
  let : Fact (m ≤ m0) := ⟨hm⟩
  simp only [conditionalProjection, condExpL2,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem conditionalProjection_symmetric (hm : m ≤ m0) (f g : Lp ℝ 2 μ) :
    inner ℝ (conditionalProjection hm f) g = inner ℝ f (conditionalProjection hm g) :=
  inner_condExpL2_left_eq_right hm

theorem conditionalProjection_positive (hm : m ≤ m0) (f : Lp ℝ 2 μ) :
    0 ≤ inner ℝ f (conditionalProjection hm f) := by
  have h := conditionalProjection_symmetric hm f (conditionalProjection hm f)
  rw [conditionalProjection_idempotent] at h
  rw [← h, real_inner_self_eq_norm_sq]
  exact sq_nonneg _

theorem conditionalProjection_residual_energy (hm : m ≤ m0) (f : Lp ℝ 2 μ) :
    inner ℝ f (f - conditionalProjection hm f) = ‖f - conditionalProjection hm f‖ ^ 2 := by
  have h := conditionalProjection_symmetric hm f (conditionalProjection hm f)
  rw [conditionalProjection_idempotent] at h
  rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right]
  have hc := real_inner_comm (conditionalProjection hm f) f
  linarith
end HitAndRun.Markov
