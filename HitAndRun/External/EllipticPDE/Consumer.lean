module

public import HitAndRun.External.EllipticPDE.Poincare.GraphBounded

/-!
# Concrete consumers of the adapted Sobolev graph

Project-written bridge, not an upstream EllipticPDE file. No source-paper
numbered result is claimed by this foundation consumer.
-/

@[expose] public section

namespace HitAndRun.Sobolev

open MeasureTheory EllipticPdes
open EllipticPdes.H1Graph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

omit [Nontrivial E] in
/-- The closed zero-trace graph is a complete space with its original graph norm. -/
theorem h01_complete : CompleteSpace (H01 μ Ω) := inferInstance

omit [Nontrivial E] in
/-- Every genuine zero-trace graph satisfies the weak derivative constraints. -/
theorem h01_weak (u : H01 μ Ω) : (u : H1Graph μ Ω) ∈ W12 μ Ω :=
  H01_le_W12 u.property

/-- The full graph norm is controlled by the actual gradient on a bounded domain. -/
theorem graph_norm_sq_le_gradient (hb : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H01 μ Ω,
      ‖(u : H1Graph μ Ω)‖ ^ 2 ≤ C * ‖gradL (u : H1Graph μ Ω)‖ ^ 2 := by
  obtain ⟨C, hC, hp⟩ := poincare_H01_of_bounded (μ := μ) hb
  refine ⟨C + 1, by linarith, fun u => ?_⟩
  rw [norm_sq_eq]
  have := hp u u.property
  nlinarith

/-- The gradient map loses no zero-trace function on a bounded domain. -/
theorem gradient_injective (hb : Bornology.IsBounded Ω) :
    Function.Injective (fun u : H01 μ Ω => gradL (u : H1Graph μ Ω)) := by
  intro u v huv
  dsimp only at huv
  obtain ⟨C, _, hp⟩ := graph_norm_sq_le_gradient (μ := μ) hb
  have h := hp (u - v)
  have hg : gradL ((u - v : H01 μ Ω) : H1Graph μ Ω) = 0 := by
    change gradL ((u : H1Graph μ Ω) - (v : H1Graph μ Ω)) = 0
    rw [map_sub, huv, sub_self]
  rw [hg, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at h
  have hz : ((u - v : H01 μ Ω) : H1Graph μ Ω) = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (((u - v : H01 μ Ω) : H1Graph μ Ω))]
  have : u - v = 0 := Subtype.ext hz
  exact sub_eq_zero.mp this

end HitAndRun.Sobolev
