import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Minimum-norm preimages

Abstract attainment used in arXiv:2608.16878v1 Lemma 1.3. This file does
not construct the actual Sobolev divergence operator or its feasibility.
-/

namespace HitAndRun.Analysis

variable {V Q : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- A nonempty fiber of a bounded linear map on a real Hilbert space has a
minimum-norm preimage. -/
theorem exists_minimum_norm_preimage (D : V →L[ℝ] Q) (f : Q)
    (hf : ∃ v : V, D v = f) :
    ∃ u : V, D u = f ∧ ∀ v : V, D v = f → ‖u‖ ≤ ‖v‖ := by
  let K : Set V := D ⁻¹' {f}
  have hne : K.Nonempty := hf
  have hclosed : IsClosed K := isClosed_singleton.preimage D.continuous
  have hconvex : Convex ℝ K := (convex_singleton f).linear_preimage D.toLinearMap
  obtain ⟨u, hu, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    hne hclosed.isComplete hconvex (0 : V)
  refine ⟨u, hu, ?_⟩
  intro v hv
  have hinf : (⨅ w : K, ‖(0 : V) - w‖) ≤ ‖(0 : V) - v‖ :=
    ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ (⟨v, hv⟩ : K)
  simpa using hmin.le.trans hinf

/-- The squared norm infimum is attained as well, with a nonempty fiber
explicitly supplied to avoid an empty-infimum convention. -/
theorem exists_minimum_energy_preimage (D : V →L[ℝ] Q) (f : Q)
    (hf : ∃ v : V, D v = f) :
    ∃ u : V, D u = f ∧ ∀ v : V, D v = f → ‖u‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  obtain ⟨u, hu, hmin⟩ := exists_minimum_norm_preimage D f hf
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact pow_le_pow_left₀ (norm_nonneg u) (hmin v hv) 2

end HitAndRun.Analysis
