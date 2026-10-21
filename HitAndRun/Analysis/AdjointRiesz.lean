import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Abstract Riesz field for a bounded divergence-like map

This is the Hilbert-space part of arXiv:2608.16878v1, Lemma B.2.
The actual Sobolev carrier and its divergence operator are not supplied here.
-/

namespace HitAndRun.Analysis

open scoped InnerProduct

variable {V Q : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]

/-- The adjoint is the unique representing vector, without a nontriviality assumption. -/
theorem existsUnique_riesz_field (D : V →L[ℝ] Q) (f : Q) :
    ∃! u : V, ∀ v : V, inner ℝ f (D v) = inner ℝ u v := by
  refine ⟨D.adjoint f, ?_, ?_⟩
  · intro v
    exact (D.adjoint_inner_left v f).symm
  · intro u hu
    apply ext_inner_right ℝ
    intro v
    exact (hu v).symm.trans (D.adjoint_inner_left v f).symm

/-- Quotients over nonzero vectors appearing in the source's Riesz norm formula. -/
def divergenceDualQuotients (D : V →L[ℝ] Q) (f : Q) : Set ℝ :=
  {r | ∃ v : V, v ≠ 0 ∧ r = inner ℝ f (D v) / ‖v‖}

/-- The norm of the representing field is the least upper bound of the signed quotients.
The zero representing field is handled separately, rather than substituting it for a
nonzero test vector. -/
theorem adjoint_norm_isLUB [Nontrivial V] (D : V →L[ℝ] Q) (f : Q) :
    IsLUB (divergenceDualQuotients D f) ‖D.adjoint f‖ := by
  constructor
  · rintro r ⟨v, hv, rfl⟩
    rw [← D.adjoint_inner_left v f]
    exact (div_le_iff₀ (norm_pos_iff.mpr hv)).mpr
      (real_inner_le_norm (D.adjoint f) v)
  · intro b hb
    by_cases hu : D.adjoint f = 0
    · obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have h := hb (show inner ℝ f (D v) / ‖v‖ ∈ divergenceDualQuotients D f
        from ⟨v, hv, rfl⟩)
      rw [← D.adjoint_inner_left v f, hu] at h
      simpa [hu] using h
    · have h := hb (show inner ℝ f (D (D.adjoint f)) / ‖D.adjoint f‖ ∈
          divergenceDualQuotients D f from ⟨D.adjoint f, hu, rfl⟩)
      rw [← D.adjoint_inner_left (D.adjoint f) f, real_inner_self_eq_norm_sq] at h
      have hn : ‖D.adjoint f‖ ≠ 0 := norm_ne_zero_iff.mpr hu
      simpa [pow_two, hn] using h

/-- Exact nonzero-test-vector supremum formula for the representing field. -/
theorem adjoint_norm_eq_sSup [Nontrivial V] (D : V →L[ℝ] Q) (f : Q) :
    ‖D.adjoint f‖ = sSup (divergenceDualQuotients D f) := by
  apply Eq.symm
  apply (adjoint_norm_isLUB D f).csSup_eq
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact ⟨_, v, hv, rfl⟩

end HitAndRun.Analysis
