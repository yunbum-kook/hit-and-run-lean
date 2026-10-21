import HitAndRun.Analysis.AdjointRiesz
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Tactic.Linarith

/-! Exact quantitative Hilbert duality underlying Lemma B.1.
No Sobolev realization or paper endpoint is claimed. -/
namespace HitAndRun.Analysis
open scoped InnerProduct
variable {V Q : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]

private theorem energy_algebra {a b c C : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b)
    (_hc : 0 ≤ c) (hC : 0 ≤ C) (h : a ^ 2 ≤ b * c)
    (hc' : c ^ 2 ≤ C * a ^ 2) : a ^ 2 ≤ C * b ^ 2 := by
  have hs : (a ^ 2) ^ 2 ≤ (b * c) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg a) h 2
  have ht := mul_le_mul_of_nonneg_left hc' (sq_nonneg b)
  by_cases hz : a = 0
  · simp [hz, mul_nonneg hC (sq_nonneg b)]
  · have hp : 0 < a ^ 2 := sq_pos_of_ne_zero hz
    nlinarith

/-- Witness energy control implies the adjoint lower bound, with the same C. -/
theorem adjoint_lower_bound_of_right_inverse_bound (D : V →L[ℝ] Q) {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ f : Q, ∃ v : V, D v = f ∧ ‖v‖ ^ 2 ≤ C * ‖f‖ ^ 2) :
    ∀ f : Q, ‖f‖ ^ 2 ≤ C * ‖D.adjoint f‖ ^ 2 := by
  intro f
  obtain ⟨v, hv, hnorm⟩ := h f
  have hi : ‖f‖ ^ 2 ≤ ‖D.adjoint f‖ * ‖v‖ := by
    calc
      ‖f‖ ^ 2 = inner ℝ (D.adjoint f) v := by
        rw [D.adjoint_inner_left, hv, real_inner_self_eq_norm_sq]
      _ ≤ _ := real_inner_le_norm _ _
  exact energy_algebra (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hC hi hnorm

/-- An adjoint lower bound yields actual preimages with the exact energy constant.
Surjectivity is obtained from Mathlib's Lax–Milgram theorem, not assumed. -/
theorem right_inverse_bound_of_adjoint_lower_bound (D : V →L[ℝ] Q) {C : ℝ}
    (hC : 0 < C) (h : ∀ f : Q, ‖f‖ ^ 2 ≤ C * ‖D.adjoint f‖ ^ 2) :
    ∀ f : Q, ∃ v : V, D v = f ∧ ‖v‖ ^ 2 ≤ C * ‖f‖ ^ 2 := by
  let B : Q →L[ℝ] Q →L[ℝ] ℝ := (innerSL ℝ).comp (D.comp D.adjoint)
  have hB : IsCoercive B := by
    refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
    intro f
    change C⁻¹ * ‖f‖ * ‖f‖ ≤ inner ℝ (D (D.adjoint f)) f
    rw [← D.adjoint_inner_right, real_inner_self_eq_norm_sq]
    have hh : ‖f‖ ^ 2 / C ≤ ‖D.adjoint f‖ ^ 2 := (div_le_iff₀ hC).mpr (by simpa [mul_comm] using h f)
    simpa only [div_eq_mul_inv, pow_two, mul_assoc, mul_comm, mul_left_comm] using hh
  intro f
  let g := hB.continuousLinearEquivOfBilin.symm f
  have hg : D (D.adjoint g) = f := by
    apply ext_inner_right ℝ
    intro w
    have hw := hB.continuousLinearEquivOfBilin_apply g w
    have he : hB.continuousLinearEquivOfBilin g = f :=
      hB.continuousLinearEquivOfBilin.apply_symm_apply f
    rw [he] at hw
    exact hw.symm
  refine ⟨D.adjoint g, hg, ?_⟩
  have hi : ‖D.adjoint g‖ ^ 2 ≤ ‖f‖ * ‖g‖ := by
    calc
      ‖D.adjoint g‖ ^ 2 = inner ℝ f g := by
        rw [← hg, ← D.adjoint_inner_right, real_inner_self_eq_norm_sq]
      _ ≤ _ := real_inner_le_norm _ _
  exact energy_algebra (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hC.le hi (h g)

/-- Exact squared-constant duality, including zero vectors and trivial spaces (the constant C remains positive). -/
theorem right_inverse_bound_iff_adjoint_lower_bound (D : V →L[ℝ] Q) {C : ℝ}
    (hC : 0 < C) :
    (∀ f : Q, ∃ v : V, D v = f ∧ ‖v‖ ^ 2 ≤ C * ‖f‖ ^ 2) ↔
      (∀ f : Q, ‖f‖ ^ 2 ≤ C * ‖D.adjoint f‖ ^ 2) :=
  ⟨adjoint_lower_bound_of_right_inverse_bound D hC.le,
    right_inverse_bound_of_adjoint_lower_bound D hC⟩

/-- Lemma B.1's exact nonzero-test-vector supremum formulation. -/
theorem right_inverse_bound_iff_dual_sup [Nontrivial V] (D : V →L[ℝ] Q)
    {C : ℝ} (hC : 0 < C) :
    (∀ f : Q, ∃ v : V, D v = f ∧ ‖v‖ ^ 2 ≤ C * ‖f‖ ^ 2) ↔
      (∀ f : Q, ‖f‖ ^ 2 ≤ C * (sSup (divergenceDualQuotients D f)) ^ 2) := by
  simpa only [← adjoint_norm_eq_sSup] using
    right_inverse_bound_iff_adjoint_lower_bound D hC
end HitAndRun.Analysis
