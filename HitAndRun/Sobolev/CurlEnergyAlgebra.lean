module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

/-!
# Upper-triangle curl energy algebra

A helper identity only: the cross-inner-product hypothesis is discharged by
actual H01 integration by parts in the source-facing theorem.
-/

@[expose] public section
namespace HitAndRun.Sobolev

open scoped BigOperators RealInnerProductSpace

variable {n : ℕ}

/-- Sum a symmetric, zero-diagonal matrix once per unordered pair. -/
theorem double_sum_eq_two_upper (f : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = 2 * ∑ i, ∑ j, if i < j then f i j else 0 := by
  have hp (i j : Fin n) : f i j =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j; simp [hdiag]
    · simp [h, not_lt_of_gt h, hsym i j]
  have hswap : (∑ i, ∑ j, if j < i then f j i else 0) =
      ∑ i, ∑ j, if i < j then f i j else 0 := Finset.sum_comm
  calc
    (∑ i, ∑ j, f i j) = ∑ i, ∑ j,
        ((if i < j then f i j else 0) + (if j < i then f j i else 0)) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      exact hp i j
    _ = 2 * ∑ i, ∑ j, if i < j then f i j else 0 := by
      simp only [Finset.sum_add_distrib, hswap]
      ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Exact upper-triangle energy identity, with cross terms exposed as a helper premise. -/
theorem matrix_curl_energy (A : Fin n → Fin n → H)
    (hcross : ∀ i j, inner ℝ (A i i) (A j j) = inner ℝ (A i j) (A j i)) :
    (∑ i, ∑ j, ‖A i j‖ ^ 2) = ‖∑ i, A i i‖ ^ 2 +
      ∑ i, ∑ j, if i < j then ‖A i j - A j i‖ ^ 2 else 0 := by
  have hd : ‖∑ i, A i i‖ ^ 2 = ∑ i, ∑ j, inner ℝ (A i j) (A j i) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    exact (real_inner_comm _ _).trans (hcross i j)
  have ht : (∑ i, ∑ j, ‖A j i‖ ^ 2) = ∑ i, ∑ j, ‖A i j‖ ^ 2 := Finset.sum_comm
  have he : (∑ i, ∑ j, ‖A i j - A j i‖ ^ 2) =
      2 * (∑ i, ∑ j, ‖A i j‖ ^ 2) - 2 * ‖∑ i, A i i‖ ^ 2 := by
    simp_rw [norm_sub_sq_real]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [ht, ← hd]
    ring
  have hu := double_sum_eq_two_upper (fun i j => ‖A i j - A j i‖ ^ 2)
    (fun i j => by rw [norm_sub_rev]) (fun i => by simp)
  nlinarith

end HitAndRun.Sobolev
