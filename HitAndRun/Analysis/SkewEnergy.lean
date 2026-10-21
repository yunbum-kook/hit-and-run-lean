module
public import HitAndRun.Sobolev.CurlEnergyAlgebra

/-! Exact upper-triangle exterior-product algebra for Lemma B.5.
These are algebraic helpers, not a weighted Sobolev estimate. -/
@[expose] public section
namespace HitAndRun.Analysis
open scoped BigOperators
variable {n : ℕ}

/-- Lagrange's identity in the manuscript's upper-triangle convention. -/
theorem upper_wedge_energy (a b : Fin n → ℝ) :
    (∑ i, ∑ j, if i < j then (a j * b i - a i * b j) ^ 2 else 0) =
      (∑ i, a i ^ 2) * (∑ i, b i ^ 2) - (∑ i, a i * b i) ^ 2 := by
  have h := HitAndRun.Sobolev.double_sum_eq_two_upper
    (fun i j => (a j * b i - a i * b j) ^ 2)
    (fun i j => by ring) (fun i => by ring)
  have he : (∑ i, ∑ j, (a j * b i - a i * b j) ^ 2) =
      2 * ((∑ i, a i ^ 2) * (∑ i, b i ^ 2) - (∑ i, a i * b i) ^ 2) := by
    calc
      _ = ∑ i, ∑ j, (a j ^ 2 * b i ^ 2 + a i ^ 2 * b j ^ 2 -
          2 * (a i * b i) * (a j * b j)) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_mul, ← Finset.mul_sum]
        ring
  linarith

/-- The wedge energy is bounded by the product of the two vector energies. -/
theorem upper_wedge_energy_le (a b : Fin n → ℝ) :
    (∑ i, ∑ j, if i < j then (a j * b i - a i * b j) ^ 2 else 0) ≤
      (∑ i, a i ^ 2) * (∑ i, b i ^ 2) := by
  rw [upper_wedge_energy]
  exact sub_le_self _ (sq_nonneg _)

/-- A unit-bounded cutoff gradient gives the exact coefficient needed in B.5. -/
theorem upper_wedge_energy_le_of_energy_le_one (a b : Fin n → ℝ)
    (ha : (∑ i, a i ^ 2) ≤ 1) :
    (∑ i, ∑ j, if i < j then (a j * b i - a i * b j) ^ 2 else 0) ≤
      ∑ i, b i ^ 2 := by
  exact (upper_wedge_energy_le a b).trans
    (mul_le_of_le_one_left (Finset.sum_nonneg (fun i _ => sq_nonneg (b i))) ha)

/-- A symmetric Hessian contracts to zero against an antisymmetric tensor. -/
theorem symmetric_skew_contraction (H G : Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hG : ∀ i j, G i j = -G j i) :
    (∑ i, ∑ j, H i j * G i j) = 0 := by
  have h : (∑ i, ∑ j, H i j * G i j) = -(∑ i, ∑ j, H i j * G i j) := by
    calc
      _ = ∑ j, ∑ i, H i j * G i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -(H j i * G j i) := by
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro i _
        rw [hH i j, hG i j]; ring
      _ = _ := by simp
  linarith

/-- Contracting an antisymmetric tensor reduces exactly to its upper triangle. -/
theorem skew_contraction_upper (a b : Fin n → ℝ) (G : Fin n → Fin n → ℝ)
    (hG : ∀ i j, G i j = -G j i) :
    (∑ i, ∑ j, a j * b i * G i j) =
      ∑ i, ∑ j, if i < j then (a j * b i - a i * b j) * G i j else 0 := by
  have ht : (∑ i, ∑ j, a i * b j * G i j) =
      -(∑ i, ∑ j, a j * b i * G i j) := by
    calc
      _ = ∑ j, ∑ i, a i * b j * G i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -(a i * b j * G j i) := by
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro i _
        rw [hG i j]; ring
      _ = _ := by simp
  have h := HitAndRun.Sobolev.double_sum_eq_two_upper
    (fun i j => (a j * b i - a i * b j) * G i j)
    (fun i j => by rw [hG i j]; ring) (fun i => by ring)
  simp only [sub_mul, Finset.sum_sub_distrib] at h ⊢
  rw [ht] at h
  linarith

/-- Existing finite Cauchy–Schwarz gives the exact squared contraction estimate. -/
theorem skew_contraction_sq_le (a b : Fin n → ℝ) (G : Fin n → Fin n → ℝ)
    (hG : ∀ i j, G i j = -G j i) (ha : (∑ i, a i ^ 2) ≤ 1) :
    (∑ i, ∑ j, a j * b i * G i j) ^ 2 ≤
      (∑ i, b i ^ 2) * (∑ i, ∑ j, if i < j then G i j ^ 2 else 0) := by
  rw [skew_contraction_upper a b G hG]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
    (fun p => a p.2 * b p.1 - a p.1 * b p.2) (fun p => G p.1 p.2)
  simp only [Finset.sum_filter, Fintype.sum_prod_type] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right
    (upper_wedge_energy_le_of_energy_le_one a b ha)
    (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by positivity))))
end HitAndRun.Analysis
