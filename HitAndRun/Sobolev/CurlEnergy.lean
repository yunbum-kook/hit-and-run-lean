module

public import HitAndRun.Sobolev.CurlEnergyIBP
public import HitAndRun.Sobolev.CurlEnergyAlgebra

/-!
# Divergence/curl energy identity on actual zero-trace vector fields

The curl energy sums only i<j, as in manuscript Lemma B.3. The final theorem
has no cross-term premise: mixed-gradient integration by parts supplies it.
-/

@[expose] public section
noncomputable section

namespace HitAndRun.Sobolev

open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open scoped BigOperators RealInnerProductSpace

variable {n : ℕ} [NeZero n]
variable {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]
  {Ω : Set (EuclideanSpace ℝ (Fin n))}

/-- The j-th weak derivative of the i-th vector component. -/
def weakPartial (u : VectorField μ Ω) (i j : Fin n) : Lp ℝ 2 (μ.restrict Ω) :=
  (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).compLpL 2 (μ.restrict Ω)
    ((u i : gradientSpace μ Ω) : Lp (EuclideanSpace ℝ (Fin n)) 2 (μ.restrict Ω))

/-- Hilbert energy of coordinate projections is the full L2 vector energy. -/
theorem lp_coordinate_energy (g : Lp (EuclideanSpace ℝ (Fin n)) 2 (μ.restrict Ω)) :
    (∑ j : Fin n, ‖(innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).compLpL 2
      (μ.restrict Ω) g‖ ^ 2) = ‖g‖ ^ 2 := by
  let q (j : Fin n) := (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).compLpL 2
    (μ.restrict Ω) g
  change (∑ j, ‖q j‖ ^ 2) = ‖g‖ ^ 2
  simp_rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  rw [← integral_finset_sum Finset.univ (fun j _ => L2.integrable_inner (q j) (q j))]
  apply integral_congr_ae
  have hq : ∀ᵐ x ∂(μ.restrict Ω), ∀ j : Fin n,
      q j x = inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ j) (g x) := by
    rw [ae_all_iff]
    intro j
    exact (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).coeFn_compLpL g
  filter_upwards [hq] with x hx
  simp_rw [hx, real_inner_self_eq_norm_sq]
  exact (EuclideanSpace.basisFun (Fin n) ℝ).sum_sq_norm_inner_right (g x)

/-- The vectorfield norm is exactly the sum of every weak partial's energy. -/
theorem vectorField_energy (u : VectorField μ Ω) :
    ‖u‖ ^ 2 = ∑ i, ∑ j, ‖weakPartial u i j‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  exact (lp_coordinate_energy ((u i : gradientSpace μ Ω) :
    Lp (EuclideanSpace ℝ (Fin n)) 2 (μ.restrict Ω))).symm

/-- Genuine integration by parts supplies the cross terms of the matrix identity. -/
theorem weakPartial_cross (u : VectorField μ Ω) (i j : Fin n) :
    inner ℝ (weakPartial u i i) (weakPartial u j j) =
      inner ℝ (weakPartial u i j) (weakPartial u j i) := by
  rcases (u i).property with ⟨v, hv⟩
  rcases (u j).property with ⟨w, hw⟩
  unfold weakPartial
  rw [← hv, ← hw]
  exact h01_cross v w (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)

/-- Source Lemma B.3: full gradient energy equals divergence plus upper-triangle curl. -/
theorem divergence_curl_energy (u : VectorField μ Ω) :
    ‖u‖ ^ 2 = ‖divergence μ Ω u‖ ^ 2 +
      ∑ i, ∑ j, if i < j then ‖weakPartial u i j - weakPartial u j i‖ ^ 2 else 0 := by
  have h := matrix_curl_energy (weakPartial u) (weakPartial_cross u)
  rw [← vectorField_energy u] at h
  have hd : (∑ i, weakPartial u i i) = divergence μ Ω u := by
    simp only [divergence, sum_apply]
    rfl
  rw [hd] at h
  exact h

end HitAndRun.Sobolev
