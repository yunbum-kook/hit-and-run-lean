module

public import HitAndRun.External.EllipticPDE.GradientSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Actual coordinate divergence on zero-trace vector fields

The carrier is the finite Hilbert product of actual zero-trace gradient fields.
Its norm is the full gradient energy of the corresponding H01 vector field.
The codomain is initially L2, not the centered subspace: zero mean is a separate
proof obligation and is not assumed in this module.
-/

@[expose] public section

noncomputable section

namespace HitAndRun.Sobolev

open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open scoped BigOperators NNReal

variable {n : ℕ} [NeZero n]
variable (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure] (Ω : Set (EuclideanSpace ℝ (Fin n)))

/-- Each component is a genuine gradient of a zero-trace scalar H01 function. -/
abbrev VectorField := PiLp 2 (fun _ : Fin n => gradientSpace μ Ω)

/-- The i-th coordinate derivative of the i-th vector-field component. -/
def diagonalDerivative (i : Fin n) : VectorField μ Ω →L[ℝ] Lp ℝ 2 (μ.restrict Ω) :=
  ((innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).compLpL 2 (μ.restrict Ω)).comp
    ((gradientSpace μ Ω).subtypeL.comp (PiLp.proj 2 (fun _ : Fin n => gradientSpace μ Ω) i))

/-- Divergence is the actual sum of the diagonal weak partial derivatives. -/
def divergence : VectorField μ Ω →L[ℝ] Lp ℝ 2 (μ.restrict Ω) :=
  ∑ i : Fin n, diagonalDerivative μ Ω i

variable {μ Ω}

omit [NeZero n] in
/-- Coordinate projection has norm at most one. -/
theorem norm_diagonalDerivative_le (i : Fin n) (u : VectorField μ Ω) :
    ‖diagonalDerivative μ Ω i u‖ ≤ ‖u i‖ := by
  have h := ContinuousLinearMap.le_opNorm
    ((innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).compLpL 2 (μ.restrict Ω))
    ((u i : gradientSpace μ Ω) : Lp (EuclideanSpace ℝ (Fin n)) 2 (μ.restrict Ω))
  have hop := (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).norm_compLpL_le
    (p := 2) (μ := μ.restrict Ω)
  have he : ‖EuclideanSpace.basisFun (Fin n) ℝ i‖ = 1 :=
    (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i
  rw [innerSL_apply_norm, he] at hop
  exact h.trans (by simpa using mul_le_mul_of_nonneg_right hop (norm_nonneg ((u i : gradientSpace μ Ω) : Lp (EuclideanSpace ℝ (Fin n)) 2 (μ.restrict Ω))))

omit [NeZero n] in
/-- Exact squared-energy bound for genuine divergence. -/
theorem norm_divergence_sq_le (u : VectorField μ Ω) :
    ‖divergence μ Ω u‖ ^ 2 ≤ (n : ℝ) * ‖u‖ ^ 2 := by
  have ht : ‖divergence μ Ω u‖ ≤ ∑ i : Fin n, ‖u i‖ := by
    calc
      ‖divergence μ Ω u‖ = ‖∑ i : Fin n, diagonalDerivative μ Ω i u‖ := by
        simp [divergence]
      _ ≤ ∑ i : Fin n, ‖diagonalDerivative μ Ω i u‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ‖u i‖ := Finset.sum_le_sum (fun i _ => norm_diagonalDerivative_le i u)
  have hs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => ‖u i‖)
  have hn : 0 ≤ ∑ i : Fin n, ‖u i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hu := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => gradientSpace μ Ω) u
  have ht2 : ‖divergence μ Ω u‖ ^ 2 ≤ (∑ i : Fin n, ‖u i‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hn).2 ht
  simpa only [Finset.card_univ, Fintype.card_fin, ← hu] using ht2.trans hs

omit [NeZero n] in
/-- Source divergence bound, with the exact square-root dimension factor. -/
theorem norm_divergence_le (u : VectorField μ Ω) :
    ‖divergence μ Ω u‖ ≤ Real.sqrt n * ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)] using norm_divergence_sq_le u

end HitAndRun.Sobolev
