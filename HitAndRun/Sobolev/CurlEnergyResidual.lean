module

public import HitAndRun.Sobolev.CurlEnergy

/-!
# Algebraic residual consequences of the actual Riesz equation

This gives parts(i) and(iii) of source LemmaB.4. The distributional part(ii)
is separate and is not claimed by this file.
-/

@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

variable {n : ℕ} [NeZero n]
variable {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]
  {Ω : Set (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure (μ.restrict Ω)]

/-- The source residual is an actual L2 function, f minus weak divergence. -/
def divergenceResidual (f : centeredL2 (μ := μ) (Ω := Ω)) (u : VectorField μ Ω) :
    Lp ℝ 2 (μ.restrict Ω) := (f : Lp ℝ 2 (μ.restrict Ω)) - divergence μ Ω u

/-- LemmaB.4(i): both terms have actual mean zero. -/
theorem divergenceResidual_mean_zero (f : centeredL2 (μ := μ) (Ω := Ω))
    (u : VectorField μ Ω) : meanCLM μ Ω (divergenceResidual f u) = 0 := by
  rw [divergenceResidual, map_sub, divergence_mean_zero, sub_zero]
  exact f.property

/-- LemmaB.4(iii): the Riesz equation and proved curl energy determine the pairing. -/
theorem divergenceResidual_inner (f : centeredL2 (μ := μ) (Ω := Ω))
    (u : VectorField μ Ω)
    (hu : ∀ v : VectorField μ Ω, inner ℝ f (centeredDivergence v) = inner ℝ u v) :
    inner ℝ (divergenceResidual f u) (divergence μ Ω u) =
      ∑ i, ∑ j, if i < j then ‖weakPartial u i j - weakPartial u j i‖ ^ 2 else 0 := by
  have h := hu u
  change inner ℝ (f : Lp ℝ 2 (μ.restrict Ω)) (divergence μ Ω u) = inner ℝ u u at h
  rw [divergenceResidual, inner_sub_left, h, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  have he := divergence_curl_energy u
  linarith

end HitAndRun.Sobolev
