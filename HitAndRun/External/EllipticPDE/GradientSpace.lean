module

public import HitAndRun.External.EllipticPDE.Consumer

/-!
# The zero-trace Sobolev space with its gradient norm

Project-written bridge. We use the closed range of the genuine gradient map,
with its inherited L2 inner product. Injectivity identifies this carrier with
the H01 graph, so the gradient norm is literal rather than an assumed energy.
-/

@[expose] public section

noncomputable section

namespace HitAndRun.Sobolev

open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] (Ω : Set E)

/-- Actual weak gradient of a zero-trace Sobolev graph. -/
def gradientMap : H01 μ Ω →L[ℝ] Lp E 2 (μ.restrict Ω) :=
  gradL.comp (H01 μ Ω).subtypeL

/-- Genuine gradient fields of zero-trace functions, not arbitrary L2 fields. -/
def gradientSpace : Submodule ℝ (Lp E 2 (μ.restrict Ω)) :=
  (gradientMap μ Ω).range

variable {μ Ω}

/-- Bounded-domain Poincare makes the gradient range closed. -/
theorem gradientSpace_closed (hb : Bornology.IsBounded Ω) :
    IsClosed (gradientSpace μ Ω : Set (Lp E 2 (μ.restrict Ω))) := by
  obtain ⟨C, hC, hp⟩ := graph_norm_sq_le_gradient (μ := μ) hb
  have hbound : ∀ u : H01 μ Ω,
      ‖u‖ ≤ (⟨Real.sqrt C, Real.sqrt_nonneg C⟩ : ℝ≥0) * ‖gradientMap μ Ω u‖ := by
    intro u
    change ‖(u : H1Graph μ Ω)‖ ≤ Real.sqrt C * ‖gradL (u : H1Graph μ Ω)‖
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt hC.le] using hp u
  exact ((gradientMap μ Ω).antilipschitz_of_bound hbound).isClosed_range
    (gradientMap μ Ω).uniformContinuous

/-- The gradient-norm carrier is complete, as a closed subspace of L2. -/
theorem gradientSpace_complete (hb : Bornology.IsBounded Ω) :
    CompleteSpace (gradientSpace μ Ω) :=
  (gradientSpace_closed (μ := μ) hb).isComplete.completeSpace_coe

/-- Every gradient-norm element corresponds to exactly one H01 graph. -/
def gradientEquiv (hb : Bornology.IsBounded Ω) : H01 μ Ω ≃ₗ[ℝ] gradientSpace μ Ω :=
  LinearEquiv.ofInjective (gradientMap μ Ω).toLinearMap (gradient_injective hb)

/-- The gradient-space norm is precisely the L2 norm of the weak gradient. -/
theorem gradientEquiv_norm (hb : Bornology.IsBounded Ω) (u : H01 μ Ω) :
    ‖gradientEquiv (μ := μ) hb u‖ = ‖gradL (u : H1Graph μ Ω)‖ := rfl

end HitAndRun.Sobolev
