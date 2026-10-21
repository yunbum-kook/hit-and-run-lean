module

public import HitAndRun.Sobolev.ResidualDistribution
public import HitAndRun.Sobolev.UniformSource

/-! All three conclusions of source Lemma B.4 for the actual uniform Riesz field. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Analysis
open scoped BigOperators InnerProduct
variable {n : ℕ} [NeZero n]

/-- The unique actual Riesz field fixed by Lemma B.2. -/
def rieszField (K : BoundedOpenDomain n) (f : K.Target) : K.Field :=
  ContinuousLinearMap.adjoint K.div f

theorem rieszField_equation (K : BoundedOpenDomain n) (f : K.Target) (v : K.Field) :
    inner ℝ f (K.div v) = inner ℝ (K.rieszField f) v :=
  (K.div.adjoint_inner_left v f).symm

/-- Source B.4(i),(ii),(iii), all for the same actual residual and Riesz field.
The middle statement is distributional and imposes no classical derivative on f. -/
theorem residual_identities (K : BoundedOpenDomain n) (f : K.Target) :
    meanCLM K.ambient K.carrier (divergenceResidual f (K.rieszField f)) = 0 ∧
    (∀ (φ : testFunctions K.carrier) (i : Fin n),
      (∫ x in K.carrier, divergenceResidual f (K.rieszField f) x *
        fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x (EuclideanSpace.basisFun (Fin n) ℝ i)
          ∂K.ambient) =
        ∑ j : Fin n, ∫ x in K.carrier,
          (weakPartial (K.rieszField f) i j - weakPartial (K.rieszField f) j i) x *
          fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x (EuclideanSpace.basisFun (Fin n) ℝ j)
            ∂K.ambient) ∧
    inner ℝ (divergenceResidual f (K.rieszField f)) (divergence K.ambient K.carrier (K.rieszField f)) =
      ∑ i, ∑ j, if i < j then
        ‖weakPartial (K.rieszField f) i j - weakPartial (K.rieszField f) j i‖ ^ 2 else 0 := by
  refine ⟨divergenceResidual_mean_zero f _, ?_, ?_⟩
  · intro φ i
    exact divergenceResidual_distribution_integral f _ (K.rieszField_equation f) φ i
  · exact divergenceResidual_inner f _ (K.rieszField_equation f)
end HitAndRun.Sobolev.BoundedOpenDomain
