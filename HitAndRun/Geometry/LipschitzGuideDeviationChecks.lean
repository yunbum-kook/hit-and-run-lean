module
public import HitAndRun.Geometry.LipschitzGuideDeviation
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory HitAndRun.Sobolev
open scoped ENNReal
variable {n : ℕ} [NeZero n]
example (K : BoundedOpenDomain n) (hfin : K.poincareConstant < ⊤)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : LipschitzWith 1 u) :
    variance u (uniformMeasure K.carrier) ≤ K.poincareConstant.toReal :=
  K.lipschitz_guide_variance_le hfin u hu
example (K : BoundedOpenDomain n) (hfin : K.poincareConstant < ⊤)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : LipschitzWith 1 u) :
    (∫ x, |u x - ∫ y, u y ∂uniformMeasure K.carrier| ∂uniformMeasure K.carrier) ≤
      Real.sqrt K.poincareConstant.toReal :=
  K.lipschitz_guide_mean_deviation_le hfin u hu
#print axioms BoundedOpenDomain.lipschitz_guide_variance_le
#print axioms BoundedOpenDomain.lipschitz_guide_mean_deviation_le
