import HitAndRun.Sobolev.TranslationConstants
open MeasureTheory ProbabilityTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Sobolev Set
open scoped ENNReal
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (c : EuclideanSpace ℝ (Fin n))
example : (K.translate c).poincareConstant = K.poincareConstant := K.poincareConstant_translate c
example : (K.translate c).improvedPoincareConstant = K.improvedPoincareConstant :=
  K.improvedPoincareConstant_translate c
example (u : (K.translate c).H1) : K.translationGraph c u.val ∈ W12 K.ambient K.carrier :=
  K.translationGraph_mem_W12 c u
example (x : EuclideanSpace ℝ (Fin n)) :
    (K.translate c).boundaryDistance (c + x) = K.boundaryDistance x :=
  K.translate_boundaryDistance c x
example {a : EuclideanSpace ℝ (Fin n)} {r : ℝ} (h : Metric.ball a r ⊆ K.carrier) :
    Metric.ball 0 r ⊆ (K.translate (-a)).carrier := K.translate_neg_inner_ball h
example (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x in K.carrier, f x) = (volume K.carrier).toReal *
      ∫ x, f x ∂K.ambient.restrict K.carrier := K.integral_volume_eq_uniform f
#print axioms BoundedOpenDomain.translate_volume
#print axioms BoundedOpenDomain.translate_measurePreserving
#print axioms BoundedOpenDomain.translate_boundaryDistance
#print axioms BoundedOpenDomain.translate_variance
#print axioms BoundedOpenDomain.integral_uniform_eq_volume
#print axioms BoundedOpenDomain.integral_volume_eq_uniform
#print axioms BoundedOpenDomain.translate_neg_inner_ball
#print axioms BoundedOpenDomain.translationGraph_mem_W12
#print axioms BoundedOpenDomain.translationH1_variance
#print axioms BoundedOpenDomain.translationH1_gradientEnergy
#print axioms BoundedOpenDomain.translationH1_weightedGradientEnergy
#print axioms BoundedOpenDomain.poincareConstant_translate
#print axioms BoundedOpenDomain.improvedPoincareConstant_translate
