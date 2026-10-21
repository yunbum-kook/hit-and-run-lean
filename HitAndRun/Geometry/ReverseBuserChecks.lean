module
import HitAndRun.Geometry.ReverseBuserBody

noncomputable section
open MeasureTheory Set HitAndRun.Sobolev HitAndRun.Geometry
open scoped ENNReal Topology

example : UniversalOrdinaryL1ReverseBuser 256 := universalOrdinaryL1ReverseBuser_256

example (n : ℕ) [NeZero n] (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) :
    ∃ z : ℝ, (∫ x, |f x-z| ∂uniformMeasure K.carrier) ≤
      (256 * Real.sqrt K.poincareConstant.toReal) *
        ∫ x, ‖fderiv ℝ f x‖ ∂uniformMeasure K.carrier :=
  K.ordinaryL1ReverseBuserInput_256 hc f hf

example (n : ℕ) [NeZero n] (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier)
    {r : ℝ} (hr : 0 < r) {a : EuclideanSpace ℝ (Fin n)}
    (hball : Metric.ball a r ⊆ K.carrier)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f) :
    ∃ z : ℝ, (∫ x in K.carrier, |f x-z| ∂K.ambient) ≤
      (1036 * (n : ℝ) * Real.sqrt K.poincareConstant.toReal / r) *
        ∫ x in K.carrier, K.boundaryDistance x * ‖gradient f x‖ ∂K.ambient :=
  reverseBuser_arbitrary_center_1036 K hc hr hball f hf

example (n : ℕ) [NeZero n] (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier)
    {r : ℝ} (hr : 0 < r) {a : EuclideanSpace ℝ (Fin n)}
    (hball : Metric.ball a r ⊆ K.carrier) :
    K.improvedPoincareConstant ≤ ENNReal.ofReal
      (4293184 * (n : ℝ)^2 * K.poincareConstant.toReal / r^2) :=
  reverseBuser_arbitrary_center_IPI_4293184 K hc hr hball

example (n : ℕ) [NeZero n] (K : Set (EuclideanSpace ℝ (Fin n)))
    (hbK : Bornology.IsBounded K) (hi : (interior K).Nonempty) (hc : Convex ℝ K)
    {r : ℝ} (hr : 0 < r) {a : EuclideanSpace ℝ (Fin n)} (hball : Metric.ball a r ⊆ K)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f) :
    ∃ z : ℝ, (∫ x in K, |f x-z|) ≤
      (1036 * (n : ℝ) * Real.sqrt (bodyInteriorDomain K hbK hi).poincareConstant.toReal / r) *
        ∫ x in K, Metric.infDist x (frontier K) * ‖gradient f x‖ :=
  reverseBuser_body_1036 hbK hi hc hr hball f hf

example (n : ℕ) [NeZero n] (K : Set (EuclideanSpace ℝ (Fin n)))
    (hbK : Bornology.IsBounded K) (hi : (interior K).Nonempty) (hc : Convex ℝ K)
    {r : ℝ} (hr : 0 < r) {a : EuclideanSpace ℝ (Fin n)} (hball : Metric.ball a r ⊆ K)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f) :
    (⨅ z : ℝ, ∫ x in K, |f x-z|) ≤
      (1036 * (n : ℝ) * Real.sqrt (bodyInteriorDomain K hbK hi).poincareConstant.toReal / r) *
        ∫ x in K, Metric.infDist x (frontier K) * ‖gradient f x‖ :=
  reverseBuser_body_infimum_1036 hbK hi hc hr hball f hf

example (n : ℕ) [NeZero n] (K : Set (EuclideanSpace ℝ (Fin n)))
    (hbK : Bornology.IsBounded K) (hi : (interior K).Nonempty) (hc : Convex ℝ K) :
    let Ω := bodyInteriorDomain K hbK hi
    let r := sSup {r : ℝ | 0 < r ∧ ∃ c, Metric.ball c r ⊆ K}
    Ω.improvedPoincareConstant ≤ ENNReal.ofReal
      (4293184 * (n : ℝ)^2 * Ω.poincareConstant.toReal / r^2) :=
  reverseBuser_body_maximum_IPI_4293184 hbK hi hc

#print axioms HitAndRun.Geometry.exists_compactC1_eq_near_bounded
#print axioms HitAndRun.Geometry.exists_bounded_lipschitz_eq_near_bounded
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.uniform_guide_concentration
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.uniform_c1_l1_of_bounded_lipschitz
#print axioms HitAndRun.Geometry.cheeger_l1_median_bounded
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.uniformDensity_sinho_logConcave
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.uniform_cheeger_from_actual_poincare
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.ordinaryL1ReverseBuserInput_256
#print axioms HitAndRun.Geometry.universalOrdinaryL1ReverseBuser_256
#print axioms reverseBuser_arbitrary_center_1036
#print axioms reverseBuser_arbitrary_center_IPI_4293184
#print axioms reverseBuser_body_1036
#print axioms reverseBuser_body_infimum_1036
#print axioms reverseBuser_body_maximum_IPI_4293184

-- Print complete exported signatures, including every implicit parameter.
set_option pp.explicit true in
#check @HitAndRun.Geometry.UniversalOrdinaryL1ReverseBuser
set_option pp.explicit true in
#check @HitAndRun.Sobolev.BoundedOpenDomain.ordinaryL1ReverseBuserInput_256
set_option pp.explicit true in
#check @HitAndRun.Geometry.universalOrdinaryL1ReverseBuser_256
set_option pp.explicit true in
#check @HitAndRun.Geometry.reverseBuser_arbitrary_center_1036
set_option pp.explicit true in
#check @HitAndRun.Geometry.reverseBuser_arbitrary_center_IPI_4293184
set_option pp.explicit true in
#check @HitAndRun.Geometry.reverseBuser_body_1036
set_option pp.explicit true in
#check @HitAndRun.Geometry.reverseBuser_body_infimum_1036
set_option pp.explicit true in
#check @HitAndRun.Geometry.reverseBuser_body_maximum_IPI_4293184

-- Display the actual property definitions, not just their names.
#print HitAndRun.Geometry.UniversalOrdinaryL1ReverseBuser
#print HitAndRun.Sobolev.BoundedOpenDomain.OrdinaryL1ReverseBuserInput

-- This definitional consumer rules out a substituted test class or hidden supplier.
example : UniversalOrdinaryL1ReverseBuser 256 =
    (∀ (d : ℕ) [NeZero d] (K : BoundedOpenDomain d), Convex ℝ K.carrier →
      K.poincareConstant < ⊤ →
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 f → ∃ z : ℝ,
        (∫ x, |f x-z| ∂uniformMeasure K.carrier) ≤
          (256 * Real.sqrt K.poincareConstant.toReal) *
            ∫ x, ‖fderiv ℝ f x‖ ∂uniformMeasure K.carrier) := rfl
