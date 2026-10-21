module
public import HitAndRun.Geometry.WeightedPoincareConditionalSource
public import HitAndRun.Geometry.ConvexBodyInradiusBoundary
public import HitAndRun.Sobolev.TranslationConstants
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set HitAndRun.Sobolev
open scoped ENNReal Topology

/-- Explicit missing universal reverse-Buser input, uniform across all dimensions
and convex domains. This definition does not assert that such a constant exists. -/
def UniversalOrdinaryL1ReverseBuser (b : ℝ) : Prop :=
  ∀ (d : ℕ) [NeZero d] (K : BoundedOpenDomain d), Convex ℝ K.carrier →
    K.poincareConstant < ⊤ → K.OrdinaryL1ReverseBuserInput b

variable {n : ℕ} [NeZero n]

theorem conditional_reverseBuser_arbitrary_center (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) (hfin : K.poincareConstant < ⊤)
    {b r : ℝ} (hb : 0 ≤ b) (hr : 0 < r) {a : EuclideanSpace ℝ (Fin n)}
    (hball : Metric.ball a r ⊆ K.carrier) (hRB : UniversalOrdinaryL1ReverseBuser b)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f) :
    ∃ z : ℝ, (∫ x in K.carrier, |f x-z| ∂K.ambient) ≤
      ((12+4*b)*(n : ℝ)*Real.sqrt K.poincareConstant.toReal/r) *
        ∫ x in K.carrier, K.boundaryDistance x * ‖gradient f x‖ ∂K.ambient := by
  let L := K.translate (-a)
  have hLc : Convex ℝ L.carrier := hc.vadd (-a)
  have hLf : L.poincareConstant < ⊤ := by simpa only [L, K.poincareConstant_translate] using hfin
  have hfl : LocallyLipschitz (fun x => f (a+x)) :=
    hf.comp (isometry_add_left a).lipschitz.locallyLipschitz
  obtain ⟨z, hz⟩ := L.conditional_reverseBuser_locallyLipschitz hLc hLf hb hr
    (K.translate_neg_inner_ball hball) (hRB n L hLc hLf) (fun x => f (a+x)) hfl
  have hl : (∫ x in L.carrier, |f (a+x)-z| ∂L.ambient) =
      ∫ x in K.carrier, |f x-z| ∂K.ambient := by
    rw [← K.translate_integral (-a) (fun x => |f (a+x)-z|)]
    simp
  have hg : (∫ x in L.carrier, L.boundaryDistance x * ‖gradient (fun y => f (a+y)) x‖ ∂L.ambient) =
      ∫ x in K.carrier, K.boundaryDistance x * ‖gradient f x‖ ∂K.ambient := by
    rw [← K.translate_integral (-a)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp [L, K.translate_boundaryDistance, gradient, fderiv_comp_add_left]
  rw [hl, hg] at hz
  refine ⟨z, ?_⟩
  simpa only [L, K.poincareConstant_translate] using hz

theorem conditional_reverseBuser_arbitrary_center_IPI (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) (hfin : K.poincareConstant < ⊤)
    {b r : ℝ} (hb : 0 ≤ b) (hr : 0 < r) {a : EuclideanSpace ℝ (Fin n)}
    (hball : Metric.ball a r ⊆ K.carrier) (hRB : UniversalOrdinaryL1ReverseBuser b) :
    K.improvedPoincareConstant ≤ ENNReal.ofReal
      (4 * (((12+4*b)*(n : ℝ)*Real.sqrt K.poincareConstant.toReal/r)^2)) := by
  have hLc : Convex ℝ (K.translate (-a)).carrier := hc.vadd (-a)
  have hLf : (K.translate (-a)).poincareConstant < ⊤ := by
    simpa only [K.poincareConstant_translate] using hfin
  have h := (K.translate (-a)).conditional_reverseBuser_IPI hLc hLf hb hr
    (K.translate_neg_inner_ball hball) (hRB n (K.translate (-a)) hLc hLf)
  simpa only [K.poincareConstant_translate, K.improvedPoincareConstant_translate] using h
end HitAndRun.Geometry
