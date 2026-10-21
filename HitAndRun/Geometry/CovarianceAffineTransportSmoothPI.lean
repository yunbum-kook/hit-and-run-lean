module
public import HitAndRun.Geometry.ConvexPoincareFiniteDensity
public import HitAndRun.Sobolev.TranslationConstants
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory ProbabilityTheory
variable {n : ℕ} [NeZero n]

/-- The generic smooth-to-W12 PI transfer on arbitrary bounded open convex domains. -/
theorem isPoincareConstant_of_smooth_bound_convex (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f →
      variance f (K.ambient.restrict K.carrier) ≤
        C * ∫ x in K.carrier, ‖fderiv ℝ f x‖ ^ 2 ∂K.ambient) :
    K.IsPoincareConstant (ENNReal.ofReal C) := by
  obtain ⟨a, ha⟩ := K.nonempty
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp K.isOpen a ha
  have ht : (K.translate (-a)).IsPoincareConstant (ENNReal.ofReal C) := by
    apply (K.translate (-a)).isPoincareConstant_of_smooth_bound (hc.translate (-a)) hr
      (K.translate_neg_inner_ball hball) hC
    intro f hf
    let g : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f (-a + x)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp (contDiff_const.add contDiff_id)
    have h := hbound g hg
    have hv := K.translate_variance (-a) f hf.continuous.measurable.aemeasurable
    change variance g _ = _ at hv
    rw [hv] at h
    have hd (x : EuclideanSpace ℝ (Fin n)) :
        fderiv ℝ g x = fderiv ℝ f (-a + x) := by
      have hfd := (hf.differentiable (by simp) (-a + x)).hasFDerivAt.comp
        x ((hasFDerivAt_id x).const_add (-a))
      simpa [g, Function.comp_def] using hfd.fderiv
    simpa only [hd, K.translate_integral (-a) (fun x => ‖fderiv ℝ f x‖^2)] using h
  exact (K.isPoincareConstant_translate_iff (-a) _).mp ht
end HitAndRun.Sobolev.BoundedOpenDomain
