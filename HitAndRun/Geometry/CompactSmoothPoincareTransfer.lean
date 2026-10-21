module
public import HitAndRun.Geometry.ConvexPoincareFiniteDensity
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every global smooth function can be localized without changing its germ anywhere
on a bounded closure. The compact support is supplied by an actual smooth bump. -/
theorem exists_compactSmooth_eq_near_bounded {K : Set E} (hb : Bornology.IsBounded K)
    (f : E → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∃ g : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      ∀ x ∈ closure K, g =ᶠ[𝓝 x] f := by
  obtain ⟨R, hR, hnorm⟩ := hb.closure.exists_pos_norm_le
  let χ : ContDiffBump (0 : E) :=
    { rIn := R+1, rOut := R+2, rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  refine ⟨fun x => χ x * f x, χ.contDiff.mul hf, χ.hasCompactSupport.mul_right, ?_⟩
  intro x hx
  have hin : x ∈ Metric.ball (0 : E) χ.rIn := by
    change dist x 0 < R+1
    rw [dist_zero_right]
    linarith [hnorm x hx]
  filter_upwards [χ.eventuallyEq_one_of_mem_ball hin] with y hy
  change χ y = 1 at hy
  simp only [hy, one_mul]

end HitAndRun.Geometry

namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
variable {n : ℕ} [NeZero n]

/-- External compact-C∞ PI input, stated only for the actual normalized uniform
measure. This definition makes no assertion that a named external theorem applies. -/
def CompactSmoothPoincareBound (K : BoundedOpenDomain n) (C : ℝ) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
    variance f (K.ambient.restrict K.carrier) ≤
      C * ∫ x in K.carrier, ‖fderiv ℝ f x‖^2 ∂K.ambient

/-- Compact ambient tests suffice for every global smooth test on a bounded domain,
because one cutoff preserves both function and derivative on the entire domain. -/
theorem CompactSmoothPoincareBound.smooth_bound {K : BoundedOpenDomain n} {C : ℝ}
    (h : K.CompactSmoothPoincareBound C)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    variance f (K.ambient.restrict K.carrier) ≤
      C * ∫ x in K.carrier, ‖fderiv ℝ f x‖^2 ∂K.ambient := by
  obtain ⟨g, hg, hgc, heq⟩ := Geometry.exists_compactSmooth_eq_near_bounded K.isBounded f hf
  have hae : g =ᵐ[K.ambient.restrict K.carrier] f :=
    (ae_restrict_mem K.isOpen.measurableSet).mono fun x hx =>
      (heq x (subset_closure hx)).eq_of_nhds
  have hderiv : (fun x => ‖fderiv ℝ g x‖^2) =ᵐ[K.ambient.restrict K.carrier]
      (fun x => ‖fderiv ℝ f x‖^2) :=
    (ae_restrict_mem K.isOpen.measurableSet).mono fun x hx => by
      change ‖fderiv ℝ g x‖^2 = ‖fderiv ℝ f x‖^2
      rw [(heq x (subset_closure hx)).fderiv_eq (𝕜 := ℝ)]
  simpa only [variance_congr hae, integral_congr_ae hderiv] using h g hg hgc

/-- Compact ambient C∞ PI input extends to the actual genuine W12 space, using
proved smooth density rather than assuming compactly supported approximants. -/
theorem CompactSmoothPoincareBound.isPoincareConstant_of_inner_ball
    {K : BoundedOpenDomain n} {C : ℝ} (h : K.CompactSmoothPoincareBound C)
    (hC : 0 ≤ C) (hc : Convex ℝ K.carrier) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ K.carrier) :
    K.IsPoincareConstant (ENNReal.ofReal C) :=
  K.isPoincareConstant_of_smooth_bound hc hr hball hC h.smooth_bound

/-- The actual least CPI inherits the same external compact-test constant. -/
theorem CompactSmoothPoincareBound.poincareConstant_le_of_inner_ball
    {K : BoundedOpenDomain n} {C : ℝ} (h : K.CompactSmoothPoincareBound C)
    (hC : 0 ≤ C) (hc : Convex ℝ K.carrier) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ K.carrier) :
    K.poincareConstant ≤ ENNReal.ofReal C :=
  K.poincareConstant_le (h.isPoincareConstant_of_inner_ball hC hc hr hball)

end HitAndRun.Sobolev.BoundedOpenDomain
