module
/-
Project-written bridge composing actual hit-and-run definitions and proved
source endpoints. External CvxBody provenance: chewisinho/cvx_body_lean,
commit 41678c03373f8d3ac9d95bab31bcc17022d85bec (private repository).
This staging file does not grant public redistribution permission.
-/
public import HitAndRun.Geometry.LipschitzGuideDeviation
public import HitAndRun.Geometry.UniformConvexDensity
public import HitAndRun.Geometry.ConvexPoincareFinite
public import HitAndRun.Geometry.WeightedPoincareBodySource
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Localize actual ambient C1 functions, preserving every germ on the bounded closure. -/
theorem exists_compactC1_eq_near_bounded {K : Set E} (hb : Bornology.IsBounded K)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) :
    ∃ g : E → ℝ, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧
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

/-- The localized ambient function is globally bounded and globally Lipschitz. -/
theorem exists_bounded_lipschitz_eq_near_bounded {K : Set E} (hb : Bornology.IsBounded K)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) :
    ∃ (g : E → ℝ) (L : ℝ≥0) (M : ℝ), LipschitzWith L g ∧
      (∀ x, |g x| ≤ M) ∧ ∀ x ∈ closure K, g =ᶠ[𝓝 x] f := by
  obtain ⟨g, hg, hgc, heq⟩ := exists_compactC1_eq_near_bounded hb f hf
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  exact ⟨g, L, M, hL, fun x => by simpa only [Real.norm_eq_abs] using hM x, heq⟩
end HitAndRun.Geometry

namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory ProbabilityTheory Set Filter EllipticPdes
open scoped Topology NNReal ENNReal
variable {n : ℕ} [NeZero n]

/-- Integrability of genuine ambient Lipschitz guide functions on the actual uniform measure. -/
theorem uniform_integrable_lipschitz (K : BoundedOpenDomain n)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) {L : ℝ≥0} (hu : LipschitzWith L u) :
    Integrable u (uniformMeasure K.carrier) := by
  rw [← K.measure_eq_uniform]
  exact (continuous_memLp_bounded_restrict K.isBounded K.isOpen.measurableSet
    hu.continuous).integrable (by norm_num)

/-- Genuine finite positive concentration scale furnished by the actual optimal CPI. -/
theorem uniform_guide_concentration (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) :
    0 < Real.sqrt K.poincareConstant.toReal ∧
      ∀ u : EuclideanSpace ℝ (Fin n) → ℝ, LipschitzWith 1 u →
        Integrable u (uniformMeasure K.carrier) ∧
          (∫ x, |u x - ∫ y, u y ∂uniformMeasure K.carrier| ∂uniformMeasure K.carrier) ≤
            Real.sqrt K.poincareConstant.toReal := by
  refine ⟨Real.sqrt_pos.2 (K.poincareConstant_toReal_pos_convex hc), fun u hu => ?_⟩
  exact ⟨K.uniform_integrable_lipschitz u hu,
    K.lipschitz_guide_mean_deviation_le (K.poincareConstant_lt_top_convex hc) u hu⟩
/-- A genuine local-to-global transfer: the ambient C1 test class is preserved. -/
theorem uniform_c1_l1_of_bounded_lipschitz (K : BoundedOpenDomain n) {C : ℝ}
    (h : ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ≥0) (M : ℝ),
      LipschitzWith L g → (∀ x, |g x| ≤ M) → ∃ z : ℝ,
        (∫ x, |g x-z| ∂uniformMeasure K.carrier) ≤
          C * ∫ x, ‖fderiv ℝ g x‖ ∂uniformMeasure K.carrier)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) :
    ∃ z : ℝ, (∫ x, |f x-z| ∂uniformMeasure K.carrier) ≤
      C * ∫ x, ‖fderiv ℝ f x‖ ∂uniformMeasure K.carrier := by
  obtain ⟨g, L, M, hL, hM, heq⟩ :=
    Geometry.exists_bounded_lipschitz_eq_near_bounded K.isBounded f hf
  obtain ⟨z, hz⟩ := h g L M hL hM
  have hae : g =ᵐ[uniformMeasure K.carrier] f := by
    rw [← K.measure_eq_uniform]
    exact (ae_restrict_mem K.isOpen.measurableSet).mono fun x hx =>
      (heq x (subset_closure hx)).eq_of_nhds
  have hderiv : (fun x => ‖fderiv ℝ g x‖) =ᵐ[uniformMeasure K.carrier]
      (fun x => ‖fderiv ℝ f x‖) := by
    rw [← K.measure_eq_uniform]
    exact (ae_restrict_mem K.isOpen.measurableSet).mono fun x hx => by
      change ‖fderiv ℝ g x‖ = ‖fderiv ℝ f x‖
      rw [(heq x (subset_closure hx)).fderiv_eq (𝕜 := ℝ)]
  refine ⟨z, ?_⟩
  rw [integral_congr_ae (hae.mono fun x hx => by rw [hx]),
    integral_congr_ae hderiv] at hz
  exact hz
end HitAndRun.Sobolev.BoundedOpenDomain
