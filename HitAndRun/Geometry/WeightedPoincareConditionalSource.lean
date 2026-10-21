module
public import HitAndRun.Geometry.WeightedPoincareAssembly
public import HitAndRun.Geometry.WeightedPoincareCoefficient
public import HitAndRun.Geometry.ConvexCovarianceRadius
public import HitAndRun.Geometry.MedianWeightedBridge
public import HitAndRun.Geometry.WeightedPoincareLipschitzExtension
public import HitAndRun.Sobolev.WeightedPoincareTransferSource
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory Set HitAndRun.Geometry
open scoped ENNReal Topology
variable {n : ℕ} [NeZero n]

/-- The sole analytic premise still missing from the reverse-Buser route.
This is an explicit property, not an established theorem for convex bodies. -/
def OrdinaryL1ReverseBuserInput (K : BoundedOpenDomain n) (b : ℝ) : Prop :=
  ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 g → ∃ z : ℝ,
    (∫ x, |g x-z| ∂uniformMeasure K.carrier) ≤
      (b * Real.sqrt K.poincareConstant.toReal) *
        ∫ x, ‖fderiv ℝ g x‖ ∂uniformMeasure K.carrier

/-- Explicitly conditional S07 assembly, with the actual Poincare radius bound.
The reverse-Buser premise is not discharged here. -/
theorem conditional_reverseBuser_weighted_center (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) (hfin : K.poincareConstant < ⊤)
    {b r : ℝ} (hb : 0 ≤ b) (hr : 0 < r) (hball : Metric.ball 0 r ⊆ K.carrier)
    (hRB : K.OrdinaryL1ReverseBuserInput b)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) :
    ∃ z : ℝ, (∫ x in K.carrier, |f x-z| ∂K.ambient) ≤
      ((12 + 4*b) * (n : ℝ) * Real.sqrt K.poincareConstant.toReal / r) *
        ∫ x in K.carrier, K.boundaryDistance x * ‖fderiv ℝ f x‖ ∂K.ambient := by
  let a : ℝ := 1 - 1 / (2 * (n : ℝ))
  let R : ℝ := 6 * (n : ℝ) * Real.sqrt K.poincareConstant.toReal
  let B : ℝ := b * Real.sqrt K.poincareConstant.toReal
  have hn : 0 < n := NeZero.pos n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ha0 : 0 < a := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h : 1 / (2 * (n : ℝ)) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    dsimp [a]; linarith
  have ha1 : a < 1 := by
    dsimp [a]
    exact sub_lt_self _ (by positivity)
  have hB : 0 ≤ B := mul_nonneg hb (Real.sqrt_nonneg _)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hfront : (frontier K.carrier).Nonempty := nonempty_frontier_iff.mpr
    ⟨K.nonempty, fun h => NormedSpace.unbounded_univ ℝ _ (h ▸ K.isBounded)⟩
  have hz0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ K.carrier := hball (Metric.mem_ball_self hr)
  have hordinary : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 g → ∃ z : ℝ,
      (∫ x in K.carrier, ‖g x-z‖ ∂K.ambient) ≤
        B * ∫ x in K.carrier, ‖fderiv ℝ g x‖ ∂K.ambient := by
    intro g hg
    simpa only [K.measure_eq_uniform, Real.norm_eq_abs, B] using hRB g hg
  obtain ⟨z, hz⟩ := exists_weighted_center_of_ordinaryL1 K.ambient K.isBounded hc K.isOpen
    hfront hr hball ha0 ha1 hB (fun x hx => K.norm_le_poincare_radius hc hz0 hfin hx) hordinary f hf
  have hcoef := radial_assembly_coefficient_le n hn hR hB hr
  have hcoef' : R * (a ^ n)⁻¹ / r + B * a * (a ^ n)⁻¹ / ((1-a)*r) ≤
      (12 + 4*b) * (n : ℝ) * Real.sqrt K.poincareConstant.toReal / r := by
    convert hcoef using 1 <;> dsimp [R, B] <;> ring
  refine ⟨z, ?_⟩
  have hi : 0 ≤ ∫ x in K.carrier, K.boundaryDistance x * ‖fderiv ℝ f x‖ ∂K.ambient :=
    integral_nonneg fun x => mul_nonneg Metric.infDist_nonneg (norm_nonneg _)
  have hz' : (∫ x in K.carrier, |f x-z| ∂K.ambient) ≤
      (R * (a ^ n)⁻¹ / r + B * a * (a ^ n)⁻¹ / ((1-a)*r)) *
        ∫ x in K.carrier, K.boundaryDistance x * ‖fderiv ℝ f x‖ ∂K.ambient := by
    simpa only [Real.norm_eq_abs, finrank_euclideanSpace_fin, boundaryDistance] using hz
  exact hz'.trans (mul_le_mul_of_nonneg_right hcoef' hi)

/-- Conditional exact median-zero interface needed by the proved S08 transfer. -/
theorem conditional_reverseBuser_C1WeightedL1 (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) (hfin : K.poincareConstant < ⊤)
    {b r : ℝ} (hb : 0 ≤ b) (hr : 0 < r) (hball : Metric.ball 0 r ⊆ K.carrier)
    (hRB : K.OrdinaryL1ReverseBuserInput b) :
    C1WeightedL1Bound (K.ambient.restrict K.carrier) K.boundaryDistance
      ((12 + 4*b) * (n : ℝ) * Real.sqrt K.poincareConstant.toReal / r) := by
  letI : IsProbabilityMeasure (K.ambient.restrict K.carrier) := by
    rw [K.measure_eq_uniform]
    exact uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  apply C1WeightedL1Bound.of_exists_center
  intro f hf _ _
  exact K.conditional_reverseBuser_weighted_center hc hfin hb hr hball hRB f hf

/-- Conditional S08 bound for the genuine optimal W12 constant. -/
theorem conditional_reverseBuser_IPI (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) (hfin : K.poincareConstant < ⊤)
    {b r : ℝ} (hb : 0 ≤ b) (hr : 0 < r) (hball : Metric.ball 0 r ⊆ K.carrier)
    (hRB : K.OrdinaryL1ReverseBuserInput b) :
    K.improvedPoincareConstant ≤ ENNReal.ofReal
      (4 * (((12 + 4*b) * (n : ℝ) * Real.sqrt K.poincareConstant.toReal / r) ^ 2)) :=
  K.improvedPoincareConstant_le_of_C1WeightedL1 hc hr hball
    (K.conditional_reverseBuser_C1WeightedL1 hc hfin hb hr hball hRB)

/-- Conditional S07 estimate for the exact ambient locally-Lipschitz class. -/
theorem conditional_reverseBuser_locallyLipschitz (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) (hfin : K.poincareConstant < ⊤)
    {b r : ℝ} (hb : 0 ≤ b) (hr : 0 < r) (hball : Metric.ball 0 r ⊆ K.carrier)
    (hRB : K.OrdinaryL1ReverseBuserInput b)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f) :
    ∃ z : ℝ, (∫ x in K.carrier, |f x-z| ∂K.ambient) ≤
      ((12 + 4*b) * (n : ℝ) * Real.sqrt K.poincareConstant.toReal / r) *
        ∫ x in K.carrier, K.boundaryDistance x * ‖gradient f x‖ ∂K.ambient := by
  have hs : ∀ u : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) u →
      ∃ z : ℝ, (∫ x in K.carrier, ‖u x-z‖ ∂K.ambient) ≤
        ((12 + 4*b) * (n : ℝ) * Real.sqrt K.poincareConstant.toReal / r) *
          ∫ x in K.carrier, K.boundaryDistance x * ‖gradient u x‖ ∂K.ambient := by
    intro u hu
    simpa [Real.norm_eq_abs, gradient] using
      K.conditional_reverseBuser_weighted_center hc hfin hb hr hball hRB u (hu.of_le (by simp))
  simpa only [Real.norm_eq_abs] using
    locallyLipschitz_exists_center_bound_of_smooth K hc hr hball hs f hf
end HitAndRun.Sobolev.BoundedOpenDomain
