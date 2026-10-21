module
public import HitAndRun.Geometry.ConvexPoincareFiniteTransport
public import HitAndRun.Geometry.ConvexPoincareFiniteSegment
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Integrating one half-segment only uses nonsingular affine contractions. -/
theorem convex_half_difference_integral_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hb : Bornology.IsBounded K) (hm : MeasurableSet K) (hc : Convex ℝ K)
    {y : E} (hy : y ∈ K) (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ K, ‖x-y‖ ≤ D) :
    (∫ x in K, (f x - f ((1/2 : ℝ) • y + (1/2 : ℝ) • x))^2 ∂μ) ≤
      D^2 * ((1/2 : ℝ)^Module.finrank ℝ E)⁻¹ * ∫ x in K, ‖fderiv ℝ f x‖^2 ∂μ := by
  let h : E → ℝ := fun x => ‖fderiv ℝ f x‖^2
  have hh : Continuous h := (hf.continuous_fderiv (by norm_num)).norm.pow 2
  have hjc : Continuous (fun p : ℝ × E => h ((1-p.1) • y + p.1 • p.2)) := by fun_prop
  have hj : Integrable (fun p : ℝ × E => h ((1-p.1) • y + p.1 • p.2))
      ((volume.restrict (Ioo (1/2 : ℝ) 1)).prod (μ.restrict K)) := by
    rw [Measure.prod_restrict]
    exact (hjc.continuousOn.integrableOn_compact
      (isCompact_Icc.prod hb.isCompact_closure)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self subset_closure)
  have hi := hj.integral_prod_right
  have hl : IntegrableOn (fun x => (f x-f ((1/2 : ℝ) • y+(1/2 : ℝ) • x))^2) K μ :=
    continuous_integrableOn_bounded μ hb (by fun_prop)
  have hpt : ∀ x ∈ K, (f x-f ((1/2 : ℝ) • y+(1/2 : ℝ) • x))^2 ≤
      D^2 * ∫ a in Ioo (1/2 : ℝ) 1, h ((1-a) • y+a • x) := by
    intro x hx
    have hs := half_segment_sq_sub_le f hf x y
    have hd : (1/2 : ℝ) * ‖x-y‖^2 ≤ D^2 := by
      have hsq := pow_le_pow_left₀ (norm_nonneg (x-y)) (hdiam x hx) 2
      nlinarith [sq_nonneg ‖x-y‖]
    exact hs.trans (mul_le_mul_of_nonneg_right hd (integral_nonneg fun _ => sq_nonneg _))
  have hbnd := integral_mono_ae hl (hi.const_mul (D^2))
    ((ae_restrict_mem hm).mono fun x hx => hpt x hx)
  rw [integral_const_mul, ← integral_integral_swap hj] at hbnd
  exact hbnd.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (integral_convex_half_homothety_le μ hb hc hy hh (fun _ => sq_nonneg _)) (sq_nonneg D))

/-- Averaging the midpoint decomposition controls variance by half-differences. -/
theorem variance_le_four_half_difference_bound (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hb : Bornology.IsBounded K) (hm : MeasurableSet K)
    [IsProbabilityMeasure (μ.restrict K)] (f : E → ℝ) (hf : Continuous f)
    {B : ℝ} (hbound : ∀ y ∈ K,
      (∫ x in K, (f x-f ((1/2 : ℝ) • y+(1/2 : ℝ) • x))^2 ∂μ) ≤ B) :
    variance f (μ.restrict K) ≤ 4 * B := by
  let ν := μ.restrict K
  let H : E → E → ℝ := fun x y => (f x-f ((1/2 : ℝ) • y+(1/2 : ℝ) • x))^2
  have hint (g : E × E → ℝ) (hg : Continuous g) : Integrable g (ν.prod ν) := by
    dsimp [ν]
    rw [Measure.prod_restrict]
    exact (hg.continuousOn.integrableOn_compact
      (hb.isCompact_closure.prod hb.isCompact_closure)).mono_set
      (Set.prod_mono subset_closure subset_closure)
  have hH : Integrable (fun p : E × E => H p.2 p.1) (ν.prod ν) := hint _ (by dsimp [H]; fun_prop)
  have hHs : Integrable (fun p : E × E => H p.1 p.2) (ν.prod ν) := hint _ (by dsimp [H]; fun_prop)
  have hP : Integrable (fun p : E × E => (f p.2-f p.1)^2) (ν.prod ν) := hint _ (by fun_prop)
  have htotal : (∫ y, ∫ x, H x y ∂ν ∂ν) ≤ B := by
    have h := integral_mono_ae hH.integral_prod_left (integrable_const B)
      ((ae_restrict_mem hm).mono fun y hy => hbound y hy)
    simpa using h
  have hswap : (∫ y, ∫ x, H y x ∂ν ∂ν) = ∫ y, ∫ x, H x y ∂ν ∂ν :=
    integral_integral_swap hHs
  have hp : (∫ p, (f p.2-f p.1)^2 ∂ν.prod ν) ≤
      ∫ p, 2 * (H p.2 p.1+H p.1 p.2) ∂ν.prod ν := by
    apply integral_mono hP ((hH.add hHs).const_mul 2)
    intro p
    dsimp [H]
    rw [add_comm ((1/2 : ℝ) • p.2) ((1/2 : ℝ) • p.1)]
    nlinarith [sq_nonneg (f p.2+f p.1-2*f ((1/2 : ℝ) • p.1+(1/2 : ℝ) • p.2))]
  rw [integral_const_mul, integral_add hH hHs, integral_prod _ hP,
    integral_prod _ hH, integral_prod _ hHs, hswap] at hp
  have hv : variance f ν ≤ ∫ y, ∫ x, (f x-f y)^2 ∂ν ∂ν := by
    have hpwise (y : E) : variance f ν ≤ ∫ x, (f x-f y)^2 ∂ν := by
      have h := variance_le_expectation_sq (μ := ν) (X := fun x => f x-f y)
        ((hf.sub continuous_const).aestronglyMeasurable)
      rw [variance_sub_const hf.aestronglyMeasurable] at h
      exact h
    have h := integral_mono (integrable_const (variance f ν)) hP.integral_prod_left hpwise
    simpa using h
  exact hv.trans (hp.trans (by linarith))

/-- A concrete dimension-exponential smooth ordinary PI on a bounded convex domain. -/
theorem convex_smooth_variance_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hb : Bornology.IsBounded K) (hm : MeasurableSet K) (hc : Convex ℝ K)
    [IsProbabilityMeasure (μ.restrict K)] (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ x ∈ K, ∀ y ∈ K, ‖x-y‖ ≤ D) :
    variance f (μ.restrict K) ≤
      (4 * D^2 * ((1/2 : ℝ)^Module.finrank ℝ E)⁻¹) *
        ∫ x in K, ‖fderiv ℝ f x‖^2 ∂μ := by
  have h := variance_le_four_half_difference_bound μ hb hm f hf.continuous
    (fun y hy => convex_half_difference_integral_le μ hb hm hc hy f hf hD
      (fun x hx => hdiam x hx y hy))
  simpa only [mul_assoc] using h

end HitAndRun.Geometry
