module
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Tactic
@[expose] public section

/-! Inward-dilation ingredients for convex-domain H1 density. These lemmas do not
assert H1 density or introduce a boundary regularity assumption. -/
namespace HitAndRun.Geometry
open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Dilation is strongly continuous on bounded continuous tests for every finite
measure. This is the dense-test part of the L2 dilation argument. -/
theorem integral_sq_dilation_sub_tendsto_of_bounded
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
    {μ : Measure E} [IsFiniteMeasure μ] {g : E → F}
    (hg : Continuous g) {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x, ‖g x‖ ≤ B)
    {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun k => ∫ x, ‖g (a k • x) - g x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun k x => ‖g (a k • x) - g x‖ ^ 2)
    (f := fun _ => (0 : ℝ)) (fun _ => (2 * B) ^ 2)
    (fun k => ((hg.comp (continuous_const.smul continuous_id)).sub hg).norm.pow 2 |>.aestronglyMeasurable)
    (integrable_const _) ?_ ?_
  · simpa using h
  · intro k
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb : ‖g (a k • x) - g x‖ ≤ 2 * B :=
      (norm_sub_le _ _).trans (by linarith [hbound (a k • x), hbound x])
    nlinarith [norm_nonneg (g (a k • x) - g x)]
  · filter_upwards [] with x
    have hx : Tendsto (fun k => g (a k • x) - g x) atTop (𝓝 (0 : F)) := by
      simpa using ((hg.tendsto x).comp (by simpa using ha.smul_const x)).sub_const (g x)
    simpa using hx.norm.pow 2

/-- Exact L2 dilation scaling, reusing the pinned Haar Jacobian theorem. -/
theorem integral_sq_dilation {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → F) {a : ℝ} (ha : 0 < a) :
    (∫ x, ‖f (a • x)‖ ^ 2 ∂μ) =
      (a ^ Module.finrank ℝ E)⁻¹ * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  simpa only [smul_eq_mul] using
    Measure.integral_comp_smul_of_nonneg μ (fun x => ‖f x‖ ^ 2) a (hR := ha.le)

/-- Pullback by a nonzero dilation preserves actual L2 membership. -/
theorem memLp_comp_dilation {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] {μ : Measure E} [μ.IsAddHaarMeasure]
    {f : E → F} (hf : MemLp f 2 μ) {a : ℝ} (ha : a ≠ 0) :
    MemLp (fun x => f (a • x)) 2 μ := by
  have hm : MemLp f 2 (Measure.map (fun x : E => a • x) μ) := by
    rw [Measure.map_addHaar_smul μ ha]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hm.comp_of_map (continuous_const.smul continuous_id).aemeasurable

/-- Three-term square estimate for the dense-test dilation argument. -/
theorem dilation_error_sq_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] (f g : E → F) (a : ℝ) (x : E) :
    ‖f (a • x) - f x‖ ^ 2 ≤ 3 * (‖f (a • x) - g (a • x)‖ ^ 2 +
      ‖g (a • x) - g x‖ ^ 2 + ‖g x - f x‖ ^ 2) := by
  have hn : ‖f (a • x) - f x‖ ≤ ‖f (a • x) - g (a • x)‖ +
      ‖g (a • x) - g x‖ + ‖g x - f x‖ := by
    calc
      _ = ‖(f (a • x) - g (a • x)) + (g (a • x) - g x) + (g x - f x)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  nlinarith [norm_nonneg (f (a • x) - f x), norm_nonneg (f (a • x) - g (a • x)),
    norm_nonneg (g (a • x) - g x), norm_nonneg (g x - f x),
    sq_nonneg (‖f (a • x) - g (a • x)‖ - ‖g (a • x) - g x‖),
    sq_nonneg (‖g (a • x) - g x‖ - ‖g x - f x‖),
    sq_nonneg (‖g x - f x‖ - ‖f (a • x) - g (a • x)‖)]
/-- Strong L2 dilation continuity on a finite-measure set for a genuine global
L2 function. The approximation uses compact continuous tests, not pointwise
continuity of the original function. -/
theorem integral_sq_dilation_sub_tendsto
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E} [μ.IsAddHaarMeasure] [μ.Regular]
    {K : Set E} [IsFiniteMeasure (μ.restrict K)]
    {f : E → F} (hf : MemLp f 2 μ) {a : ℕ → ℝ}
    (ha0 : ∀ k, 0 < a k) (ha : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun k => ∫ x in K, ‖f (a k • x) - f x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hε' : 0 < ε / 24 := by positivity
  have hf2 : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
  obtain ⟨g, hgc, hfg, hg, hgL⟩ :=
    hf2.exists_hasCompactSupport_integral_rpow_sub_le (p := (2 : ℝ)) (by norm_num) hε'
  simp only [Real.rpow_two] at hfg
  have hgL : MemLp g 2 μ := by simpa using hgL
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hgc
  have hB0 : 0 ≤ B := (norm_nonneg (g 0)).trans (hB 0)
  have hmid := integral_sq_dilation_sub_tendsto_of_bounded
    (μ := μ.restrict K) hg hB0 hB ha
  have hcoef : Tendsto (fun k => (a k ^ Module.finrank ℝ E)⁻¹) atTop (𝓝 1) := by
    simpa using (ha.pow (Module.finrank ℝ E)).inv₀ (by simp)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hmid.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 12))).and
      (hcoef.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))))
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨hmidk, hcoefk⟩ := hN k hk
  have hF := (memLp_comp_dilation hf (ha0 k).ne').sub hf
  have hU := memLp_comp_dilation (hf.sub hgL) (ha0 k).ne'
  have hV := (memLp_comp_dilation hgL (ha0 k).ne').sub hgL
  have hW := hgL.sub hf
  have hUi : Integrable (fun x => ‖f (a k • x) - g (a k • x)‖ ^ 2) μ := hU.norm.integrable_sq
  have hVi : Integrable (fun x => ‖g (a k • x) - g x‖ ^ 2) μ := hV.norm.integrable_sq
  have hWi : Integrable (fun x => ‖g x - f x‖ ^ 2) μ := hW.norm.integrable_sq
  have hu : (∫ x in K, ‖f (a k • x) - g (a k • x)‖ ^ 2 ∂μ) ≤ 2 * (ε / 24) := by
    calc
      _ ≤ ∫ x, ‖f (a k • x) - g (a k • x)‖ ^ 2 ∂μ :=
        integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun x => sq_nonneg _) hUi
      _ = (a k ^ Module.finrank ℝ E)⁻¹ * ∫ x, ‖f x - g x‖ ^ 2 ∂μ :=
        integral_sq_dilation μ (fun x => f x - g x) (ha0 k)
      _ ≤ 2 * (ε / 24) := mul_le_mul hcoefk.le hfg (integral_nonneg fun x => sq_nonneg _) (by norm_num)
  have hw : (∫ x in K, ‖g x - f x‖ ^ 2 ∂μ) ≤ ε / 24 := by
    calc
      _ ≤ ∫ x, ‖g x - f x‖ ^ 2 ∂μ :=
        integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun x => sq_nonneg _) hWi
      _ = ∫ x, ‖f x - g x‖ ^ 2 ∂μ := by simp only [norm_sub_rev]
      _ ≤ _ := hfg
  have hsum := integral_mono (μ := μ.restrict K) hF.norm.integrable_sq.restrict
    (((hUi.restrict.add hVi.restrict).add hWi.restrict).const_mul 3)
    (dilation_error_sq_le f g (a k))
  simp only [integral_const_mul, integral_add' (hUi.restrict.add hVi.restrict) hWi.restrict,
    integral_add' hUi.restrict hVi.restrict] at hsum
  simp only [Pi.sub_apply] at hsum
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun x => sq_nonneg _)]
  linarith
/-- The domain version needs only L2 membership on K. Zero extension is used
internally and disappears because every dilation maps K into itself. -/
theorem integral_sq_dilation_sub_tendsto_restrict
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E} [μ.IsAddHaarMeasure] [μ.Regular]
    {K : Set E} [IsFiniteMeasure (μ.restrict K)] (hK : MeasurableSet K)
    {f : E → F} (hf : MemLp f 2 (μ.restrict K)) {a : ℕ → ℝ}
    (ha0 : ∀ k, 0 < a k) (ha : Tendsto a atTop (𝓝 1))
    (hmap : ∀ k, MapsTo (fun x => a k • x) K K) :
    Tendsto (fun k => ∫ x in K, ‖f (a k • x) - f x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hext : MemLp (K.indicator f) 2 μ :=
    (memLp_indicator_iff_restrict hK.nullMeasurableSet).mpr hf
  have h := integral_sq_dilation_sub_tendsto (K := K) hext ha0 ha
  have he : (fun k => ∫ x in K, ‖K.indicator f (a k • x) - K.indicator f x‖ ^ 2 ∂μ) =
      (fun k => ∫ x in K, ‖f (a k • x) - f x‖ ^ 2 ∂μ) := by
    funext k
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hK] with x hx
    simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hmap k hx)]
  rwa [he] at h

/-- Inward dilations of an arbitrary convex body containing zero converge in
actual L2, without any boundary smoothness. -/
theorem integral_sq_inward_dilation_sub_tendsto
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E} [μ.IsAddHaarMeasure] [μ.Regular]
    {K : Set E} [IsFiniteMeasure (μ.restrict K)] (hK : MeasurableSet K)
    (hconv : Convex ℝ K) (hzero : (0 : E) ∈ K)
    {f : E → F} (hf : MemLp f 2 (μ.restrict K)) {a : ℕ → ℝ}
    (ha0 : ∀ k, 0 < a k) (ha1 : ∀ k, a k ≤ 1) (ha : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun k => ∫ x in K, ‖f (a k • x) - f x‖ ^ 2 ∂μ) atTop (𝓝 0) :=
  integral_sq_dilation_sub_tendsto_restrict hK hf ha0 ha
    (fun k x hx => hconv.smul_mem_of_zero_mem hzero hx ⟨(ha0 k).le, ha1 k⟩)
end HitAndRun.Geometry
