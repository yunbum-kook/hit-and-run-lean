module
public import HitAndRun.Sobolev.WeightedCutoffExtension
public import HitAndRun.Geometry.PlateauDistanceCutoffSequence
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

theorem plateau_function_sq_error_tendsto (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    {h : E → ℝ} (hh : MemLp h 2 (μ.restrict Ω)) :
    Tendsto (fun n => ∫ x in Ω,
      (plateauCutoffSequence (μ := μ) Ω n x * h x - h x)^2 ∂μ) atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence (μ := μ.restrict Ω)
    (F := fun n x => (plateauCutoffSequence (μ := μ) Ω n x * h x - h x)^2)
    (f := fun _ => (0 : ℝ)) (fun x => h x ^ 2) ?_ hh.integrable_sq ?_ ?_
  · simpa using ht
  · intro n
    exact (((plateauCutoffSequence_smooth (μ := μ) Ω n).continuous.aestronglyMeasurable.mul
      hh.aestronglyMeasurable).sub hh.aestronglyMeasurable).pow 2
  · intro n
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hn := plateauCutoffSequence_nonneg (μ := μ) Ω n x
    have hl := plateauCutoffSequence_le_one (μ := μ) Ω n x
    nlinarith [sq_nonneg (h x), mul_nonneg hn (sq_nonneg (h x)),
      mul_nonneg (sub_nonneg.mpr hl) (sq_nonneg (h x)),
      mul_nonneg hn (sub_nonneg.mpr hl)]
  · filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [plateauCutoffSequence_eventually_one (μ := μ) ho hc hx] with n hn
    simp [hn]

/-- The boundary-weighted localized derivative, written without division. -/
def plateauWeightedField (h : E → ℝ) (q : E → E) (n : ℕ) (x : E) : E :=
  plateauCutoffSequence (μ := μ) Ω n x • q x +
    (interiorDistance Ω x * h x) • gradient (plateauCutoffSequence (μ := μ) Ω n) x

theorem plateauWeightedField_norm_sub_le (h : E → ℝ) (q : E → E) (n : ℕ) (x : E) :
    ‖plateauWeightedField (μ := μ) (Ω := Ω) h q n x - q x‖ ≤
      2 * ‖q x‖ + 4 * ‖h x‖ := by
  have hn := plateauCutoffSequence_nonneg (μ := μ) Ω n x
  have hl := plateauCutoffSequence_le_one (μ := μ) Ω n x
  have hd := plateauCutoffSequence_weighted_fderiv_le (μ := μ) Ω n x
  have hdn : 0 ≤ interiorDistance Ω x := Metric.infDist_nonneg
  have hgrad : ‖gradient (plateauCutoffSequence (μ := μ) Ω n) x‖ =
      ‖fderiv ℝ (plateauCutoffSequence (μ := μ) Ω n) x‖ := by
    simp [gradient]
  have hfirst : ‖plateauCutoffSequence (μ := μ) Ω n x • q x‖ ≤ ‖q x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hn]
    nlinarith [norm_nonneg (q x)]
  have hsecond : ‖(interiorDistance Ω x * h x) •
      gradient (plateauCutoffSequence (μ := μ) Ω n) x‖ ≤ 4 * ‖h x‖ := by
    rw [norm_smul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hdn, hgrad]
    nlinarith [mul_le_mul_of_nonneg_right hd (norm_nonneg (h x))]
  calc
    ‖plateauWeightedField (μ := μ) (Ω := Ω) h q n x - q x‖ ≤
        ‖plateauWeightedField (μ := μ) (Ω := Ω) h q n x‖ + ‖q x‖ := norm_sub_le _ _
    _ ≤ (‖q x‖ + 4 * ‖h x‖) + ‖q x‖ :=
      add_le_add ((norm_add_le _ _).trans (add_le_add hfirst hsecond)) le_rfl
    _ = 2 * ‖q x‖ + 4 * ‖h x‖ := by ring

theorem plateau_weighted_gradient_sq_error_tendsto (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    {h : E → ℝ} {q : E → E} (hh : MemLp h 2 (μ.restrict Ω))
    (hq : MemLp q 2 (μ.restrict Ω)) :
    Tendsto (fun n => ∫ x in Ω,
      ‖plateauWeightedField (μ := μ) (Ω := Ω) h q n x - q x‖ ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have hqi : Integrable (fun x => ‖q x‖ ^ 2) (μ.restrict Ω) :=
    (memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).mp hq
  have ht := tendsto_integral_of_dominated_convergence (μ := μ.restrict Ω)
    (F := fun n x => ‖plateauWeightedField (μ := μ) (Ω := Ω) h q n x - q x‖ ^ 2)
    (f := fun _ => (0 : ℝ)) (fun x => 8 * ‖q x‖ ^ 2 + 32 * h x ^ 2) ?_
    ((hqi.const_mul 8).add (hh.integrable_sq.const_mul 32)) ?_ ?_
  · simpa using ht
  · intro n
    have hg : Continuous (gradient (plateauCutoffSequence (μ := μ) Ω n)) :=
      (InnerProductSpace.toDual ℝ E).symm.continuous.comp
        ((plateauCutoffSequence_smooth (μ := μ) Ω n).continuous_fderiv (by simp))
    exact ((((plateauCutoffSequence_smooth (μ := μ) Ω n).continuous.aestronglyMeasurable.smul
      hq.aestronglyMeasurable).add
      (((interiorDistance_lipschitz Ω).continuous.aestronglyMeasurable.mul
        hh.aestronglyMeasurable).smul hg.aestronglyMeasurable)).sub
      hq.aestronglyMeasurable).norm.pow 2
  · intro n
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := plateauWeightedField_norm_sub_le (μ := μ) (Ω := Ω) h q n x
    have hs := sq_le_sq₀ (norm_nonneg (plateauWeightedField (μ := μ) (Ω := Ω) h q n x - q x)) (by positivity : 0 ≤ 2 * ‖q x‖ + 4 * ‖h x‖)
    have hhabs : ‖h x‖ ^ 2 = h x ^ 2 := by simp [Real.norm_eq_abs]
    nlinarith [hs.mpr hb, sq_nonneg (2 * ‖q x‖ - 4 * ‖h x‖)]
  · filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [plateauCutoffSequence_eventually_one (μ := μ) ho hc hx,
      plateauCutoffSequence_fderiv_eventually_zero (μ := μ) ho hc hx] with n hn hd
    simp [plateauWeightedField, hn, gradient, hd]

theorem weightedCutoffGradient_weighted_eq_plateau (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (h : E → ℝ) (q : E → E) (n : ℕ) {x : E} (hx : x ∈ Ω) :
    interiorDistance Ω x • weightedCutoffGradient (Ω := Ω)
      (plateauCutoffSequence (μ := μ) Ω n) h q x =
      plateauWeightedField (μ := μ) (Ω := Ω) h q n x := by
  have hd : interiorDistance Ω x ≠ 0 := ne_of_gt
    ((ho.isClosed_compl.notMem_iff_infDist_pos hc).mp (by simpa using hx))
  simp only [weightedCutoffGradient, plateauWeightedField, smul_add, smul_smul]
  rw [mul_div_cancel₀ _ hd]

/-- Squared integral error convergence is genuine L2 norm convergence. -/
theorem tendsto_toLp_of_sq_error {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {ν : Measure E} {f : ℕ → E → F} {g : E → F}
    (hf : ∀ n, MemLp (f n) 2 ν) (hg : MemLp g 2 ν)
    (ht : Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2 ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have he (n : ℕ) : ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2 =
      ∫ x, ‖f n x - g x‖ ^ 2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf n).toLp (f n)) (hg.toLp g),
      (hf n).coeFn_toLp, hg.coeFn_toLp] with x hs hfn hgn
    simp only [hs, Pi.sub_apply, hfn, hgn, real_inner_self_eq_norm_sq]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs := (Real.continuous_sqrt.tendsto 0).comp ht
  simpa only [Function.comp_def, ← he, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs

theorem plateau_function_memLp (hb : Bornology.IsBounded Ω)
    {h : E → ℝ} (hh : MemLp h 2 (μ.restrict Ω)) (n : ℕ) :
    MemLp (fun x => plateauCutoffSequence (μ := μ) Ω n x * h x) 2 (μ.restrict Ω) :=
  ((plateauCutoffSequence_smooth (μ := μ) Ω n).continuous.memLp_top_of_hasCompactSupport
    (plateauCutoffSequence_compact hb n) _).mul hh

theorem plateauWeightedField_memLp (hb : Bornology.IsBounded Ω)
    {h : E → ℝ} {q : E → E} (hh : MemLp h 2 (μ.restrict Ω))
    (hq : MemLp q 2 (μ.restrict Ω)) (n : ℕ) :
    MemLp (plateauWeightedField (μ := μ) (Ω := Ω) h q n) 2 (μ.restrict Ω) := by
  have hg : Continuous (gradient (plateauCutoffSequence (μ := μ) Ω n)) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      ((plateauCutoffSequence_smooth (μ := μ) Ω n).continuous_fderiv (by simp))
  have ha : MemLp (fun x => interiorDistance Ω x •
      gradient (plateauCutoffSequence (μ := μ) Ω n) x) ⊤ (μ.restrict Ω) := by
    apply memLp_top_of_bound
      (((interiorDistance_lipschitz Ω).continuous.smul hg).aestronglyMeasurable) 4
    filter_upwards with x
    change ‖interiorDistance Ω x • gradient (plateauCutoffSequence (μ := μ) Ω n) x‖ ≤ 4
    have hdn : 0 ≤ interiorDistance Ω x := Metric.infDist_nonneg
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdn]
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      plateauCutoffSequence_weighted_fderiv_le (μ := μ) Ω n x
  have he := (((plateauCutoffSequence_smooth (μ := μ) Ω n).continuous.memLp_top_of_hasCompactSupport
    (plateauCutoffSequence_compact hb n) _).smul (r := 2) hq).add (hh.smul (r := 2) ha)
  convert he using 1
  funext x
  simp [plateauWeightedField, smul_smul, mul_comm]

theorem plateau_function_toLp_tendsto (hb : Bornology.IsBounded Ω)
    (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty) {h : E → ℝ} (hh : MemLp h 2 (μ.restrict Ω)) :
    Tendsto (fun n => (plateau_function_memLp hb hh n).toLp _) atTop (𝓝 (hh.toLp h)) := by
  apply tendsto_toLp_of_sq_error
  simpa only [Real.norm_eq_abs, sq_abs] using plateau_function_sq_error_tendsto ho hc hh

theorem plateauWeightedField_toLp_tendsto (hb : Bornology.IsBounded Ω)
    (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty) {h : E → ℝ} {q : E → E}
    (hh : MemLp h 2 (μ.restrict Ω)) (hq : MemLp q 2 (μ.restrict Ω)) :
    Tendsto (fun n => (plateauWeightedField_memLp hb hh hq n).toLp _) atTop
      (𝓝 (hq.toLp q)) :=
  tendsto_toLp_of_sq_error _ hq (plateau_weighted_gradient_sq_error_tendsto ho hc hh hq)
end HitAndRun.Sobolev
