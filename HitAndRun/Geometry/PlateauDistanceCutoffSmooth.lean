module
public import HitAndRun.Geometry.PlateauDistanceCutoff

/-! Probability mollification of actual interior plateaus. No boundary regularity is assumed. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Metric Set Filter Topology EllipticPdes
open scoped Convolution NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

def smoothPlateauDistance (Ω : Set E) (ε : ℝ) (ρ : ContDiffBump (0 : E)) : E → ℝ :=
  ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] plateauDistance Ω ε

theorem smoothPlateauDistance_smooth (Ω : Set E) {ε : ℝ} (hε : 0 < ε)
    (ρ : ContDiffBump (0 : E)) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothPlateauDistance (μ := μ) Ω ε ρ) :=
  contDiff_normed_convolution ρ (plateauDistance_lipschitz Ω hε).continuous.locallyIntegrable

theorem smoothPlateauDistance_lipschitz (Ω : Set E) {ε : ℝ} (hε : 0 < ε)
    (ρ : ContDiffBump (0 : E)) :
    LipschitzWith ⟨ε⁻¹, inv_nonneg.mpr hε.le⟩ (smoothPlateauDistance (μ := μ) Ω ε ρ) :=
  HitAndRun.Analysis.lipschitz_normed_convolution ρ (plateauDistance_lipschitz Ω hε)

theorem smoothPlateauDistance_nonneg (Ω : Set E) {ε : ℝ} (hε : 0 < ε)
    (ρ : ContDiffBump (0 : E)) (x : E) :
    0 ≤ smoothPlateauDistance (μ := μ) Ω ε ρ x := by
  apply integral_nonneg
  intro t
  exact mul_nonneg (ρ.nonneg_normed t) (plateauDistance_nonneg Ω hε (x - t))

theorem smoothPlateauDistance_le_one (Ω : Set E) {ε : ℝ} (hε : 0 < ε)
    (ρ : ContDiffBump (0 : E)) (x : E) :
    smoothPlateauDistance (μ := μ) Ω ε ρ x ≤ 1 := by
  apply (Real.le_norm_self _).trans
  apply norm_normed_convolution_le ρ (plateauDistance_lipschitz Ω hε).continuous
  intro y
  rw [Real.norm_eq_abs, abs_of_nonneg (plateauDistance_nonneg Ω hε y)]
  exact plateauDistance_le_one Ω ε y

theorem smoothPlateauDistance_compact {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {ε : ℝ} (hε : 0 < ε) (ρ : ContDiffBump (0 : E)) :
    HasCompactSupport (smoothPlateauDistance (μ := μ) Ω ε ρ) :=
  hasCompactSupport_normed_convolution ρ (hasCompactSupport_plateauDistance hb hε)

theorem smoothPlateauDistance_support_margin {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {ε : ℝ} (hε : 0 < ε) (ρ : ContDiffBump (0 : E)) (hr : ρ.rOut ≤ ε) :
    tsupport (smoothPlateauDistance (μ := μ) Ω ε ρ) ⊆ {x | ε ≤ interiorDistance Ω x} := by
  intro x hx
  have hc := hasCompactSupport_plateauDistance hb hε
  have ht := tsupport_normed_convolution_subset (μ := μ) ρ hc hx
  rw [hc.cthickening_eq_biUnion_closedBall ρ.rOut_pos.le] at ht
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp ht
  have hdy := tsupport_plateauDistance_subset hε hy
  change 2 * ε ≤ interiorDistance Ω y at hdy
  have hl := (interiorDistance_lipschitz Ω).dist_le_mul x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hl
  have hd := (abs_le.mp hl).1
  have hxy' : dist x y ≤ ρ.rOut := hxy
  change ε ≤ interiorDistance Ω x
  linarith

theorem smoothPlateauDistance_support_domain {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {ε : ℝ} (hε : 0 < ε) (ρ : ContDiffBump (0 : E)) (hr : ρ.rOut ≤ ε) :
    tsupport (smoothPlateauDistance (μ := μ) Ω ε ρ) ⊆ Ω := by
  intro x hx
  have hm := smoothPlateauDistance_support_margin hb hε ρ hr hx
  change ε ≤ interiorDistance Ω x at hm
  by_contra hn
  rw [interiorDistance_zero_outside hn] at hm
  linarith

theorem smoothPlateauDistance_eq_one {Ω : Set E} {ε : ℝ} (hε : 0 < ε)
    (ρ : ContDiffBump (0 : E)) (hr : ρ.rOut ≤ ε) {x : E}
    (hx : 4 * ε ≤ interiorDistance Ω x) :
    smoothPlateauDistance (μ := μ) Ω ε ρ x = 1 := by
  rw [smoothPlateauDistance, convolution_def, ← ρ.integral_normed (μ := μ)]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  by_cases ht : ρ.normed μ t = 0
  · simp [ht]
  · have hm : t ∈ Function.support (ρ.normed μ) := ht
    rw [ρ.support_normed_eq] at hm
    have hn : ‖t‖ ≤ ρ.rOut :=
      (by simpa only [mem_ball, dist_zero_right] using hm : ‖t‖ < ρ.rOut).le
    have hl := (interiorDistance_lipschitz Ω).dist_le_mul (x - t) x
    simp only [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm, sub_sub_cancel_left,
      norm_neg] at hl
    have hd := (abs_le.mp hl).1
    rw [plateauDistance_eq_one hε (by linarith), mul_one]

theorem smoothPlateauDistance_fderiv_le (Ω : Set E) {ε : ℝ} (hε : 0 < ε)
    (ρ : ContDiffBump (0 : E)) (x : E) :
    ‖fderiv ℝ (smoothPlateauDistance (μ := μ) Ω ε ρ) x‖ ≤ ε⁻¹ :=
  norm_fderiv_le_of_lipschitz ℝ (smoothPlateauDistance_lipschitz Ω hε ρ)

theorem smoothPlateauDistance_fderiv_eq_zero {Ω : Set E} {ε : ℝ} (hε : 0 < ε)
    (ρ : ContDiffBump (0 : E)) (hr : ρ.rOut ≤ ε) {x : E}
    (hx : 4 * ε < interiorDistance Ω x) :
    fderiv ℝ (smoothPlateauDistance (μ := μ) Ω ε ρ) x = 0 := by
  have hev : ∀ᶠ y in 𝓝 x, 4 * ε < interiorDistance Ω y :=
    (interiorDistance_lipschitz Ω).continuous.continuousAt.eventually (lt_mem_nhds hx)
  have heq : smoothPlateauDistance (μ := μ) Ω ε ρ =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    hev.mono fun y hy => smoothPlateauDistance_eq_one hε ρ hr hy.le
  rw [heq.fderiv_eq]
  exact fderiv_const_apply _

theorem smoothPlateauDistance_weighted_fderiv_le (Ω : Set E) {ε : ℝ} (hε : 0 < ε)
    (ρ : ContDiffBump (0 : E)) (hr : ρ.rOut ≤ ε) (x : E) :
    interiorDistance Ω x * ‖fderiv ℝ (smoothPlateauDistance (μ := μ) Ω ε ρ) x‖ ≤ 4 := by
  by_cases hx : 4 * ε < interiorDistance Ω x
  · rw [smoothPlateauDistance_fderiv_eq_zero hε ρ hr hx]
    simp
  · have hd : 0 ≤ interiorDistance Ω x := infDist_nonneg
    have hn := mul_le_mul_of_nonneg_left (smoothPlateauDistance_fderiv_le (μ := μ) Ω hε ρ x) hd
    have hp : interiorDistance Ω x * ε⁻¹ ≤ 4 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hε]
      linarith
    exact hn.trans hp
/-- The whole derivative support lies in the shrinking boundary strip. -/
theorem smoothPlateauDistance_fderiv_support {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {ε : ℝ} (hε : 0 < ε) (ρ : ContDiffBump (0 : E)) (hr : ρ.rOut ≤ ε) :
    tsupport (fderiv ℝ (smoothPlateauDistance (μ := μ) Ω ε ρ)) ⊆
      {x | ε ≤ interiorDistance Ω x ∧ interiorDistance Ω x ≤ 4 * ε} := by
  have hu : tsupport (fderiv ℝ (smoothPlateauDistance (μ := μ) Ω ε ρ)) ⊆
      {x | interiorDistance Ω x ≤ 4 * ε} := by
    apply closure_minimal
    · intro x hx
      by_contra hn
      exact hx (smoothPlateauDistance_fderiv_eq_zero hε ρ hr (lt_of_not_ge hn))
    · exact isClosed_le (interiorDistance_lipschitz Ω).continuous continuous_const
  intro x hx
  exact ⟨smoothPlateauDistance_support_margin hb hε ρ hr
    (tsupport_fderiv_subset ℝ hx), hu hx⟩

theorem smoothPlateauDistance_scaled_fderiv_le (Ω : Set E) {ε : ℝ} (hε : 0 < ε)
    (ρ : ContDiffBump (0 : E)) (x : E) :
    ε * ‖fderiv ℝ (smoothPlateauDistance (μ := μ) Ω ε ρ) x‖ ≤ 1 := by
  calc
    _ ≤ ε * ε⁻¹ := mul_le_mul_of_nonneg_left
      (smoothPlateauDistance_fderiv_le (μ := μ) Ω hε ρ x) hε.le
    _ = 1 := mul_inv_cancel₀ hε.ne'
end HitAndRun.Geometry
