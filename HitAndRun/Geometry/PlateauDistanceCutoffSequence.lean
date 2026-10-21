module
public import HitAndRun.Geometry.PlateauDistanceCutoffSmooth

/-! A concrete smooth plateau exhaustion of any open proper domain. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Metric Set Filter Topology EllipticPdes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

def plateauCutoffSequence (Ω : Set E) (n : ℕ) : E → ℝ :=
  let ρ : ContDiffBump (0 : E) := mollifier (show (0 : ℝ) < 1 by norm_num) n
  smoothPlateauDistance (μ := μ) Ω ρ.rOut ρ

theorem plateauCutoffSequence_smooth (Ω : Set E) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (plateauCutoffSequence (μ := μ) Ω n) :=
  smoothPlateauDistance_smooth _ (ContDiffBump.rOut_pos _) _

theorem plateauCutoffSequence_nonneg (Ω : Set E) (n : ℕ) (x : E) :
    0 ≤ plateauCutoffSequence (μ := μ) Ω n x :=
  smoothPlateauDistance_nonneg _ (ContDiffBump.rOut_pos _) _ _

theorem plateauCutoffSequence_le_one (Ω : Set E) (n : ℕ) (x : E) :
    plateauCutoffSequence (μ := μ) Ω n x ≤ 1 :=
  smoothPlateauDistance_le_one _ (ContDiffBump.rOut_pos _) _ _

theorem plateauCutoffSequence_compact {Ω : Set E} (hb : Bornology.IsBounded Ω) (n : ℕ) :
    HasCompactSupport (plateauCutoffSequence (μ := μ) Ω n) :=
  smoothPlateauDistance_compact hb (ContDiffBump.rOut_pos _) _

theorem plateauCutoffSequence_support {Ω : Set E} (hb : Bornology.IsBounded Ω) (n : ℕ) :
    tsupport (plateauCutoffSequence (μ := μ) Ω n) ⊆ Ω :=
  smoothPlateauDistance_support_domain hb (ContDiffBump.rOut_pos _) _ le_rfl

theorem plateauCutoffSequence_weighted_fderiv_le (Ω : Set E) (n : ℕ) (x : E) :
    interiorDistance Ω x * ‖fderiv ℝ (plateauCutoffSequence (μ := μ) Ω n) x‖ ≤ 4 :=
  smoothPlateauDistance_weighted_fderiv_le _ (ContDiffBump.rOut_pos _) _ le_rfl _

theorem plateauCutoffSequence_eventually_one {Ω : Set E} (ho : IsOpen Ω)
    (hc : Ωᶜ.Nonempty) {x : E} (hx : x ∈ Ω) :
    ∀ᶠ n in atTop, plateauCutoffSequence (μ := μ) Ω n x = 1 := by
  have hp : 0 < interiorDistance Ω x :=
    (ho.isClosed_compl.notMem_iff_infDist_pos hc).mp (by simpa using hx)
  have ht := (tendsto_rOut_mollifier (E := E) (show (0 : ℝ) < 1 by norm_num)).const_mul 4
  have hev : ∀ᶠ n in atTop,
      4 * (mollifier (show (0 : ℝ) < 1 by norm_num) n : ContDiffBump (0 : E)).rOut <
        interiorDistance Ω x := ht.eventually (gt_mem_nhds (by simpa using hp))
  exact hev.mono fun n hn => smoothPlateauDistance_eq_one (ContDiffBump.rOut_pos _) _ le_rfl hn.le

theorem plateauCutoffSequence_tendsto {Ω : Set E} (ho : IsOpen Ω)
    (hc : Ωᶜ.Nonempty) {x : E} (hx : x ∈ Ω) :
    Tendsto (fun n => plateauCutoffSequence (μ := μ) Ω n x) atTop (𝓝 1) :=
by
  apply tendsto_const_nhds.congr'
  filter_upwards [plateauCutoffSequence_eventually_one (μ := μ) ho hc hx] with n hn
  exact hn.symm

theorem plateauCutoffSequence_fderiv_eventually_zero {Ω : Set E} (ho : IsOpen Ω)
    (hc : Ωᶜ.Nonempty) {x : E} (hx : x ∈ Ω) :
    ∀ᶠ n in atTop, fderiv ℝ (plateauCutoffSequence (μ := μ) Ω n) x = 0 := by
  have hp : 0 < interiorDistance Ω x :=
    (ho.isClosed_compl.notMem_iff_infDist_pos hc).mp (by simpa using hx)
  have ht := (tendsto_rOut_mollifier (E := E) (show (0 : ℝ) < 1 by norm_num)).const_mul 4
  have hev : ∀ᶠ n in atTop,
      4 * (mollifier (show (0 : ℝ) < 1 by norm_num) n : ContDiffBump (0 : E)).rOut <
        interiorDistance Ω x := ht.eventually (gt_mem_nhds (by simpa using hp))
  exact hev.mono fun n hn => smoothPlateauDistance_fderiv_eq_zero (ContDiffBump.rOut_pos _) _ le_rfl hn
end HitAndRun.Geometry
