module
public import HitAndRun.Geometry.DistanceCutoff
public import HitAndRun.Analysis.MollifierLipschitz

/-! Actual bounded interior plateaus built from complement distance. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Metric Set Filter Topology EllipticPdes
open scoped Convolution NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A plateau with transition between complement distances `2ε` and `3ε`. -/
def plateauDistance (Ω : Set E) (ε : ℝ) (x : E) : ℝ :=
  min (truncatedDistance Ω ε x / ε) 1

theorem plateauDistance_nonneg (Ω : Set E) {ε : ℝ} (hε : 0 < ε) (x : E) :
    0 ≤ plateauDistance Ω ε x :=
  le_min (div_nonneg (truncatedDistance_nonneg Ω ε x) hε.le) zero_le_one

theorem plateauDistance_le_one (Ω : Set E) (ε : ℝ) (x : E) :
    plateauDistance Ω ε x ≤ 1 := min_le_right _ _

theorem plateauDistance_eq_one {Ω : Set E} {ε : ℝ} (hε : 0 < ε) {x : E}
    (hx : 3 * ε ≤ interiorDistance Ω x) : plateauDistance Ω ε x = 1 := by
  apply min_eq_right
  apply (le_div_iff₀ hε).2
  have hh := le_max_left (interiorDistance Ω x - 2 * ε) 0
  dsimp [truncatedDistance]
  linarith

theorem plateauDistance_lipschitz (Ω : Set E) {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith ⟨ε⁻¹, inv_nonneg.mpr hε.le⟩ (plateauDistance Ω ε) := by
  apply LipschitzWith.min_const
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := (truncatedDistance_lipschitz Ω ε).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hh
  simp only [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hε, NNReal.coe_mk]
  calc
    _ ≤ dist x y / ε := (div_le_div_iff_of_pos_right hε).2 hh
    _ = ε⁻¹ * dist x y := by rw [div_eq_mul_inv, mul_comm]

theorem tsupport_plateauDistance_subset {Ω : Set E} {ε : ℝ} (hε : 0 < ε) :
    tsupport (plateauDistance Ω ε) ⊆ {x | 2 * ε ≤ interiorDistance Ω x} := by
  apply (closure_mono (show Function.support (plateauDistance Ω ε) ⊆
      Function.support (truncatedDistance Ω ε) from ?_)).trans
    (tsupport_truncatedDistance_subset hε)
  intro x hx hh
  exact hx (by simp [plateauDistance, hh])

theorem tsupport_plateauDistance_subset_domain {Ω : Set E} {ε : ℝ} (hε : 0 < ε) :
    tsupport (plateauDistance Ω ε) ⊆ Ω := by
  intro x hx
  have hd := tsupport_plateauDistance_subset hε hx
  change 2 * ε ≤ interiorDistance Ω x at hd
  by_contra hn
  rw [interiorDistance_zero_outside hn] at hd
  linarith

theorem hasCompactSupport_plateauDistance {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (plateauDistance Ω ε) :=
  hb.isCompact_closure.of_isClosed_subset (isClosed_tsupport _)
    ((tsupport_plateauDistance_subset_domain hε).trans subset_closure)
end HitAndRun.Geometry
