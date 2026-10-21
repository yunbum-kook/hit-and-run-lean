module
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic
@[expose] public section
namespace HitAndRun.Geometry
open MeasureTheory Set Filter

lemma integral_radial_residence_length {a g : ℝ} (ha : a < 1) (hg : g < 1) :
    (∫ t in Ioo a 1, (Ioi g).indicator (fun _ : ℝ => (1 : ℝ)) t) = 1 - max a g := by
  rw [setIntegral_indicator measurableSet_Ioi]
  have hs : Ioo a 1 ∩ Ioi g = Ioo (max a g) 1 := by
    ext t
    simp only [mem_inter_iff, mem_Ioo, mem_Ioi, max_lt_iff]
    tauto
  rw [hs, integral_const]
  simp [Real.volume_real_Ioo_of_le (max_lt ha hg).le]

/-- Exact Tonelli/Fubini residence-time identity for the radial gauge slice. -/
theorem integral_radial_residence {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [SFinite ν] {h g : Y → ℝ}
    (hh : Integrable h ν) (hg : Measurable g)
    {a : ℝ} (ha : a < 1) (hg1 : ∀ᵐ y ∂ν, g y < 1) :
    (∫ t in Ioo a 1, ∫ y, if g y < t then h y else 0 ∂ν) =
      ∫ y, h y * (1 - max a (g y)) ∂ν := by
  have hs : MeasurableSet {p : ℝ × Y | g p.2 < p.1} :=
    measurableSet_lt (hg.comp measurable_snd) measurable_fst
  have hi : Integrable (Function.uncurry (fun t y => if g y < t then h y else 0))
      ((volume.restrict (Ioo a 1)).prod ν) := by
    apply ((hh.comp_snd (volume.restrict (Ioo a 1))).indicator hs).congr
    exact Eventually.of_forall fun p => by simp [Set.indicator, Function.uncurry_def]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [hg1] with y hy
  have he : (fun t : ℝ => if g y < t then h y else 0) =
      (fun t => h y * (Ioi (g y)).indicator (fun _ : ℝ => (1 : ℝ)) t) := by
    funext t
    by_cases ht : g y < t <;> simp [Set.indicator, ht]
  rw [he, integral_const_mul, integral_radial_residence_length ha hy]
end HitAndRun.Geometry
