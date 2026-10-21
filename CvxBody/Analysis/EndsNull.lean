module
public import CvxBody.Analysis.MassBalance
public import CvxBody.Geometry.RayEnds

@[expose] public section


/-!
# Discharging the ends-null premise of the mass balance

`MassBalance.lean` proves the mass balance of the maximizer under the explicit premise
`μ (Ends u) = 0`; `RayEnds.lean` proves `volume (RayEnds u) = 0` for every 1-Lipschitz `u`. Here the
two descriptions of the ray endpoints are identified (`Ends u = RayEnds u`) and the premise is
removed for absolutely continuous `μ`.
-/

open MeasureTheory
open OAI.LeanBlast.KLS

namespace CvxBody.Geometry

variable {n : ℕ}

theorem ends_eq_rayEnds {u : Space n → ℝ} (hu : LipschitzWith 1 u) : Ends u = RayEnds u := by
  ext x
  rw [mem_ends_iff hu, mem_rayEnds_iff hu]

theorem volume_ends_eq_zero' {u : Space n → ℝ} (hu : LipschitzWith 1 u) : volume (Ends u) = 0 := by
  rw [ends_eq_rayEnds hu]; exact volume_rayEnds_eq_zero hu

theorem measure_ends_eq_zero {μ : Measure (Space n)} (hμ : μ ≪ volume) {u : Space n → ℝ}
    (hu : LipschitzWith 1 u) : μ (Ends u) = 0 :=
  hμ (volume_ends_eq_zero' hu)

/-- The mass balance of the maximizer, with the ends-null premise discharged. -/
theorem exists_maximizer_mass_balance_of_ac (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (hint : Integrable (fun x : Space n => ‖x‖) μ) {S : Set (Space n)}
    (hS : MeasurableSet S) (h0 : 0 < μ S) (h1 : μ S < 1) :
    ∃ u, IsLipschitzMaximizer μ (massBalanceFn μ S) u ∧ μ (Loose u) = 0 ∧ μ (Strain u) = 1 ∧
      ∀ B : Set (Space n × Space n), MeasurableSet B →
        ∫ x in Strain u ∩ rayInv u ⁻¹' B, massBalanceFn μ S x ∂μ = 0 :=
  exists_maximizer_mass_balance hint hS h0 h1 fun _ hmax => measure_ends_eq_zero hμ hmax.1

end CvxBody.Geometry
