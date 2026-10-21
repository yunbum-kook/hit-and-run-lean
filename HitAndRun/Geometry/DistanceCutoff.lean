module
public import HitAndRun.External.EllipticPDE.Analysis.Mollifier
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

/-! Actual complement-distance truncations for bounded open domains.
No smooth-boundary assumption is introduced. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Metric Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def interiorDistance (Ω : Set E) (x : E) : ℝ := infDist x Ωᶜ

theorem interiorDistance_lipschitz (Ω : Set E) : LipschitzWith 1 (interiorDistance Ω) :=
  lipschitz_infDist_pt Ωᶜ

theorem interiorDistance_zero_outside {Ω : Set E} {x : E} (hx : x ∉ Ω) :
    interiorDistance Ω x = 0 := infDist_zero_of_mem hx

/-- Inside an open proper domain, complement distance is the manuscript's boundary distance. -/
theorem interiorDistance_eq_frontier {Ω : Set E} (ho : IsOpen Ω) (hne : Ω ≠ univ)
    {x : E} (hx : x ∈ Ω) : interiorDistance Ω x = infDist x (frontier Ω) := by
  obtain ⟨y, hy, he⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hne
  apply le_antisymm
  · apply infDist_le_infDist_of_subset _ ⟨y, hy⟩
    intro z hz
    change z ∉ Ω
    simpa only [ho.interior_eq] using hz.2
  · exact (infDist_le_dist_of_mem hy).trans_eq he.symm

def truncatedDistance (Ω : Set E) (epsilon : ℝ) (x : E) : ℝ :=
  max (interiorDistance Ω x - 2 * epsilon) 0

theorem truncatedDistance_nonneg (Ω : Set E) (epsilon : ℝ) (x : E) :
    0 ≤ truncatedDistance Ω epsilon x := le_max_right _ _

theorem truncatedDistance_lipschitz (Ω : Set E) (epsilon : ℝ) :
    LipschitzWith 1 (truncatedDistance Ω epsilon) := by
  have hs : LipschitzWith 1 (fun x => interiorDistance Ω x - 2 * epsilon) := by
    simpa using (interiorDistance_lipschitz Ω).sub (LipschitzWith.const (2 * epsilon))
  exact hs.max_const 0

theorem tsupport_truncatedDistance_subset {Ω : Set E} {epsilon : ℝ} (he : 0 < epsilon) :
    tsupport (truncatedDistance Ω epsilon) ⊆ {x | 2 * epsilon ≤ interiorDistance Ω x} := by
  apply closure_minimal
  · intro x hx
    have hn : truncatedDistance Ω epsilon x ≠ 0 := hx
    have hp : 0 < interiorDistance Ω x - 2 * epsilon := by
      by_contra h
      exact hn (max_eq_right (le_of_not_gt h))
    change 2 * epsilon ≤ interiorDistance Ω x
    linarith
  · exact isClosed_le continuous_const (interiorDistance_lipschitz Ω).continuous

theorem tsupport_truncatedDistance_subset_domain {Ω : Set E} {epsilon : ℝ} (he : 0 < epsilon) :
    tsupport (truncatedDistance Ω epsilon) ⊆ Ω := by
  intro x hx
  have hd := tsupport_truncatedDistance_subset he hx
  by_contra hn
  change 2 * epsilon ≤ interiorDistance Ω x at hd
  rw [interiorDistance_zero_outside hn] at hd
  linarith

theorem hasCompactSupport_truncatedDistance {Ω : Set E}
    (hb : Bornology.IsBounded Ω) {epsilon : ℝ} (he : 0 < epsilon) :
    HasCompactSupport (truncatedDistance Ω epsilon) :=
  hb.isCompact_closure.of_isClosed_subset (isClosed_tsupport _)
    ((tsupport_truncatedDistance_subset_domain he).trans subset_closure)
end HitAndRun.Geometry
