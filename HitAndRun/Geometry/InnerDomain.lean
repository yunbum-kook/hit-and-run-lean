module
public import HitAndRun.Geometry.DistanceCutoff

/-! Inner parallel domains require no boundary regularity or convexity. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open Metric Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def innerDomain (Ω : Set E) (r : ℝ) : Set E := {x | r < interiorDistance Ω x}

theorem innerDomain_open (Ω : Set E) (r : ℝ) : IsOpen (innerDomain Ω r) :=
  isOpen_lt continuous_const (interiorDistance_lipschitz Ω).continuous

theorem innerDomain_subset (Ω : Set E) {r : ℝ} (hr : 0 ≤ r) :
    innerDomain Ω r ⊆ Ω := by
  intro x hx
  by_contra hn
  have := interiorDistance_zero_outside hn
  change r < interiorDistance Ω x at hx
  linarith

theorem innerDomain_bounded {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {r : ℝ} (hr : 0 ≤ r) : Bornology.IsBounded (innerDomain Ω r) :=
  hb.subset (innerDomain_subset Ω hr)

/-- The distance of an inner parallel domain loses at most its trimming radius. -/
theorem innerDomain_distance_lower {Ω : Set E} (hc : Ωᶜ.Nonempty)
    {r : ℝ} (hr : 0 ≤ r) (x : E) :
    interiorDistance Ω x - r ≤ interiorDistance (innerDomain Ω r) x := by
  have hci : (innerDomain Ω r)ᶜ.Nonempty := hc.mono
    (Set.compl_subset_compl.mpr (innerDomain_subset Ω hr))
  apply (le_infDist hci).mpr
  intro y hy
  have hdy : interiorDistance Ω y ≤ r := le_of_not_gt hy
  have hl := (interiorDistance_lipschitz Ω).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hl
  have := (le_abs_self (interiorDistance Ω x - interiorDistance Ω y)).trans hl
  linarith
end HitAndRun.Geometry
