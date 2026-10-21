module
public import HitAndRun.Geometry.DistanceCutoff
public import HitAndRun.External.EllipticPDE.Sobolev.Graph
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! The actual coefficient φ/δ in the weighted distributional gradient test.
Compact interior support makes it continuous and L2 without differentiating δ. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

theorem continuous_div_of_nonzero_on_tsupport {f g : E → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hn : ∀ x ∈ tsupport f, g x ≠ 0) : Continuous (fun x => f x / g x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf.continuousAt.div hg.continuousAt (hn x hx)
  · have he := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp [hy]

def boundaryTest (φ : testFunctions Ω) (x : E) : ℝ :=
  (φ : E → ℝ) x / interiorDistance Ω x

theorem boundaryTest_continuous (hΩ : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (φ : testFunctions Ω) : Continuous (boundaryTest φ) := by
  apply continuous_div_of_nonzero_on_tsupport φ.2.1.continuous
    (interiorDistance_lipschitz Ω).continuous
  intro x hx
  have hm : x ∈ Ω := φ.2.2.2 hx
  have hp : 0 < Metric.infDist x Ωᶜ :=
    (hΩ.isClosed_compl.notMem_iff_infDist_pos hc).mp (by simpa using hm)
  exact ne_of_gt hp

theorem boundaryTest_compact (φ : testFunctions Ω) : HasCompactSupport (boundaryTest φ) := by
  apply φ.2.2.1.of_isClosed_subset (isClosed_tsupport _)
  apply closure_mono
  intro x hx
  change (φ : E → ℝ) x ≠ 0
  intro hz
  exact hx (by simp [boundaryTest, hz])

theorem boundaryTest_memLp (hΩ : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (φ : testFunctions Ω) : MemLp (boundaryTest φ) 2 μ :=
  (boundaryTest_continuous hΩ hc φ).memLp_of_hasCompactSupport (boundaryTest_compact φ)
end HitAndRun.Sobolev
