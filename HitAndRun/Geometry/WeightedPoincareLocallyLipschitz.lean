module
public import HitAndRun.Geometry.WeightedPoincareRadialBound
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Source S07 assumes local Lipschitz regularity on the whole ambient space.
Consequently, its derivative is uniformly bounded on every bounded body. -/
theorem locallyLipschitz_fderiv_bounded {f : E → ℝ} (hf : LocallyLipschitz f)
    {K : Set E} (hb : Bornology.IsBounded K) :
    ∃ C : ℝ≥0, ∀ x ∈ K, ‖fderiv ℝ f x‖ ≤ C := by
  obtain ⟨R, hR⟩ := hb.subset_ball (0 : E)
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : E) R) (hf.locallyLipschitzOn (s := closedBall 0 R))
  refine ⟨C, fun x hx => norm_fderiv_le_of_lipschitzOn ℝ ?_ hC⟩
  exact mem_of_superset (isOpen_ball.mem_nhds (hR hx)) ball_subset_closedBall

/-- Rademacher applies on an ambient neighborhood of the body, not merely
along selected rays. -/
theorem locallyLipschitz_ae_differentiableOn (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → ℝ} (hf : LocallyLipschitz f) {K : Set E}
    (hb : Bornology.IsBounded K) (hm : MeasurableSet K) :
    ∀ᵐ x ∂μ.restrict K, DifferentiableAt ℝ f x := by
  obtain ⟨R, hR⟩ := hb.subset_ball (0 : E)
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : E) R) (hf.locallyLipschitzOn (s := closedBall 0 R))
  have hae := hC.ae_differentiableWithinAt_of_mem (μ := μ)
  rw [ae_restrict_iff' hm]
  filter_upwards [hae] with x hx hK
  exact (hx (ball_subset_closedBall (hR hK))).differentiableAt
    (mem_of_superset (isOpen_ball.mem_nhds (hR hK)) ball_subset_closedBall)

/-- Finite Lp norms of the actual derivative follow from the source hypotheses;
they are not extra endpoint assumptions. -/
theorem locallyLipschitz_fderiv_memLp (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {f : E → ℝ} (hf : LocallyLipschitz f) {K : Set E}
    (hb : Bornology.IsBounded K) (hm : MeasurableSet K) (p : ℝ≥0∞) :
    MemLp (fun x => ‖fderiv ℝ f x‖) p (μ.restrict K) := by
  have hfinite : μ K < ∞ := lt_of_le_of_lt (measure_mono subset_closure)
    hb.isCompact_closure.measure_lt_top
  letI : Fact (μ K < ∞) := ⟨hfinite⟩
  obtain ⟨C, hC⟩ := locallyLipschitz_fderiv_bounded hf hb
  apply MemLp.of_bound ((measurable_fderiv ℝ f).norm.aestronglyMeasurable) C
  filter_upwards [ae_restrict_mem hm] with x hx
  simpa only [norm_norm] using hC x hx
end HitAndRun.Geometry
