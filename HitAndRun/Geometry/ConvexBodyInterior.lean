module
public import Mathlib.Analysis.Convex.Measure
public import HitAndRun.Sobolev.UniformMeasure
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Convex bodies and their interiors agree outside their null boundary. -/
theorem convex_ae_eq_interior (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hc : Convex ℝ K) : K =ᵐ[μ] interior K := by
  have hn : ∀ᵐ x ∂μ, x ∉ frontier K := by
    rw [ae_iff]
    simpa using hc.addHaar_frontier μ
  filter_upwards [hn] with x hx
  apply propext
  constructor
  · intro hK
    by_contra hi
    exact hx ⟨subset_closure hK, hi⟩
  · exact fun hi => interior_subset hi

theorem convex_restrict_interior (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hc : Convex ℝ K) : μ.restrict K = μ.restrict (interior K) :=
  Measure.restrict_congr_set (convex_ae_eq_interior μ hc)

/-- Full dimension is needed for equality of frontiers, not for the null-boundary result. -/
theorem convex_frontier_interior {K : Set E} (hc : Convex ℝ K)
    (hi : (interior K).Nonempty) : frontier (interior K) = frontier K := by
  rw [frontier, frontier, interior_interior,
    hc.closure_interior_eq_closure_of_nonempty_interior hi]

theorem convex_infDist_frontier_interior {K : Set E} (hc : Convex ℝ K)
    (hi : (interior K).Nonempty) (x : E) :
    infDist x (frontier (interior K)) = infDist x (frontier K) := by
  rw [convex_frontier_interior hc hi]

/-- The same open inscribed balls, at arbitrary centers, belong to the body and its interior. -/
theorem ball_subset_interior_iff {K : Set E} {c : E} {r : ℝ} :
    ball c r ⊆ interior K ↔ ball c r ⊆ K :=
  ⟨fun h => h.trans interior_subset, fun h => isOpen_ball.subset_interior_iff.mpr h⟩

theorem convex_uniformMeasure_interior {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hc : Convex ℝ K) :
    Sobolev.uniformMeasure K = Sobolev.uniformMeasure (interior K) := by
  unfold Sobolev.uniformMeasure
  rw [measure_congr (convex_ae_eq_interior volume hc), convex_restrict_interior volume hc]

theorem convex_normalizedAmbient_interior {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hc : Convex ℝ K) :
    Sobolev.normalizedAmbient K = Sobolev.normalizedAmbient (interior K) := by
  unfold Sobolev.normalizedAmbient
  rw [measure_congr (convex_ae_eq_interior volume hc)]
end HitAndRun.Geometry
