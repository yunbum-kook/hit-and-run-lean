module
public import HitAndRun.Analysis.BoundedPreimageLimit
public import HitAndRun.External.EllipticPDE.Sobolev.Graph

/-! Closedness under bounded H1 energy and strong L2 convergence, on the
actual weak-derivative graph rather than an arbitrary graph relation. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {Ω : Set E}

theorem exists_weak_graph_of_bounded_l2_limit
    (u : ℕ → W12 μ Ω) (f : Lp ℝ 2 (μ.restrict Ω)) {R : ℝ}
    (hR : 0 ≤ R) (hu : ∀ k, ‖u k‖ ≤ R)
    (hf : Filter.Tendsto (fun k => fnL (u k : H1Graph μ Ω)) Filter.atTop (nhds f)) :
    ∃ U : W12 μ Ω, fnL (U : H1Graph μ Ω) = f ∧ ‖U‖ ≤ R :=
  HitAndRun.Analysis.exists_bounded_preimage_of_tendsto
    (fnL.comp (W12 μ Ω).subtypeL) u f hR hu hf

/-- On an open domain, the graph function component determines its genuine weak gradient. -/
theorem weak_graph_fn_injective (hΩ : IsOpen Ω) :
    Function.Injective (fun U : W12 μ Ω => fnL (U : H1Graph μ Ω)) := by
  intro U V hfn
  change fnL (U : H1Graph μ Ω) = fnL (V : H1Graph μ Ω) at hfn
  apply Subtype.ext
  apply H1Graph.ext hfn
  apply Lp.ext
  have hU := (mem_W12_iff_hasWeakFDerivOn hΩ (U : H1Graph μ Ω)).mp U.property
  have hV := (mem_W12_iff_hasWeakFDerivOn hΩ (V : H1Graph μ Ω)).mp V.property
  rw [hfn] at hU
  exact (hU.ae_eq hV).mono fun x hx => innerSL_inj.mp hx


theorem weak_graph_norm_le_of_bounded_l2_limit (hΩ : IsOpen Ω)
    (u : ℕ → W12 μ Ω) (U : W12 μ Ω) {R : ℝ} (hR : 0 ≤ R)
    (hu : ∀ k, ‖u k‖ ≤ R)
    (hf : Filter.Tendsto (fun k => fnL (u k : H1Graph μ Ω)) Filter.atTop
      (nhds (fnL (U : H1Graph μ Ω)))) : ‖U‖ ≤ R := by
  obtain ⟨V, hV, hnorm⟩ := exists_weak_graph_of_bounded_l2_limit u
    (fnL (U : H1Graph μ Ω)) hR hu hf
  have he : V = U := weak_graph_fn_injective hΩ hV
  simpa only [he] using hnorm

end HitAndRun.Sobolev
