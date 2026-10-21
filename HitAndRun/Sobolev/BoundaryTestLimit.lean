module
public import HitAndRun.Sobolev.BoundaryTest
public import HitAndRun.Geometry.InnerDomain
public import HitAndRun.Analysis.CompactQuotientLimit

/-! Interior-domain boundary coefficients converge on genuine compact tests.
All distance statements use arbitrary open domains, not convexity. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry Set Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

theorem test_support_distance_pos (hΩ : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (φ : testFunctions Ω) :
    ∃ e : ℝ, 0 < e ∧ ∀ x ∈ tsupport (φ : E → ℝ), e ≤ interiorDistance Ω x := by
  by_cases hs : (tsupport (φ : E → ℝ)).Nonempty
  · obtain ⟨x, hx, hmin⟩ := φ.2.2.1.exists_isMinOn hs
      (interiorDistance_lipschitz Ω).continuous.continuousOn
    refine ⟨interiorDistance Ω x, ?_, fun y hy => hmin hy⟩
    exact (hΩ.isClosed_compl.notMem_iff_infDist_pos hc).mp (by simpa using φ.2.2.2 hx)
  · exact ⟨1, by norm_num, fun x hx => False.elim (hs ⟨x, hx⟩)⟩

theorem innerDomain_distance_upper (hc : Ωᶜ.Nonempty) {r : ℝ} (hr : 0 ≤ r) (x : E) :
    interiorDistance (innerDomain Ω r) x ≤ interiorDistance Ω x :=
  Metric.infDist_le_infDist_of_subset
    (Set.compl_subset_compl.mpr (innerDomain_subset Ω hr)) hc

theorem innerDomain_distance_tendsto (hc : Ωᶜ.Nonempty) {r : ℕ → ℝ}
    (hr : ∀ k, 0 ≤ r k) (ht : Tendsto r atTop (𝓝 0)) (x : E) :
    Tendsto (fun k => interiorDistance (innerDomain Ω (r k)) x) atTop
      (𝓝 (interiorDistance Ω x)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun k => interiorDistance Ω x - r k) (h := fun _ => interiorDistance Ω x)
  · simpa using tendsto_const_nhds.sub ht
  · exact tendsto_const_nhds
  · exact fun k => innerDomain_distance_lower hc (hr k) x
  · exact fun k => innerDomain_distance_upper hc (hr k) x

theorem boundaryTest_inner_tendsto (hΩ : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (φ : testFunctions Ω) {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k)
    (ht : Tendsto r atTop (𝓝 0)) (x : E) :
    Tendsto (fun k => (φ : E → ℝ) x / interiorDistance (innerDomain Ω (r k)) x)
      atTop (𝓝 (boundaryTest φ x)) := by
  by_cases hx : (φ : E → ℝ) x = 0
  · simpa [hx, boundaryTest] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · have hm : x ∈ Ω := φ.2.2.2 (subset_closure hx)
    have hp : 0 < interiorDistance Ω x :=
      (hΩ.isClosed_compl.notMem_iff_infDist_pos hc).mp (by simpa using hm)
    exact tendsto_const_nhds.div (innerDomain_distance_tendsto hc hr ht x) hp.ne'
theorem boundaryTest_inner_sq_tendsto (hc : Ωᶜ.Nonempty)
    (φ : testFunctions Ω) {e : ℝ} (he : 0 < e)
    (hmargin : ∀ x ∈ tsupport (φ : E → ℝ), e ≤ interiorDistance Ω x)
    {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) (hrb : ∀ k, r k ≤ e / 2)
    (ht : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖(φ : E → ℝ) x / interiorDistance (innerDomain Ω (r k)) x -
      boundaryTest φ x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  apply HitAndRun.Analysis.integral_sq_quotient_sub_tendsto
    φ.2.1.continuous φ.2.2.1 (interiorDistance_lipschitz Ω).continuous
    (fun k => (interiorDistance_lipschitz (innerDomain Ω (r k))).continuous)
    (half_pos he)
  · intro x hx
    have := hmargin x (subset_closure hx)
    linarith
  · intro k x hx
    have hm := hmargin x (subset_closure hx)
    have hl := innerDomain_distance_lower hc (hr k) x
    linarith [hrb k]
  · exact innerDomain_distance_tendsto hc hr ht

end HitAndRun.Sobolev
