module
public import HitAndRun.Sobolev.VectorBoundaryLimit
public import HitAndRun.External.EllipticPDE.Analysis.Mollifier

/-! A finite family of genuine tests fits a common inner parallel domain. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Set E} {ι : Type*} [Fintype ι]

theorem finite_test_support_distance_pos (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (φ : ι → testFunctions Ω) :
    ∃ e : ℝ, 0 < e ∧ ∀ i x, x ∈ tsupport (φ i : E → ℝ) → e ≤ interiorDistance Ω x := by
  classical
  have hs (s : Finset ι) : ∃ e : ℝ, 0 < e ∧
      ∀ i ∈ s, ∀ x ∈ tsupport (φ i : E → ℝ), e ≤ interiorDistance Ω x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨a, ha, ham⟩ := test_support_distance_pos ho hc (φ i)
      obtain ⟨b, hb, hbm⟩ := ih
      refine ⟨min a b, lt_min ha hb, ?_⟩
      intro j hj x hx
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (min_le_left _ _).trans (ham x hx)
      · exact (min_le_right _ _).trans (hbm j hj x hx)
  obtain ⟨e, he, hm⟩ := hs Finset.univ
  exact ⟨e, he, fun i => hm i (Finset.mem_univ i)⟩

def innerTest (φ : testFunctions Ω) {r : ℝ}
    (hs : ∀ x ∈ tsupport (φ : E → ℝ), r < interiorDistance Ω x) :
    testFunctions (innerDomain Ω r) :=
  ⟨φ, φ.2.1, φ.2.2.1, hs⟩

theorem innerTest_coe (φ : testFunctions Ω) {r : ℝ}
    (hs : ∀ x ∈ tsupport (φ : E → ℝ), r < interiorDistance Ω x) :
    (innerTest φ hs : E → ℝ) = φ := rfl
end HitAndRun.Sobolev
