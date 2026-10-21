import HitAndRun.Sobolev.Divergence
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Nontriviality of the genuine test carrier follows from domain geometry. -/
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

/-- An interior smooth bump gives a nonzero zero-trace graph. -/
theorem h01_nontrivial (ho : IsOpen Ω) (hne : Ω.Nonempty) : Nontrivial (H01 μ Ω) := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨φ, hs, hc, hd, _, hxφ⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (ho.mem_nhds hx)
  let ψ : testFunctions Ω := ⟨φ, hd, hc, hs⟩
  let u : H01 μ Ω := ⟨testGraphₗ μ Ω ψ, testGraphₗ_mem_H01 ψ⟩
  have hu : u ≠ 0 := by
    intro hu
    have hz : fnCls μ Ω ψ = 0 := by
      have hh := congrArg (fun w : H01 μ Ω => fnL (w : H1Graph μ Ω)) hu
      simpa [u] using hh
    have he : φ =ᵐ[μ.restrict Ω] (fun _ => (0 : ℝ)) := by
      have hh := (coeFn_fnCls (μ := μ) ψ).symm
      rw [hz] at hh
      exact hh.trans (Lp.coeFn_zero _ _ _)
    have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq he ho hd.continuous.continuousOn
      continuous_const.continuousOn
    have hzero := heq hx
    rw [hxφ] at hzero
    exact one_ne_zero hzero
  exact ⟨⟨u, 0, hu⟩⟩

/-- Poincaré injectivity transports nontriviality to the exact gradient-norm carrier. -/
theorem gradientSpace_nontrivial (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hb : Bornology.IsBounded Ω) : Nontrivial (gradientSpace μ Ω) := by
  letI := h01_nontrivial (μ := μ) ho hne
  exact (gradientEquiv (μ := μ) hb).injective.nontrivial

/-- The finite Hilbert product of actual gradients is nontrivial on a nonempty open domain. -/
theorem vectorField_nontrivial {n : ℕ} [NeZero n]
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hb : Bornology.IsBounded Ω) : Nontrivial (VectorField μ Ω) := by
  letI := gradientSpace_nontrivial (μ := μ) ho hne hb
  infer_instance
end HitAndRun.Sobolev
