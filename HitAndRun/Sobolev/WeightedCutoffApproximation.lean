module
public import HitAndRun.Sobolev.WeightedCutoffLimit
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

theorem exists_weightedCutoff_approximants (hb : Bornology.IsBounded Ω)
    (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (h : Lp ℝ 2 (μ.restrict Ω)) (q : Lp E 2 (μ.restrict Ω))
    (hw : HasWeakFDerivOn ⟨Ω, ho⟩ h
      (fun x => innerSL ℝ ((interiorDistance Ω x)⁻¹ • q x)) μ) :
    ∃ u : ℕ → W12 μ Ω, ∃ w : ℕ → Lp E 2 (μ.restrict Ω),
      Tendsto (fun n => fnL (u n : H1Graph μ Ω)) atTop (𝓝 h) ∧
      Tendsto w atTop (𝓝 q) ∧
      ∀ n, (fun x => interiorDistance Ω x • gradL (u n : H1Graph μ Ω) x)
        =ᵐ[μ.restrict Ω] (w n : E → E) := by
  have hex (n : ℕ) := exists_weightedCutoff_W12 ho hc
    (plateauCutoffSequence_smooth (μ := μ) Ω n)
    (plateauCutoffSequence_compact hb n) (plateauCutoffSequence_support hb n)
    (Lp.memLp h) (Lp.memLp q) hw
  choose u huf hug using hex
  let w (n : ℕ) : Lp E 2 (μ.restrict Ω) :=
    (plateauWeightedField_memLp hb (Lp.memLp h) (Lp.memLp q) n).toLp _
  refine ⟨u, w, ?_, ?_, ?_⟩
  · have he (n : ℕ) : fnL (u n : H1Graph μ Ω) =
        (plateau_function_memLp hb (Lp.memLp h) n).toLp _ := by
      apply Lp.ext
      exact (huf n).trans (plateau_function_memLp hb (Lp.memLp h) n).coeFn_toLp.symm
    simp_rw [he]
    simpa only [Lp.toLp_coeFn] using plateau_function_toLp_tendsto hb ho hc (Lp.memLp h)
  · simpa only [Lp.toLp_coeFn] using
      plateauWeightedField_toLp_tendsto hb ho hc (Lp.memLp h) (Lp.memLp q)
  · intro n
    filter_upwards [hug n,
      (plateauWeightedField_memLp hb (Lp.memLp h) (Lp.memLp q) n).coeFn_toLp,
      ae_restrict_mem ho.measurableSet] with x hg hw' hx
    rw [hg]
    exact (weightedCutoffGradient_weighted_eq_plateau ho hc h q n hx).trans hw'.symm
end HitAndRun.Sobolev
