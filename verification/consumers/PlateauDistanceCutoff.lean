module
import HitAndRun.Geometry.PlateauDistanceCutoffSequence
open MeasureTheory Set Filter Topology HitAndRun.Geometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]
example (Ω : Set E) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (plateauCutoffSequence (μ := μ) Ω n) :=
  plateauCutoffSequence_smooth Ω n
example {Ω : Set E} (hb : Bornology.IsBounded Ω) (n : ℕ) :
    HasCompactSupport (plateauCutoffSequence (μ := μ) Ω n) ∧
    tsupport (plateauCutoffSequence (μ := μ) Ω n) ⊆ Ω :=
  ⟨plateauCutoffSequence_compact hb n, plateauCutoffSequence_support hb n⟩
example (Ω : Set E) (n : ℕ) (x : E) :
    0 ≤ plateauCutoffSequence (μ := μ) Ω n x ∧ plateauCutoffSequence (μ := μ) Ω n x ≤ 1 :=
  ⟨plateauCutoffSequence_nonneg Ω n x, plateauCutoffSequence_le_one Ω n x⟩
example (Ω : Set E) (n : ℕ) (x : E) :
    interiorDistance Ω x * ‖fderiv ℝ (plateauCutoffSequence (μ := μ) Ω n) x‖ ≤ 4 :=
  plateauCutoffSequence_weighted_fderiv_le Ω n x
example {Ω : Set E} (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty) {x : E} (hx : x ∈ Ω) :
    Tendsto (fun n => plateauCutoffSequence (μ := μ) Ω n x) atTop (𝓝 1) :=
  plateauCutoffSequence_tendsto ho hc hx
example {Ω : Set E} (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty) {x : E} (hx : x ∈ Ω) :
    ∀ᶠ n in atTop, fderiv ℝ (plateauCutoffSequence (μ := μ) Ω n) x = 0 :=
  plateauCutoffSequence_fderiv_eventually_zero ho hc hx
#print axioms plateauDistance_lipschitz
#print axioms smoothPlateauDistance_eq_one
#print axioms smoothPlateauDistance_weighted_fderiv_le
#print axioms plateauCutoffSequence_smooth
#print axioms plateauCutoffSequence_compact
#print axioms plateauCutoffSequence_support
#print axioms plateauCutoffSequence_nonneg
#print axioms plateauCutoffSequence_le_one
#print axioms plateauCutoffSequence_weighted_fderiv_le
#print axioms plateauCutoffSequence_tendsto
#print axioms plateauCutoffSequence_fderiv_eventually_zero
#print axioms smoothPlateauDistance_fderiv_support
#print axioms smoothPlateauDistance_scaled_fderiv_le
