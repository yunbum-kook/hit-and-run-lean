module
public import CvxBody.Analysis.NeedleLogConcave
public import CvxBody.Analysis.RayDisintegrationNeedle
public import CvxBody.Analysis.EndsNull
public import CvxBody.Analysis.ConcentrationL1

@[expose] public section


/-!
# Milman's converse, Poincaré case: concentration implies a Poincaré inequality for log-concave measures

P02.2 (second half of `bg:concentration`, the exponential-concentration statement; [Milman12,
Thm 5.2]) proved through Klartag's guided needle decomposition. The chain is:

* `needle_decomposition_exists` (Theorem N of the blueprint): for a log-concave probability density
  `ρ` with finite first moment and a measurable `S` with `0 < μ S < 1`, a maximizer `u` of the
  `L¹` Kantorovich problem for `1_S − μ S` (`LipschitzMaximizer.lean`) has ends of the transport rays
  of measure zero (`RayEnds.lean`, via Alexandrov's theorem on the semiconcave envelope), the mass
  balance holds on ray-saturated sets (`MassBalance.lean`), `μ` disintegrates along the rays
  (`RayDisintegration.lean`), and the needle densities are log-concave (`NeedleLogConcave.lean`,
  via the shift maps of `RayShift.lean` and the area formula);
* `isPoincareBound_of_concentration_logConcave`: with `∫ |v − ∫ v| ≤ s` for all 1-Lipschitz `v`,
  `cheeger_of_needle_decomposition` (one-dimensional isoperimetry `LogConcave1D.lean`, Markov and
  Fatou) gives the Cheeger inequality, and `isPoincareBound_of_cheeger` the Poincaré constant
  `4 (256 s)²`;
* `isPoincareBound_of_exp_concentration`: the manuscript's form of the hypothesis (exponential
  tails around a center `b_v`).
Scope: the log-concave density is a function on all of `ℝⁿ` (full-dimensional support), as for the
manuscript's lifted measure `σ`; measures with lower-dimensional convex support need a reduction to the
affine hull, not written.
-/

open MeasureTheory
open OAI.LeanBlast.KLS
open CvxBody.Geometry

namespace CvxBody

variable {n : ℕ}

/-- **Theorem N**: a guided needle decomposition exists for every measurable `S` of measure in
`(0,1)` of a log-concave probability measure with finite first moment. -/
theorem needle_decomposition_exists {ρ : Space n → ℝ} (hρ : IsLogConcaveFunction ρ)
    (hρm : Measurable ρ)
    [hprob : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (ρ x))]
    (hμ : Integrable (fun x : Space n => ‖x‖) (volume.withDensity fun x => ENNReal.ofReal (ρ x)))
    {S : Set (Space n)} (hS : MeasurableSet S)
    (h0 : 0 < (volume.withDensity fun x => ENNReal.ofReal (ρ x)) S)
    (h1 : (volume.withDensity fun x => ENNReal.ofReal (ρ x)) S < 1) :
    ∃ u, NeedleDecomposition (volume.withDensity fun x => ENNReal.ofReal (ρ x)) S u := by
  set μ : Measure (Space n) := volume.withDensity fun x => ENNReal.ofReal (ρ x) with hμdef
  have hac : μ ≪ volume := withDensity_absolutelyContinuous _ _
  obtain ⟨u, hmax, -, hStrain, -⟩ := exists_maximizer_mass_balance_of_ac μ hac hμ hS h0 h1
  have hu := hmax.1
  have hEnds : μ (Ends u) = 0 := measure_ends_eq_zero hac hu
  have := isProbabilityMeasure_rayBase hu hStrain (μ := μ)
  refine ⟨u, needleDecomposition_of_rayDisintegration μ hμ hS h0 h1 hmax hEnds ?_⟩
  exact NeedleLC.needleDensity_logConcave hu hρ hρm (q := rayBase μ u) (κ := rayKernel μ u)
    (fun A B hA hB => isRayDisintegration_rayKernel (μ := μ) hu A hA B hB)

/-- **Milman's converse (Poincaré case), `L¹` form**: a log-concave probability measure for which
every 1-Lipschitz function is integrable with `∫ |v − ∫ v| ≤ s` has Poincaré constant at most
`4 (256 s)²`. -/
theorem isPoincareBound_of_concentration_logConcave {ρ : Space n → ℝ}
    (hρ : IsLogConcaveFunction ρ) (hρm : Measurable ρ)
    [hprob : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (ρ x))]
    {s : ℝ} (hs : 0 < s)
    (hconc : ∀ v : Space n → ℝ, LipschitzWith 1 v →
      Integrable v (volume.withDensity fun x => ENNReal.ofReal (ρ x)) ∧
        ∫ x, |v x - ∫ y, v y ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x))|
          ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x)) ≤ s) :
    IsPoincareBound (volume.withDensity fun x => ENNReal.ofReal (ρ x)) (4 * (256 * s) ^ 2) := by
  have hμ : Integrable (fun x : Space n => ‖x‖) (volume.withDensity fun x => ENNReal.ofReal (ρ x)) :=
    (hconc _ lipschitzWith_one_norm).1
  exact isPoincareBound_of_concentration _ (withDensity_absolutelyContinuous _ _) hs
    (fun A hA h0 h1 => needle_decomposition_exists hρ hρm hμ hA h0 h1) hconc

/-- The manuscript's form of the hypothesis of `bg:concentration` (exponential concentration with
centers `b_v`): `μ(|v − b_v| > t) ≤ C exp(−c t / s)` for every 1-Lipschitz `v`. -/
theorem isPoincareBound_of_exp_concentration {ρ : Space n → ℝ}
    (hρ : IsLogConcaveFunction ρ) (hρm : Measurable ρ)
    [hprob : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (ρ x))]
    {C c s : ℝ} (hC : 0 < C) (hc : 0 < c) (hs : 0 < s)
    (hconc : ∀ v : Space n → ℝ, LipschitzWith 1 v → ∃ b : ℝ, ∀ t : ℝ, 0 ≤ t →
      (volume.withDensity fun x => ENNReal.ofReal (ρ x)) {x | t < |v x - b|} ≤
        ENNReal.ofReal (C * Real.exp (-c * t / s))) :
    IsPoincareBound (volume.withDensity fun x => ENNReal.ofReal (ρ x))
      (4 * (256 * (2 * C / c * s)) ^ 2) := by
  refine isPoincareBound_of_concentration_logConcave hρ hρm (by positivity) fun v hv => ?_
  obtain ⟨b, hb⟩ := hconc v hv
  exact integral_abs_sub_integral_le_of_exp_tail hv.continuous.measurable hC hc hs hb

end CvxBody
