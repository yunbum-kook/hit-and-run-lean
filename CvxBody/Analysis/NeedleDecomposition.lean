module
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import CvxBody.Analysis.Cheeger
public import CvxBody.Analysis.LogConcave1D

@[expose] public section


/-!
# Needle decompositions, concentration, and the Poincaré inequality

Work package WP-A of `docs/part1/P02-NEEDLE-BLUEPRINT.md` (lemma L3 and Corollary C): the
assembly "needle decomposition + concentration of one Lipschitz function ⇒ Cheeger inequality ⇒
Poincaré inequality", proved for *arbitrary* decompositions.

* `NeedleDecomposition μ S u` is the output of Klartag's guided needle decomposition of
  `f = 1_S - μ(S)` (Theorem N of the blueprint), as a `Prop`.  Its *existence* (Theorem N) is **not**
  proved here; it is the content of a separate work package.
* `cheeger_of_needle_decomposition` (L3) is an unconditional theorem about any such object: if
  `D : NeedleDecomposition μ S u` and `∫ |u - ∫ u| dμ ≤ s`, then
  `ν⁺(S) ≥ min (μ S) (1 - μ S) / (256 s)`.  Constants: Markov puts at least half of the needles
  in `B = {E_{ν_ω}|u - c| ≤ 2s}`; on such a needle `ν_ω{|u - c| > 8s} ≤ 1/4`, and the
  one-dimensional isoperimetric inequality (`isoperimetry_log_concave_1D`, constant `1/16` at
  radius `r = 8s`) gives `1/(128 s)`; the factor `1/2` is `q(B)`.
* `isoperimetry` along a single needle is `needleMeasure_isoperimetry`; the thickening of `S` in
  `ℝⁿ` contains the image of the thickening of `x_ω⁻¹ S` because `t ↦ o_ω + t θ_ω` is an isometry
  for `‖θ_ω‖ = 1`.  Fatou's lemma is applied along the filter `𝓝[>] 0` (Mathlib's
  `lintegral_liminf_le` holds for countably generated filters).
* `isPoincareBound_of_concentration` (Corollary C): **this theorem depends on Theorem N** through
  its hypothesis `hN`, which asks for a needle decomposition of every measurable `A` with
  `0 < μ A < 1`.  It is stated in this form so that it can be applied to the guide `u` produced by
  `needle_decomposition_exists` (`MilmanPoincare.lean`), which discharges `hN` for every log-concave
  probability density with finite first moment (`isPoincareBound_of_concentration_logConcave`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Metric
open OAI.LeanBlast.KLS
open scoped ENNReal NNReal

namespace CvxBody

variable {n : ℕ}

/-- The measure on a line with log-concave density `h`, transported to the needle `t ↦ o + tθ`. -/
noncomputable def needleMeasure (o θ : Space n) (h : ℝ → ℝ) : Measure (Space n) :=
  (volume.withDensity fun t => ENNReal.ofReal (h t)).map (fun t : ℝ => o + t • θ)

section SingleNeedle

variable {o θ : Space n} {h : ℝ → ℝ}

/-- `t ↦ o + tθ` is an isometry (in particular `1`-Lipschitz) for a unit vector `θ`. -/
theorem lipschitzWith_needle (hθ : ‖θ‖ = 1) : LipschitzWith 1 (fun t : ℝ => o + t • θ) := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  simp [dist_eq_norm, ← sub_smul, norm_smul, hθ]

/-- The `ε`-thickening in `ℝ` of `x⁻¹ S` maps into the `ε`-thickening of `S`, `x t = o + tθ`. -/
theorem thickening_preimage_subset_needle (hθ : ‖θ‖ = 1) {ε : ℝ} (S : Set (Space n)) :
    thickening ε ((fun t : ℝ => o + t • θ) ⁻¹' S) ⊆
      (fun t : ℝ => o + t • θ) ⁻¹' thickening ε S := by
  intro t ht
  rw [Set.mem_preimage, mem_thickening_iff]
  rw [mem_thickening_iff] at ht
  obtain ⟨z, hz, hd⟩ := ht
  refine ⟨o + z • θ, hz, lt_of_le_of_lt ?_ hd⟩
  simpa using (lipschitzWith_needle (o := o) hθ).dist_le_mul t z

/-- The needle measure of a measurable set is the density measure of its preimage. -/
theorem needleMeasure_apply (hθ : ‖θ‖ = 1) {A : Set (Space n)} (hA : MeasurableSet A) :
    needleMeasure o θ h A = (volume.withDensity fun t => ENNReal.ofReal (h t))
      ((fun t : ℝ => o + t • θ) ⁻¹' A) := by
  unfold needleMeasure
  exact Measure.map_apply (lipschitzWith_needle hθ).continuous.measurable hA

/-- On the support of the density, `u` is the arclength coordinate (almost everywhere). -/
theorem ae_u_needle (hm : Measurable h) {u : Space n → ℝ}
    (hu : ∀ t, h t ≠ 0 → u (o + t • θ) = t) :
    ∀ᵐ t ∂(volume.withDensity fun t => ENNReal.ofReal (h t)), u (o + t • θ) = t := by
  rw [ae_withDensity_iff (f := fun t => ENNReal.ofReal (h t)) (ENNReal.measurable_ofReal.comp hm)]
  refine Filter.Eventually.of_forall fun t ht => hu t ?_
  intro h0
  apply ht
  simp [h0]

/-- **One needle.**  If the density `h` (log-concave, `∫ h = 1`) is spread so that the needle
measure of `{x | r < |u x - c|}` is at most `1/4`, and `u (o + tθ) = t` on `{h ≠ 0}`, then the outer
Minkowski content of every measurable `S` along the needle satisfies
`(1/16)/r · min (ν S) (1 - ν S) ≤ ν⁺(S)`.  This is `isoperimetry_log_concave_1D` transported along
the isometry `t ↦ o + tθ`. -/
theorem needleMeasure_isoperimetry (hm : Measurable h) (hlc : IsLogConcaveFunction h)
    (h1 : ∫ t, h t = 1) (hθ : ‖θ‖ = 1) {u : Space n → ℝ} (hu : ∀ t, h t ≠ 0 → u (o + t • θ) = t)
    (hum : Measurable u) {c r : ℝ} (hr : 0 < r)
    (hspread : needleMeasure o θ h {x | r < |u x - c|} ≤ 1 / 4) {S : Set (Space n)}
    (hS : MeasurableSet S) :
    ENNReal.ofReal (1 / 16 / r) * min (needleMeasure o θ h S) (1 - needleMeasure o θ h S) ≤
      liminf (fun ε : ℝ => (needleMeasure o θ h (thickening ε S) - needleMeasure o θ h S) /
        ENNReal.ofReal ε) (𝓝[>] 0) := by
  set x : ℝ → Space n := fun t => o + t • θ with hx
  have hxm : Measurable x := (lipschitzWith_needle (o := o) hθ).continuous.measurable
  set ρ : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (h t)
  have hae := ae_u_needle (o := o) (θ := θ) hm hu
  have hset : x ⁻¹' {x | r < |u x - c|} =ᵐ[volume.withDensity ρ] {t : ℝ | r < |t - c|} := by
    refine (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hae] with t ht
    simp [hx, ht]
  have hS' : MeasurableSet (x ⁻¹' S) := hxm hS
  have hspread' : CvxBody.LogConcave1D.densityMeasure h {t : ℝ | r < |t - c|} ≤ 1 / 4 := by
    rw [← measure_congr hset, ← needleMeasure_apply hθ (measurableSet_lt measurable_const
      ((hum.sub_const c).abs))]
    exact hspread
  have hint : Integrable h := MeasureTheory.integrable_of_integral_eq_one h1
  have h1d := CvxBody.LogConcave1D.isoperimetry_log_concave_1D hlc hm hint h1 hr hspread' hS'
  have e1 : needleMeasure o θ h S = CvxBody.LogConcave1D.densityMeasure h (x ⁻¹' S) :=
    needleMeasure_apply hθ hS
  rw [e1]
  refine h1d.trans (liminf_le_liminf ?_)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεo : IsOpen (thickening ε S) := isOpen_thickening
  have hmono : CvxBody.LogConcave1D.densityMeasure h (thickening ε (x ⁻¹' S)) ≤
      needleMeasure o θ h (thickening ε S) := by
    rw [needleMeasure_apply hθ hεo.measurableSet]
    exact measure_mono (thickening_preimage_subset_needle hθ S)
  gcongr

end SingleNeedle

/-- **Klartag's guided needle decomposition for `f = 1_S - μ(S)`** (Theorem N of
`docs/part1/P02-NEEDLE-BLUEPRINT.md`), with guide `u`, stated as a property of the triple
`(μ, S, u)`.  This declaration only *states* what such a decomposition is; its existence is not
asserted anywhere here.

`NeedleDecomposition μ S u` says: `u` is `1`-Lipschitz, and there are a standard Borel probability
space `(Ω, q)`, a Markov kernel `ν : Ω → Measure (Space n)` and Borel maps `θ, o : Ω → Space n` with

1. (disintegration) `μ A = ∫ ν ω A dq(ω)` for every measurable `A`;
2. (needles) for `q`-a.e. `ω`: `θ ω` is a unit vector and there is a measurable log-concave
   `h : ℝ → ℝ` with `∫ h = 1` such that `ν ω` is the image of `h(t) dt` under `t ↦ o ω + t • θ ω`,
   and `u (o ω + t • θ ω) = t` whenever `h t ≠ 0` (so `u` is the arclength coordinate on the
   needle; the interval `J_ω` of the blueprint is `{h ≠ 0}`, which is an interval by
   log-concavity);
3. (mass balance) `ν ω S = μ S` for `q`-a.e. `ω`, i.e. `∫ (1_S - μ S) dν ω = 0`.

Differences from the blueprint: measurability of `h` is recorded (as in `IsLogConcaveDensity`), the
unit-vector condition on `θ` is required only `q`-a.e., and `S` is not required to be measurable
(measurability is a hypothesis of the lemmas).  `StandardBorelSpace Ω` is part of the data because
that is what the existence proof (disintegration via `condKernel`) produces; the assembly below
does not use it. -/
def NeedleDecomposition (μ : Measure (Space n)) (S : Set (Space n)) (u : Space n → ℝ) : Prop :=
  LipschitzWith 1 u ∧
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (q : Measure Ω)
    (_ : IsProbabilityMeasure q) (ν : Kernel Ω (Space n)) (_ : IsMarkovKernel ν)
    (θ o : Ω → Space n),
    Measurable θ ∧ Measurable o ∧
    (∀ A, MeasurableSet A → μ A = ∫⁻ ω, ν ω A ∂q) ∧
    (∀ᵐ ω ∂q, ‖θ ω‖ = 1 ∧ ∃ h : ℝ → ℝ, Measurable h ∧ IsLogConcaveFunction h ∧
      ∫ t, h t = 1 ∧
      ν ω = (volume.withDensity fun t => ENNReal.ofReal (h t)).map (fun t : ℝ => o ω + t • θ ω) ∧
      ∀ t, h t ≠ 0 → u (o ω + t • θ ω) = t) ∧
    (∀ᵐ ω ∂q, ν ω S = μ S)


/-- Disintegration (1) for nonnegative measurable functions. -/
theorem lintegral_eq_of_disintegration {μ : Measure (Space n)} {Ω : Type} [MeasurableSpace Ω]
    {q : Measure Ω} {ν : Kernel Ω (Space n)}
    (hd : ∀ A, MeasurableSet A → μ A = ∫⁻ ω, ν ω A ∂q) {f : Space n → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ x, f x ∂μ = ∫⁻ ω, ∫⁻ x, f x ∂(ν ω) ∂q := by
  have : μ = q.bind ν := Measure.ext fun A hA => by
    rw [hd A hA, Measure.bind_apply hA ν.aemeasurable]
  rw [this, Measure.lintegral_bind ν.aemeasurable hf.aemeasurable]

/-- **Needle decomposition + `L¹` concentration of the guide ⇒ Cheeger inequality for `S`**
(lemma L3).  For any `D : NeedleDecomposition μ S u` with `u ∈ L¹(μ)` and
`∫ |u - ∫ u| dμ ≤ s`, one has `min (μ S) (1 - μ S) / (256 s) ≤ ν⁺(S)`.  Unconditional: no
existence statement for needle decompositions is assumed. -/
theorem cheeger_of_needle_decomposition (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    {S : Set (Space n)} (hS : MeasurableSet S) {u : Space n → ℝ} (D : NeedleDecomposition μ S u)
    {s : ℝ} (hs : 0 < s) (hu : Integrable u μ)
    (hR : ∫ x, |u x - ∫ y, u y ∂μ| ∂μ ≤ s) :
    ENNReal.ofReal (1 / (256 * s)) * min (μ S) (1 - μ S) ≤ minkowskiContent μ S := by
  obtain ⟨hlip, Ω, mΩ, sb, q, pq, ν, mk, θ, o, hθm, hom, hd, hn, hm⟩ := D
  set c : ℝ := ∫ y, u y ∂μ with hc
  have hum : Measurable u := hlip.continuous.measurable
  set K : ℝ≥0∞ := ENNReal.ofReal (1 / 16 / (8 * s)) * min (μ S) (1 - μ S) with hK
  have hfun : Measurable fun x => ENNReal.ofReal |u x - c| :=
    ENNReal.measurable_ofReal.comp (hum.sub_const c).abs
  set g : Ω → ℝ≥0∞ := fun ω => ∫⁻ x, ENNReal.ofReal |u x - c| ∂(ν ω) with hg
  have hgm : Measurable g := hfun.lintegral_kernel
  have hgint : ∫⁻ ω, g ω ∂q ≤ ENNReal.ofReal s := by
    have h1 := lintegral_eq_of_disintegration hd hfun
    have h2 : ∫⁻ x, ENNReal.ofReal |u x - c| ∂μ = ENNReal.ofReal (∫ x, |u x - c| ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal (hu.sub (integrable_const c)).abs
        (Filter.Eventually.of_forall fun x => abs_nonneg _)).symm
    calc ∫⁻ ω, g ω ∂q = ∫⁻ x, ENNReal.ofReal |u x - c| ∂μ := h1.symm
      _ = _ := h2
      _ ≤ _ := ENNReal.ofReal_le_ofReal hR
  set B : Set Ω := {ω | g ω ≤ ENNReal.ofReal (2 * s)} with hB
  have hBm : MeasurableSet B := measurableSet_le hgm measurable_const
  have hqB : 2⁻¹ ≤ q B := by
    have h1 : ENNReal.ofReal (2 * s) * q Bᶜ ≤ ENNReal.ofReal s := by
      refine le_trans ?_ hgint
      refine le_trans ?_ (mul_meas_ge_le_lintegral₀ hgm.aemeasurable (ENNReal.ofReal (2 * s)))
      gcongr
      intro ω hω
      simp only [hB, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
      exact hω.le
    have hs0 : ENNReal.ofReal s ≠ 0 := by simpa using hs
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat] at h1
    have h2 : ENNReal.ofReal s * (2 * q Bᶜ) ≤ ENNReal.ofReal s * 1 := by
      rw [mul_one, ← mul_assoc, mul_comm (ENNReal.ofReal s)]
      exact h1
    have h3 : 2 * q Bᶜ ≤ 1 := (ENNReal.mul_le_mul_iff_right hs0 ENNReal.ofReal_ne_top).1 h2
    have h4 : q Bᶜ ≤ 2⁻¹ := by
      rw [ENNReal.le_inv_iff_mul_le]
      simpa [mul_comm] using h3
    have h5 : q B = 1 - q Bᶜ := by
      simpa using prob_compl_eq_one_sub hBm.compl
    rw [h5]
    calc (2⁻¹ : ℝ≥0∞) = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
      _ ≤ 1 - q Bᶜ := tsub_le_tsub_left h4 _
  have hpt : ∀ᵐ ω ∂q, ω ∈ B → K ≤ liminf (fun ε : ℝ =>
      (ν ω (thickening ε S) - μ S) / ENNReal.ofReal ε) (𝓝[>] 0) := by
    filter_upwards [hn, hm] with ω hω hmω hωB
    obtain ⟨hθ1, h, hhm, hlc, h1, hνω, hu'⟩ := hω
    have hνω' : ν ω = needleMeasure (o ω) (θ ω) h := hνω
    have hC : ν ω {x | 8 * s < |u x - c|} ≤ 1 / 4 := by
      have h1 : ENNReal.ofReal (8 * s) * ν ω {x | 8 * s < |u x - c|} ≤ ENNReal.ofReal (2 * s) := by
        refine le_trans ?_ hωB
        refine le_trans ?_ (mul_meas_ge_le_lintegral₀ hfun.aemeasurable (ENNReal.ofReal (8 * s)))
        refine mul_le_mul_right (measure_mono fun x hx => ?_) _
        exact ENNReal.ofReal_le_ofReal (le_of_lt hx)
      have h2 : ENNReal.ofReal (8 * s) * ν ω {x | 8 * s < |u x - c|} ≤
          ENNReal.ofReal (8 * s) * (1 / 4) := by
        refine h1.trans (le_of_eq ?_)
        rw [← ENNReal.ofReal_ofNat 4, one_div, ← ENNReal.ofReal_inv_of_pos (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      exact (ENNReal.mul_le_mul_iff_right (by simpa using by positivity) ENNReal.ofReal_ne_top).1 h2
    have key := needleMeasure_isoperimetry (o := o ω) (θ := θ ω) hhm hlc h1 hθ1 hu' hum
      (c := c) (r := 8 * s) (by positivity) (by rw [← hνω']; exact hC) hS
    rw [← hνω', hmω] at key
    exact key
  have hψm : ∀ ε : ℝ, Measurable fun ω =>
      (ν ω (thickening ε S) - μ S) / ENNReal.ofReal ε := fun ε => by
    simp only [div_eq_mul_inv]
    exact ((ν.measurable_coe isOpen_thickening.measurableSet).sub measurable_const).mul_const _
  have hcomp : ∀ ε : ℝ, 0 < ε → ∫⁻ ω in B, (ν ω (thickening ε S) - μ S) / ENNReal.ofReal ε ∂q ≤
      (μ (thickening ε S) - μ S) / ENNReal.ofReal ε := by
    intro ε hε
    have hge : ∀ᵐ ω ∂q, μ S ≤ ν ω (thickening ε S) := by
      filter_upwards [hm] with ω hω
      rw [← hω]
      exact measure_mono (self_subset_thickening hε S)
    have hμth : μ (thickening ε S) = ∫⁻ ω, ν ω (thickening ε S) ∂q :=
      hd _ isOpen_thickening.measurableSet
    have hsplit : ∫⁻ ω, ν ω (thickening ε S) ∂q =
        ∫⁻ ω, (ν ω (thickening ε S) - μ S) ∂q + μ S := by
      have h1 : ∫⁻ ω, ν ω (thickening ε S) ∂q =
          ∫⁻ ω, ((ν ω (thickening ε S) - μ S) + μ S) ∂q :=
        lintegral_congr_ae (hge.mono fun ω hω => (tsub_add_cancel_of_le hω).symm)
      rw [h1, lintegral_add_right _ measurable_const]
      simp
    have hsub : ∫⁻ ω, (ν ω (thickening ε S) - μ S) ∂q = μ (thickening ε S) - μ S :=
      (ENNReal.sub_eq_of_eq_add (measure_ne_top _ _) (hμth.trans hsplit)).symm
    have hinv : (ENNReal.ofReal ε)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (by simpa using hε)
    calc ∫⁻ ω in B, (ν ω (thickening ε S) - μ S) / ENNReal.ofReal ε ∂q
        ≤ ∫⁻ ω, (ν ω (thickening ε S) - μ S) / ENNReal.ofReal ε ∂q :=
          setLIntegral_le_lintegral B _
      _ = (μ (thickening ε S) - μ S) / ENNReal.ofReal ε := by
          simp only [div_eq_mul_inv]
          rw [lintegral_mul_const' _ _ hinv, hsub]
  have hmain : 2⁻¹ * K ≤ minkowskiContent μ S := by
    have hF := lintegral_liminf_le (μ := q.restrict B) (u := 𝓝[>] (0 : ℝ))
      (f := fun (ε : ℝ) (ω : Ω) => (ν ω (thickening ε S) - μ S) / ENNReal.ofReal ε) hψm
    have hup : liminf (fun ε : ℝ => ∫⁻ ω in B,
        (ν ω (thickening ε S) - μ S) / ENNReal.ofReal ε ∂q) (𝓝[>] 0) ≤ minkowskiContent μ S := by
      refine liminf_le_liminf ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hcomp ε hε
    have hlow : K * q B ≤ ∫⁻ ω in B, liminf (fun ε : ℝ =>
        (ν ω (thickening ε S) - μ S) / ENNReal.ofReal ε) (𝓝[>] 0) ∂q := by
      calc K * q B = ∫⁻ ω in B, K ∂q := (setLIntegral_const B K).symm
        _ ≤ _ := by
          refine lintegral_mono_ae ?_
          exact (ae_restrict_iff' hBm).2 (hpt.mono fun ω hω hωB => hω hωB)
    calc 2⁻¹ * K ≤ q B * K := by gcongr
      _ = K * q B := mul_comm _ _
      _ ≤ minkowskiContent μ S := hlow.trans (hF.trans hup)
  have hconst : ENNReal.ofReal (1 / (256 * s)) = 2⁻¹ * ENNReal.ofReal (1 / 16 / (8 * s)) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    field_simp
    ring
  calc ENNReal.ofReal (1 / (256 * s)) * min (μ S) (1 - μ S) = 2⁻¹ * K := by
        rw [hK, hconst, mul_assoc]
    _ ≤ minkowskiContent μ S := hmain

/-- **Concentration ⇒ Poincaré inequality** (Corollary C), *conditional on Theorem N*: the
hypothesis `hN` supplies a needle decomposition for every measurable `A` with `0 < μ A < 1`
(Klartag's theorem, a separate work package), and `hconc` is `L¹` concentration of every
`1`-Lipschitz function at scale `s`.  Conclusion: `IsPoincareBound μ (4 * (256 s)²)`.  The `u`
produced by `hN` is a `1`-Lipschitz function (`NeedleDecomposition` records this), so `hconc`
applies to it. -/
theorem isPoincareBound_of_concentration (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) {s : ℝ} (hs : 0 < s)
    (hN : ∀ A : Set (Space n), MeasurableSet A → 0 < μ A → μ A < 1 →
      ∃ u, NeedleDecomposition μ A u)
    (hconc : ∀ v : Space n → ℝ, LipschitzWith 1 v →
      Integrable v μ ∧ ∫ x, |v x - ∫ y, v y ∂μ| ∂μ ≤ s) :
    IsPoincareBound μ (4 * (256 * s) ^ 2) := by
  have hpos : 0 < 1 / (256 * s) := by positivity
  have h := isPoincareBound_of_cheeger μ hμ hpos (fun A hA => ?_)
  · have e : 4 / (1 / (256 * s)) ^ 2 = 4 * (256 * s) ^ 2 := by field_simp
    rwa [e] at h
  · by_cases h0 : μ A = 0
    · simp [h0]
    by_cases h1 : μ A = 1
    · simp [h1]
    obtain ⟨u, hD⟩ := hN A hA (pos_iff_ne_zero.2 h0) (lt_of_le_of_ne prob_le_one h1)
    obtain ⟨hu, hR⟩ := hconc u hD.1
    exact cheeger_of_needle_decomposition μ hA hD hs hu hR

end CvxBody
