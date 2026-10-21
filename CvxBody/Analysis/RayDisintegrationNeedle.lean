module
public import CvxBody.Analysis.RayDisintegration
public import CvxBody.Analysis.NeedleDecomposition

@[expose] public section


/-!
# From a ray disintegration to a needle decomposition (assembly of WP-G)

`CvxBody.Analysis.RayDisintegration` constructs a ray disintegration `(q, κ)` of `μ` along the
rays of a Lipschitz maximizer `u`, with mass balance.  This file converts a ray disintegration whose
conditional laws `κ ω` have log-concave densities (a *hypothesis here*, discharged by
`NeedleLogConcave.lean`, lemma L12, in `MilmanPoincare.lean`) into a `NeedleDecomposition μ S u`.

* `rayNeedleKernel κ` is the kernel `ω ↦ (κ ω).map (t ↦ ω.2 + t • ω.1)` from `E × E` to `E`.
* `needleDecomposition_of_isRayDisintegration` is stated for an arbitrary ray disintegration.
* `needleDecomposition_of_rayDisintegration` specialises it to `q = rayBase μ u`,
  `κ = rayKernel μ u`; its only extra hypothesis is `hlc`, log-concavity of the needle densities.
-/

open OAI.LeanBlast.KLS MeasureTheory ProbabilityTheory Set
open CvxBody.Geometry
open scoped ENNReal

namespace CvxBody

variable {n : ℕ}

/-- The needle map `t ↦ ω.2 + t • ω.1` is measurable. -/
theorem measurable_rayPointMap (ω : Space n × Space n) :
    Measurable fun t : ℝ => ω.2 + t • ω.1 := by fun_prop

/-- The kernel `ω ↦ (κ ω).map (t ↦ ω.2 + t • ω.1)`: the parameter law `κ ω` transported to the line
with invariant `ω`. -/
noncomputable def rayNeedleKernel (κ : Kernel (Space n × Space n) ℝ) [IsSFiniteKernel κ] :
    Kernel (Space n × Space n) (Space n) where
  toFun ω := (κ ω).map fun t : ℝ => ω.2 + t • ω.1
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    simp_rw [Measure.map_apply (measurable_rayPointMap _) hA]
    exact measurable_rayKernel_preimage hA κ

section

variable (κ : Kernel (Space n × Space n) ℝ) [IsSFiniteKernel κ]

theorem rayNeedleKernel_apply (ω : Space n × Space n) :
    rayNeedleKernel κ ω = (κ ω).map fun t : ℝ => ω.2 + t • ω.1 := rfl

theorem rayNeedleKernel_apply_of_measurableSet (ω : Space n × Space n) {A : Set (Space n)}
    (hA : MeasurableSet A) :
    rayNeedleKernel κ ω A = κ ω {t : ℝ | ω.2 + t • ω.1 ∈ A} :=
  Measure.map_apply (measurable_rayPointMap ω) hA

instance [IsMarkovKernel κ] : IsMarkovKernel (rayNeedleKernel κ) :=
  ⟨fun ω => by
    rw [rayNeedleKernel_apply]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_rayPointMap ω).aemeasurable).2
      (IsMarkovKernel.isProbabilityMeasure ω)⟩

end

/-! ### Support of a log-concave density inside a closed set -/

/-- If the density `h` is log-concave, probability, and `h dt` gives no mass to the complement of a
closed set `C`, then `C` contains the whole positivity set of `h`. -/
theorem pos_subset_of_withDensity_compl_eq_zero {h : ℝ → ℝ} (hm : Measurable h)
    (hlc : IsLogConcaveFunction h)
    (h1 : (volume.withDensity fun t => ENNReal.ofReal (h t)) univ = 1) {C : Set ℝ}
    (hC : IsClosed C) (h0 : (volume.withDensity fun t => ENNReal.ofReal (h t)) Cᶜ = 0) :
    ∀ t, 0 < h t → t ∈ C := by
  set ρ : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (h t) with hρ
  have hρm : Measurable ρ := ENNReal.measurable_ofReal.comp hm
  set J : Set ℝ := {t | 0 < h t} with hJ
  have hJm : MeasurableSet J := measurableSet_lt measurable_const hm
  have hconv : J.OrdConnected := Convex.ordConnected hlc.log_concave.1
  -- `J` has positive Lebesgue measure
  have hJpos : volume J ≠ 0 := by
    intro hJ0
    have hJwd : (volume.withDensity ρ) J = 0 := withDensity_absolutelyContinuous volume ρ hJ0
    have hJc : (volume.withDensity ρ) Jᶜ = 0 := by
      rw [withDensity_apply _ hJm.compl]
      refine (setLIntegral_eq_zero_iff hJm.compl hρm).2 ?_
      refine Filter.Eventually.of_forall fun t ht => ?_
      have : ¬ 0 < h t := ht
      simp [hρ, ENNReal.ofReal_eq_zero, not_lt.mp this]
    have : (volume.withDensity ρ) univ = 0 := by
      rw [← union_compl_self J]; exact measure_union_null hJwd hJc
    rw [h1] at this
    exact one_ne_zero this
  -- `J ∩ Cᶜ` is Lebesgue null
  have hnull : volume (J ∩ Cᶜ) = 0 := by
    rw [withDensity_apply _ hC.isOpen_compl.measurableSet] at h0
    have h2 := (setLIntegral_eq_zero_iff hC.isOpen_compl.measurableSet hρm).1 h0
    refine measure_mono_null (fun t ht => ?_) (ae_iff.1 h2)
    simp only [mem_ofPred_eq, not_imp]
    refine ⟨ht.2, ?_⟩
    have : 0 < h t := ht.1
    simpa [hρ, ENNReal.ofReal_eq_zero, not_le] using this
  intro t0 ht0
  by_contra hnot
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hC.isOpen_compl t0 hnot
  have hne : ∃ t1 ∈ J, t1 ≠ t0 := by
    by_contra hcon
    push Not at hcon
    exact hJpos (Set.Subsingleton.measure_zero (fun x hx y hy => (hcon x hx).trans (hcon y hy).symm) _)
  obtain ⟨t1, ht1, hne⟩ := hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `t1 < t0`
    set ε : ℝ := min δ (t0 - t1) with hε
    have hεpos : 0 < ε := lt_min hδ (by linarith)
    have hsub : Ioo (t0 - ε) t0 ⊆ J ∩ Cᶜ := by
      intro t ht
      refine ⟨hconv.out ht1 ht0 ⟨?_, ht.2.le⟩, hball ?_⟩
      · have : ε ≤ t0 - t1 := min_le_right _ _
        linarith [ht.1]
      · have : ε ≤ δ := min_le_left _ _
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [ht.1, ht.2]
    have := measure_mono_null hsub hnull
    rw [Real.volume_Ioo] at this
    simp at this
    linarith
  · -- `t0 < t1`
    set ε : ℝ := min δ (t1 - t0) with hε
    have hεpos : 0 < ε := lt_min hδ (by linarith)
    have hsub : Ioo t0 (t0 + ε) ⊆ J ∩ Cᶜ := by
      intro t ht
      refine ⟨hconv.out ht0 ht1 ⟨ht.1.le, ?_⟩, hball ?_⟩
      · have : ε ≤ t1 - t0 := min_le_right _ _
        linarith [ht.2]
      · have : ε ≤ δ := min_le_left _ _
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [ht.1, ht.2]
    have := measure_mono_null hsub hnull
    rw [Real.volume_Ioo] at this
    simp at this
    linarith

/-! ### Assembly -/

section Assembly

/-- **Assembly (general form).**  Let `(q, κ)` be a ray disintegration of the probability measure
`μ` along the rays of the `1`-Lipschitz function `u`, with `μ (Strain u) = 1`, `q` a probability
measure and `κ` Markov.  If, for `q`-a.e. `ω`, the direction `ω.1` is a unit vector, `κ ω` is carried
by the set of slope-one parameters of the line `ω`, `κ ω` has a log-concave density, and `κ ω`
gives the mass `μ S` to `{t | ω.2 + t • ω.1 ∈ S}`, then `NeedleDecomposition μ S u` holds, with
`Ω = E × E`, `ν = rayNeedleKernel κ`, `θ ω = ω.1`, `o ω = ω.2`.  The log-concavity of the needle
densities is the hypothesis `hlc` (lemma L12, proved in `NeedleLogConcave.lean`). -/
theorem needleDecomposition_of_isRayDisintegration (μ : Measure (Space n))
    [IsProbabilityMeasure μ] {S : Set (Space n)} (hS : MeasurableSet S) {u : Space n → ℝ}
    (hu : LipschitzWith 1 u) (hStrain : μ (Strain u) = 1)
    {q : Measure (Space n × Space n)} [IsProbabilityMeasure q]
    {κ : Kernel (Space n × Space n) ℝ} [IsMarkovKernel κ] (hd : IsRayDisintegration μ u q κ)
    (hnorm : ∀ᵐ ω ∂q, ‖ω.1‖ = 1) (hsupp : ∀ᵐ ω ∂q, κ ω (raySlopeTimes u ω)ᶜ = 0)
    (hmass : ∀ᵐ ω ∂q, κ ω {t : ℝ | ω.2 + t • ω.1 ∈ S} = μ S)
    (hlc : ∀ᵐ ω ∂q, ∃ h : ℝ → ℝ, Measurable h ∧ IsLogConcaveFunction h ∧
      κ ω = volume.withDensity fun t => ENNReal.ofReal (h t)) :
    NeedleDecomposition μ S u := by
  refine ⟨hu, Space n × Space n, inferInstance, inferInstance, q, inferInstance,
    rayNeedleKernel κ, inferInstance, fun ω => ω.1, fun ω => ω.2, measurable_fst,
    measurable_snd, ?_, ?_, ?_⟩
  · -- disintegration
    intro A hA
    have h1 := hd A hA univ MeasurableSet.univ
    have hc : μ (Strain u)ᶜ = 0 := (prob_compl_eq_zero_iff (measurableSet_strain hu)).2 hStrain
    rw [preimage_univ, inter_univ, measure_inter_conull hc, Measure.restrict_univ] at h1
    rw [h1]
    refine lintegral_congr fun ω => ?_
    rw [rayNeedleKernel_apply_of_measurableSet κ ω hA]
  · -- needles
    filter_upwards [hnorm, hsupp, hlc] with ω hn hs ⟨h, hm, hl, hk⟩
    have hprob : (volume.withDensity fun t => ENNReal.ofReal (h t)) univ = 1 := by
      rw [← hk]; exact measure_univ
    have hint : ∫ t, h t = 1 := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hl.nonnegative)
        hm.aestronglyMeasurable]
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hprob
      rw [hprob]; simp
    refine ⟨hn, h, hm, hl, hint, ?_, ?_⟩
    · rw [rayNeedleKernel_apply, hk]
    · intro t ht
      have hpos : 0 < h t := lt_of_le_of_ne (hl.nonnegative t) (Ne.symm ht)
      have := pos_subset_of_withDensity_compl_eq_zero hm hl hprob
        (isClosed_raySlopeTimes hu ω) (by rw [← hk]; exact hs) t hpos
      exact this
  · -- mass balance
    filter_upwards [hmass] with ω hω
    rw [rayNeedleKernel_apply_of_measurableSet κ ω hS]
    exact hω

/-- **L11 + assembly.**  For a Lipschitz maximizer `u` of the mass-balance functional with null ends,
the ray disintegration `(rayBase μ u, rayKernel μ u)` of `μ` yields `NeedleDecomposition μ S u`,
provided the conditional laws `rayKernel μ u ω` have log-concave densities (hypothesis `hlc`:
lemma L12, proved in `NeedleLogConcave.lean`). -/
theorem needleDecomposition_of_rayDisintegration (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) {S : Set (Space n)} (hS : MeasurableSet S)
    (h0 : 0 < μ S) (h1 : μ S < 1) {u : Space n → ℝ}
    (hmax : IsLipschitzMaximizer μ (massBalanceFn μ S) u) (hEnds : μ (Ends u) = 0)
    (hlc : ∀ᵐ ω ∂(rayBase μ u), ∃ h : ℝ → ℝ, Measurable h ∧ IsLogConcaveFunction h ∧
      rayKernel μ u ω = volume.withDensity fun t => ENNReal.ofReal (h t)) :
    NeedleDecomposition μ S u := by
  have hu := hmax.1
  have hStrain : μ (Strain u) = 1 := (mass_balance_of_maximizer hμ hS h0 h1 hmax hEnds).2.1
  have := isProbabilityMeasure_rayBase hu hStrain (μ := μ)
  exact needleDecomposition_of_isRayDisintegration μ hS hu hStrain
    (isRayDisintegration_rayKernel hu) (ae_rayBase_norm_fst hu) (ae_rayKernel_mem_raySlopeTimes hu)
    (rayDisintegration_massBalance hμ hS h0 h1 hmax hEnds) hlc

end Assembly

end CvxBody
