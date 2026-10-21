module
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import CvxBody.Analysis.MassBalance

@[expose] public section


/-!
# Disintegration of a measure along the rays of a 1-Lipschitz function (lemma L11)

Work package WP-G of `docs/part1/P02-NEEDLE-BLUEPRINT.md`.  Fix a `1`-Lipschitz `u : E → ℝ`,
`E = Space n`.  A point `x ∈ Strain u` lies on the ray `t ↦ o + t • θ` with `(θ, o) = rayInv u x`
and `u`-coordinate `t = u x`, i.e. `x = o + (u x) • θ`.

* `IsRayDisintegration μ u q κ`: the kernel `κ : Kernel (E × E) ℝ` disintegrates `μ|_{Strain u}`
  along the ray invariant, parametrized by the `u`-coordinate.
* `rayKernel μ u` is the conditional kernel of the *graph measure*
  `(μ|_{Strain u}).map (x ↦ (rayInv u x, u x))` on `(E × E) × ℝ`
  (as recommended in `P02-NEEDLE-REVIEW-M0.md`, Section 7: nothing is asserted about the possibly
  non-Borel image `rayInv u '' Strain u`).
* `exists_rayDisintegration` (L11): existence of a probability measure `q` and a Markov kernel
  `κ` with `IsRayDisintegration μ u q κ`; for `q`-a.e. `ω` the measure `κ ω` lives on the open
  window `Ioo (rayLoOn u ω) (rayHiOn u ω)` of slope-one parameters of the ray `ω` (`rayLoOn`,
  `rayHiOn` are Borel functions on `E × E`, equal to `rayLo`, `rayHi` along the rays of `Strain u`).
* `rayDisintegration_massBalance`: mass balance `κ ω {t | ω.2 + t • ω.1 ∈ S} = μ S` for `q`-a.e.
  `ω`, when `u` is a Lipschitz maximizer with `μ (Ends u) = 0`.
-/

open OAI.LeanBlast.KLS MeasureTheory ProbabilityTheory Set
open CvxBody.Geometry
open scoped ENNReal

namespace CvxBody

variable {n : ℕ}

/-- `κ : Kernel (E × E) ℝ` disintegrates `μ` along the rays of `u`, `q` a measure on the
ray-invariant space `E × E`.  The ray with invariant `ω = (θ, o)` is `t ↦ o + t • θ`, and the
`u`-coordinate along it is `t` (a point `x ∈ Strain u` equals `o + u x • θ` for
`(θ, o) = rayInv u x`).  For every measurable `A ⊆ E` and `B ⊆ E × E`,
`μ (A ∩ Strain u ∩ rayInv u ⁻¹' B) = ∫⁻ ω in B, κ ω {t | ω.2 + t • ω.1 ∈ A} ∂q`. -/
def IsRayDisintegration (μ : Measure (Space n)) (u : Space n → ℝ)
    (q : Measure (Space n × Space n)) (κ : Kernel (Space n × Space n) ℝ) : Prop :=
  ∀ A : Set (Space n), MeasurableSet A → ∀ B : Set (Space n × Space n), MeasurableSet B →
    μ (A ∩ Strain u ∩ rayInv u ⁻¹' B) = ∫⁻ ω in B, κ ω {t : ℝ | ω.2 + t • ω.1 ∈ A} ∂q

/-- The graph measure `(μ|_{Strain u}).map (x ↦ (rayInv u x, u x))` on `(E × E) × ℝ`. -/
noncomputable def rayGraphMeasure (μ : Measure (Space n)) (u : Space n → ℝ) :
    Measure ((Space n × Space n) × ℝ) :=
  (μ.restrict (Strain u)).map fun x => (rayInv u x, u x)

/-- The law `q` of the ray invariant under `μ|_{Strain u}`. -/
noncomputable def rayBase (μ : Measure (Space n)) (u : Space n → ℝ) : Measure (Space n × Space n) :=
  (μ.restrict (Strain u)).map (rayInv u)

instance (μ : Measure (Space n)) [IsFiniteMeasure μ] (u : Space n → ℝ) :
    IsFiniteMeasure (rayGraphMeasure μ u) := by
  unfold rayGraphMeasure; infer_instance

instance (μ : Measure (Space n)) [IsFiniteMeasure μ] (u : Space n → ℝ) :
    IsFiniteMeasure (rayBase μ u) := by
  unfold rayBase; infer_instance

/-- The ray kernel: the conditional kernel of the graph measure given the ray invariant. -/
noncomputable def rayKernel (μ : Measure (Space n)) [IsFiniteMeasure μ] (u : Space n → ℝ) :
    Kernel (Space n × Space n) ℝ :=
  (rayGraphMeasure μ u).condKernel

instance (μ : Measure (Space n)) [IsFiniteMeasure μ] (u : Space n → ℝ) :
    IsMarkovKernel (rayKernel μ u) := by
  unfold rayKernel; infer_instance

instance (μ : Measure (Space n)) [IsFiniteMeasure μ] (u : Space n → ℝ) :
    (rayGraphMeasure μ u).IsCondKernel (rayKernel μ u) := by
  unfold rayKernel; infer_instance

section Basic

variable {μ : Measure (Space n)} [IsFiniteMeasure μ] {u : Space n → ℝ}

theorem rayInv_snd_add_smul_fst (u : Space n → ℝ) (x : Space n) :
    (rayInv u x).2 + u x • (rayInv u x).1 = x := by
  simp [rayInv]

theorem measurable_rayGraph (hu : LipschitzWith 1 u) :
    Measurable fun x => (rayInv u x, u x) :=
  (measurable_rayInv hu).prodMk hu.continuous.measurable

omit [IsFiniteMeasure μ] in
theorem rayGraphMeasure_fst (hu : LipschitzWith 1 u) : (rayGraphMeasure μ u).fst = rayBase μ u :=
  Measure.fst_map_prodMk (measurable_rayInv hu) hu.continuous.measurable

theorem rayGraphMeasure_eq_compProd (hu : LipschitzWith 1 u) :
    rayBase μ u ⊗ₘ rayKernel μ u = rayGraphMeasure μ u := by
  rw [← rayGraphMeasure_fst hu]
  exact Measure.disintegrate _ _

/-- The measurable set of `(ω, t)` with `ω.2 + t • ω.1 ∈ A`. -/
theorem measurableSet_rayPoint {A : Set (Space n)} (hA : MeasurableSet A) :
    MeasurableSet {p : (Space n × Space n) × ℝ | p.1.2 + p.2 • p.1.1 ∈ A} := by
  have : Measurable fun p : (Space n × Space n) × ℝ => p.1.2 + p.2 • p.1.1 := by fun_prop
  exact this hA

/-- The section at `ω` of the set of `(ω, t)` with `ω.2 + t • ω.1 ∈ A` is measurable. -/
theorem measurable_rayKernel_preimage {A : Set (Space n)} (hA : MeasurableSet A)
    (κ : Kernel (Space n × Space n) ℝ) [IsSFiniteKernel κ] :
    Measurable fun ω : Space n × Space n => κ ω {t : ℝ | ω.2 + t • ω.1 ∈ A} :=
  Kernel.measurable_kernel_prodMk_left (measurableSet_rayPoint hA)

/-- The kernel `rayKernel` disintegrates `μ` along the rays: statement (`IsRayDisintegration`)
for the base `rayBase μ u`.  (No hypothesis `μ (Strain u) = 1`: the identity concerns
`μ|_{Strain u}`.) -/
theorem isRayDisintegration_rayKernel (hu : LipschitzWith 1 u) :
    IsRayDisintegration μ u (rayBase μ u) (rayKernel μ u) := by
  intro A hA B hB
  have hG := measurable_rayGraph (u := u) hu
  set W : Set ((Space n × Space n) × ℝ) :=
    {p | p.1 ∈ B ∧ p.1.2 + p.2 • p.1.1 ∈ A} with hW
  have hWm : MeasurableSet W :=
    (measurable_fst hB).inter (measurableSet_rayPoint hA)
  have h1 : rayGraphMeasure μ u W = μ (A ∩ Strain u ∩ rayInv u ⁻¹' B) := by
    unfold rayGraphMeasure
    rw [Measure.map_apply hG hWm, Measure.restrict_apply (hG hWm)]
    congr 1
    ext x
    simp only [hW, mem_inter_iff, mem_preimage, mem_ofPred_eq, rayInv_snd_add_smul_fst]
    tauto
  have h2 := Measure.compProd_apply (μ := rayBase μ u) (κ := rayKernel μ u) hWm
  rw [rayGraphMeasure_eq_compProd hu, h1] at h2
  rw [h2, ← lintegral_indicator hB]
  refine lintegral_congr fun ω => ?_
  by_cases hω : ω ∈ B
  · simp [hW, hω, indicator_of_mem]
  · simp [hW, hω]

/-- Any measurable set containing the graph of `x ↦ (rayInv u x, u x)` over `Strain u` carries
the full mass of the sections `κ ω`, for `q`-a.e. `ω`. -/
theorem ae_rayKernel_section_of_graph_subset (hu : LipschitzWith 1 u)
    {W : Set ((Space n × Space n) × ℝ)} (hW : MeasurableSet W)
    (hsub : ∀ x ∈ Strain u, (rayInv u x, u x) ∈ W) :
    ∀ᵐ ω ∂(rayBase μ u), rayKernel μ u ω (Prod.mk ω ⁻¹' Wᶜ) = 0 := by
  have hG := measurable_rayGraph (u := u) hu
  have h0 : rayGraphMeasure μ u Wᶜ = 0 := by
    unfold rayGraphMeasure
    rw [Measure.map_apply hG hW.compl, Measure.restrict_apply (hG hW.compl)]
    have : (fun x => (rayInv u x, u x)) ⁻¹' Wᶜ ∩ Strain u = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false,
        not_and]
      exact fun h hx => absurd (hsub x hx) h
    rw [this, measure_empty]
  have h1 := Measure.compProd_apply (μ := rayBase μ u) (κ := rayKernel μ u) hW.compl
  rw [rayGraphMeasure_eq_compProd hu, h0] at h1
  exact (lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hW.compl)).1 h1.symm

end Basic

/-! ### The window of slope-one parameters, as a Borel function of the ray invariant -/

open Classical in
/-- Lower end of the window of slope-one parameters of the line `t ↦ ω.2 + t • ω.1`, computed over
rational parameters.  It is a Borel function of `ω ∈ E × E` (the review of L11 warns against using
the Borelness of `rayLo` as a function of the ray, which lives on a non-Borel image); on
`rayInv u '' Strain u` it equals `rayLo` (`rayLoOn_rayInv`). -/
noncomputable def rayLoOn (u : Space n → ℝ) (ω : Space n × Space n) : EReal :=
  ⨅ r : ℚ, if u (ω.2 + (r : ℝ) • ω.1) = r then (((r : ℝ)) : EReal) else ⊤

open Classical in
/-- Upper end of the window of slope-one parameters, computed over rational parameters. -/
noncomputable def rayHiOn (u : Space n → ℝ) (ω : Space n × Space n) : EReal :=
  ⨆ r : ℚ, if u (ω.2 + (r : ℝ) • ω.1) = r then (((r : ℝ)) : EReal) else ⊥

/-- The open window `(rayLoOn u ω, rayHiOn u ω)` of real parameters. -/
def rayWindow (u : Space n → ℝ) (ω : Space n × Space n) : Set ℝ :=
  {t : ℝ | rayLoOn u ω < t ∧ (t : EReal) < rayHiOn u ω}

section Window

variable {u : Space n → ℝ}

theorem measurable_rayLoOn (hu : LipschitzWith 1 u) : Measurable (rayLoOn u) := by
  classical
  unfold rayLoOn
  refine Measurable.iInf fun r => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_eq_fun (hu.continuous.measurable.comp (by fun_prop)) measurable_const

theorem measurable_rayHiOn (hu : LipschitzWith 1 u) : Measurable (rayHiOn u) := by
  classical
  unfold rayHiOn
  refine Measurable.iSup fun r => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_eq_fun (hu.continuous.measurable.comp (by fun_prop)) measurable_const

theorem measurableSet_rayWindow_graph (hu : LipschitzWith 1 u) :
    MeasurableSet {p : (Space n × Space n) × ℝ | p.2 ∈ rayWindow u p.1} := by
  have h1 : Measurable fun p : (Space n × Space n) × ℝ => rayLoOn u p.1 :=
    (measurable_rayLoOn hu).comp measurable_fst
  have h2 : Measurable fun p : (Space n × Space n) × ℝ => rayHiOn u p.1 :=
    (measurable_rayHiOn hu).comp measurable_fst
  have h3 : Measurable fun p : (Space n × Space n) × ℝ => ((p.2 : ℝ) : EReal) :=
    measurable_coe_real_ereal.comp measurable_snd
  exact (measurableSet_lt h1 h3).inter (measurableSet_lt h3 h2)

theorem rayLoOn_le_of_mem {ω : Space n × Space n} {r : ℚ} (h : u (ω.2 + (r : ℝ) • ω.1) = r) :
    rayLoOn u ω ≤ (r : ℝ) := by
  classical
  unfold rayLoOn
  refine (iInf_le _ r).trans ?_
  simp [h]

theorem le_rayHiOn_of_mem {ω : Space n × Space n} {r : ℚ} (h : u (ω.2 + (r : ℝ) • ω.1) = r) :
    ((r : ℝ) : EReal) ≤ rayHiOn u ω := by
  classical
  unfold rayHiOn
  refine le_trans ?_ (le_iSup _ r)
  simp [h]

/-- At a strain point, the window contains the `u`-coordinate in its interior. -/
theorem rayLoOn_lt_rayHiOn_rayInv (hu : LipschitzWith 1 u) {x : Space n} (hx : x ∈ Strain u) :
    rayLoOn u (rayInv u x) < (u x : ℝ) ∧ ((u x : ℝ) : EReal) < rayHiOn u (rayInv u x) := by
  obtain ⟨ε, hε, hxε⟩ := mem_strain_iff.mp hx
  have hI := Icc_subset_raySlopeTimes hu hε hxε
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show u x - ε < u x by linarith)
  obtain ⟨r', hr1', hr2'⟩ := exists_rat_btwn (show u x < u x + ε by linarith)
  have m1 : (r : ℝ) ∈ raySlopeTimes u (rayInv u x) := hI ⟨hr1.le, hr2.le.trans (by linarith)⟩
  have m2 : (r' : ℝ) ∈ raySlopeTimes u (rayInv u x) := hI ⟨(by linarith), hr2'.le⟩
  exact ⟨(rayLoOn_le_of_mem m1).trans_lt (EReal.coe_lt_coe_iff.mpr hr2),
    (EReal.coe_lt_coe_iff.mpr hr1').trans_le (le_rayHiOn_of_mem m2)⟩

/-- Every parameter in the window of a strain ray is a slope-one parameter. -/
theorem mem_raySlopeTimes_of_mem_rayWindow (hu : LipschitzWith 1 u) {x : Space n}
    (hx : x ∈ Strain u) {t : ℝ} (ht : t ∈ rayWindow u (rayInv u x)) :
    t ∈ raySlopeTimes u (rayInv u x) := by
  classical
  obtain ⟨h1, h2⟩ := ht
  obtain ⟨r, hr⟩ := iInf_lt_iff.mp h1
  obtain ⟨r', hr'⟩ := lt_iSup_iff.mp h2
  have e1 : u ((rayInv u x).2 + (r : ℝ) • (rayInv u x).1) = r := by
    by_contra hne
    simp [hne] at hr
  have e2 : u ((rayInv u x).2 + (r' : ℝ) • (rayInv u x).1) = r' := by
    by_contra hne
    simp [hne] at hr'
  simp only [e1, ↓reduceIte] at hr
  simp only [e2, ↓reduceIte] at hr'
  have hq : ‖(rayInv u x).1‖ = 1 := norm_strainDir hx
  exact (ordConnected_raySlopeTimes hu hq).out e1 e2
    ⟨(EReal.coe_lt_coe_iff.mp hr).le, (EReal.coe_lt_coe_iff.mp hr').le⟩

theorem rayLoOn_rayInv (hu : LipschitzWith 1 u) {x : Space n} (hx : x ∈ Strain u) :
    rayLoOn u (rayInv u x) = rayLo u x := by
  classical
  have hq : ‖(rayInv u x).1‖ = 1 := norm_strainDir hx
  have hcon := ordConnected_raySlopeTimes hu hq
  apply le_antisymm
  · refine le_sInf ?_
    rintro _ ⟨τ, hτ, rfl⟩
    by_cases hτu : u x ≤ τ
    · exact (rayLoOn_lt_rayHiOn_rayInv hu hx).1.le.trans (EReal.coe_le_coe_iff.mpr hτu)
    · replace hτu := not_le.mp hτu
      refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
      by_cases hau : (u x : ℝ) ≤ a
      · exact (rayLoOn_lt_rayHiOn_rayInv hu hx).1.le.trans hau
      · replace hau := not_le.mp hau
        obtain ⟨r, hr1, hr2⟩ := EReal.exists_rat_btwn_of_lt ha
        have hr1' : τ < (r : ℝ) := EReal.coe_lt_coe_iff.mp hr1
        have hr2' : (r : ℝ) < u x := EReal.coe_lt_coe_iff.mp (hr2.trans hau)
        have hm : (r : ℝ) ∈ raySlopeTimes u (rayInv u x) :=
          hcon.out hτ self_mem_raySlopeTimes ⟨hr1'.le, hr2'.le⟩
        exact (rayLoOn_le_of_mem hm).trans hr2.le
  · refine le_iInf fun r => ?_
    split_ifs with h
    · exact sInf_le (mem_image_of_mem _ h)
    · exact le_top

theorem rayHiOn_rayInv (hu : LipschitzWith 1 u) {x : Space n} (hx : x ∈ Strain u) :
    rayHiOn u (rayInv u x) = rayHi u x := by
  classical
  have hq : ‖(rayInv u x).1‖ = 1 := norm_strainDir hx
  have hcon := ordConnected_raySlopeTimes hu hq
  apply le_antisymm
  · refine iSup_le fun r => ?_
    split_ifs with h
    · exact le_sSup (mem_image_of_mem _ h)
    · exact bot_le
  · refine sSup_le ?_
    rintro _ ⟨τ, hτ, rfl⟩
    by_cases hτu : τ ≤ u x
    · exact (EReal.coe_le_coe_iff.mpr hτu).trans (rayLoOn_lt_rayHiOn_rayInv hu hx).2.le
    · replace hτu := not_le.mp hτu
      refine le_of_forall_lt_imp_le_of_dense fun a ha => ?_
      by_cases hau : a ≤ (u x : ℝ)
      · exact hau.trans (rayLoOn_lt_rayHiOn_rayInv hu hx).2.le
      · replace hau := not_le.mp hau
        obtain ⟨r, hr1, hr2⟩ := EReal.exists_rat_btwn_of_lt ha
        have hr1' : u x < (r : ℝ) := EReal.coe_lt_coe_iff.mp (hau.trans hr1)
        have hr2' : (r : ℝ) < τ := EReal.coe_lt_coe_iff.mp hr2
        have hm : (r : ℝ) ∈ raySlopeTimes u (rayInv u x) :=
          hcon.out self_mem_raySlopeTimes hτ ⟨hr1'.le, hr2'.le⟩
        exact hr1.le.trans (le_rayHiOn_of_mem hm)

end Window

/-! ### Existence (L11) -/

section Existence

variable {μ : Measure (Space n)} [IsFiniteMeasure μ] {u : Space n → ℝ}

omit [IsFiniteMeasure μ] in
/-- `q`-a.e. the ray direction has unit norm. -/
theorem ae_rayBase_norm_fst (hu : LipschitzWith 1 u) :
    ∀ᵐ ω ∂(rayBase μ u), ‖ω.1‖ = 1 := by
  have hm : MeasurableSet {ω : Space n × Space n | ‖ω.1‖ = 1} :=
    measurableSet_eq_fun (measurable_fst.norm) measurable_const
  unfold rayBase
  rw [ae_map_iff (measurable_rayInv hu).aemeasurable hm,
    ae_restrict_iff' (measurableSet_strain hu)]
  exact Filter.Eventually.of_forall fun x hx => norm_strainDir hx

/-- `q`-a.e., `κ ω` is carried by the set of slope-one parameters of the line `ω`. -/
theorem ae_rayKernel_mem_raySlopeTimes (hu : LipschitzWith 1 u) :
    ∀ᵐ ω ∂(rayBase μ u), rayKernel μ u ω (raySlopeTimes u ω)ᶜ = 0 := by
  have hC : MeasurableSet {p : (Space n × Space n) × ℝ | u (p.1.2 + p.2 • p.1.1) = p.2} :=
    measurableSet_eq_fun (hu.continuous.measurable.comp (by fun_prop)) measurable_snd
  have h := ae_rayKernel_section_of_graph_subset (μ := μ) hu hC (fun x _ => by
    simp only [mem_ofPred_eq, rayInv_snd_add_smul_fst])
  filter_upwards [h] with ω hω
  exact hω

/-- `q`-a.e., `κ ω` is carried by the open window `(rayLoOn u ω, rayHiOn u ω)`; at the points
`ω = rayInv u x`, `x ∈ Strain u`, this is `Ioo (rayLo u x) (rayHi u x)`
(`rayLoOn_rayInv`, `rayHiOn_rayInv`). -/
theorem ae_rayKernel_mem_rayWindow (hu : LipschitzWith 1 u) :
    ∀ᵐ ω ∂(rayBase μ u), rayKernel μ u ω (rayWindow u ω)ᶜ = 0 := by
  have h := ae_rayKernel_section_of_graph_subset (μ := μ) hu (measurableSet_rayWindow_graph hu)
    (fun x hx => by
      obtain ⟨h1, h2⟩ := rayLoOn_lt_rayHiOn_rayInv hu hx
      exact ⟨h1, h2⟩)
  filter_upwards [h] with ω hω
  exact hω

omit [IsFiniteMeasure μ] in
/-- `q = rayBase μ u` is a probability measure when `μ (Strain u) = 1`. -/
theorem isProbabilityMeasure_rayBase (hu : LipschitzWith 1 u) (hS : μ (Strain u) = 1) :
    IsProbabilityMeasure (rayBase μ u) := by
  constructor
  unfold rayBase
  rw [Measure.map_apply (measurable_rayInv hu) MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, hS]

/-- **L11 (disintegration along the rays).**  Let `u` be `1`-Lipschitz and `μ` a probability
measure with `μ (Strain u) = 1`.  Then `q = (μ|_{Strain u}).map (rayInv u)` is a probability
measure on the ray-invariant space `E × E` and `κ = rayKernel μ u` is a Markov kernel with
`IsRayDisintegration μ u q κ`; moreover, for `q`-a.e. `ω` the direction `ω.1` is a unit vector and
`κ ω` is carried by the open window `Ioo (rayLoOn u ω) (rayHiOn u ω)` of slope-one parameters of the
line `ω`, where `rayLoOn`, `rayHiOn : E × E → EReal` are Borel and agree with `rayLo`, `rayHi` on
every strain ray. -/
theorem exists_rayDisintegration (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    {u : Space n → ℝ} (hu : LipschitzWith 1 u) (hS : μ (Strain u) = 1) :
    ∃ (q : Measure (Space n × Space n)) (_ : IsProbabilityMeasure q)
      (κ : Kernel (Space n × Space n) ℝ) (_ : IsMarkovKernel κ)
      (a b : Space n × Space n → EReal),
      q = (μ.restrict (Strain u)).map (rayInv u) ∧ IsRayDisintegration μ u q κ ∧
      Measurable a ∧ Measurable b ∧
      (∀ x ∈ Strain u, a (rayInv u x) = rayLo u x ∧ b (rayInv u x) = rayHi u x) ∧
      (∀ᵐ ω ∂q, ‖ω.1‖ = 1) ∧
      (∀ᵐ ω ∂q, κ ω {t : ℝ | a ω < t ∧ (t : EReal) < b ω}ᶜ = 0) ∧
      (∀ᵐ ω ∂q, κ ω (raySlopeTimes u ω)ᶜ = 0) := by
  exact ⟨rayBase μ u, isProbabilityMeasure_rayBase hu hS, rayKernel μ u, inferInstance, rayLoOn u, rayHiOn u, rfl,
    isRayDisintegration_rayKernel hu, measurable_rayLoOn hu, measurable_rayHiOn hu,
    fun x hx => ⟨rayLoOn_rayInv hu hx, rayHiOn_rayInv hu hx⟩, ae_rayBase_norm_fst hu,
    ae_rayKernel_mem_rayWindow hu, ae_rayKernel_mem_raySlopeTimes hu⟩

end Existence

/-! ### Mass balance along the rays -/

section MassBalance

variable {μ : Measure (Space n)} [IsProbabilityMeasure μ] {S : Set (Space n)} {u : Space n → ℝ}

/-- Mass balance in measure form: on every `B`, the strain part of the ray-invariant set `B`
carries `S`-mass proportional to its mass. -/
theorem measure_inter_strain_preimage_eq
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hS : MeasurableSet S) (h0 : 0 < μ S)
    (h1 : μ S < 1) (hmax : IsLipschitzMaximizer μ (massBalanceFn μ S) u) (hEnds : μ (Ends u) = 0)
    {B : Set (Space n × Space n)} (hB : MeasurableSet B) :
    μ (S ∩ Strain u ∩ rayInv u ⁻¹' B) = μ S * μ (Strain u ∩ rayInv u ⁻¹' B) := by
  have hu := hmax.1
  have hR : MeasurableSet (Strain u ∩ rayInv u ⁻¹' B) :=
    (measurableSet_strain hu).inter (measurable_rayInv hu hB)
  have hz := (mass_balance_of_maximizer hμ hS h0 h1 hmax hEnds).2.2 B hB
  have e1 : ∫ x in Strain u ∩ rayInv u ⁻¹' B, massBalanceFn μ S x ∂μ =
      μ.real (Strain u ∩ rayInv u ⁻¹' B ∩ S) - μ.real S * μ.real (Strain u ∩ rayInv u ⁻¹' B) := by
    unfold massBalanceFn
    rw [integral_sub ((integrable_const (1 : ℝ)).indicator hS).integrableOn
      (integrable_const _).integrableOn, setIntegral_indicator hS]
    simp [Measure.real, mul_comm]
  rw [e1] at hz
  have e2 : μ.real (Strain u ∩ rayInv u ⁻¹' B ∩ S) =
      μ.real S * μ.real (Strain u ∩ rayInv u ⁻¹' B) := sub_eq_zero.mp hz
  have e3 : S ∩ Strain u ∩ rayInv u ⁻¹' B = Strain u ∩ rayInv u ⁻¹' B ∩ S := by
    ext x; simp only [mem_inter_iff]; tauto
  rw [e3]
  rw [Measure.real, Measure.real, Measure.real, ← ENNReal.toReal_mul] at e2
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).1 e2

/-- **Mass balance along rays**, for an arbitrary ray disintegration `(q, κ)` of `μ` along the rays
of `u` (`q` finite, `κ` Markov): for `q`-a.e. `ω`, the line `t ↦ ω.2 + t • ω.1` carries `S`-mass
`μ S` for the measure `κ ω`. -/
theorem ae_massBalance_of_isRayDisintegration
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hS : MeasurableSet S) (h0 : 0 < μ S)
    (h1 : μ S < 1) (hmax : IsLipschitzMaximizer μ (massBalanceFn μ S) u) (hEnds : μ (Ends u) = 0)
    {q : Measure (Space n × Space n)} [IsFiniteMeasure q] {κ : Kernel (Space n × Space n) ℝ}
    [IsMarkovKernel κ] (hd : IsRayDisintegration μ u q κ) :
    ∀ᵐ ω ∂q, κ ω {t : ℝ | ω.2 + t • ω.1 ∈ S} = μ S := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (measurable_rayKernel_preimage hS κ) measurable_const fun B hB _ => ?_
  have h2 := hd S hS B hB
  have h3 := hd univ MeasurableSet.univ B hB
  have e : ∀ ω : Space n × Space n, κ ω {t : ℝ | ω.2 + t • ω.1 ∈ (univ : Set (Space n))} = 1 :=
    fun ω => by simp
  simp only [e, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul,
    univ_inter] at h3
  rw [← h2, setLIntegral_const, ← h3, measure_inter_strain_preimage_eq hμ hS h0 h1 hmax hEnds hB]

/-- **L11, mass balance** for the kernel `rayKernel`: for `q`-a.e. `ω`,
`κ ω {t | ω.2 + t • ω.1 ∈ S} = μ S`. -/
theorem rayDisintegration_massBalance
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hS : MeasurableSet S) (h0 : 0 < μ S)
    (h1 : μ S < 1) (hmax : IsLipschitzMaximizer μ (massBalanceFn μ S) u) (hEnds : μ (Ends u) = 0) :
    ∀ᵐ ω ∂(rayBase μ u), rayKernel μ u ω {t : ℝ | ω.2 + t • ω.1 ∈ S} = μ S :=
  ae_massBalance_of_isRayDisintegration hμ hS h0 h1 hmax hEnds
    (isRayDisintegration_rayKernel hmax.1)

end MassBalance

end CvxBody
