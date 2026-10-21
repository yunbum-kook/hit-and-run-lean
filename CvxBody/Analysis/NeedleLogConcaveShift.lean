module
public import CvxBody.Analysis.NeedleLogConcaveRay
public import CvxBody.Analysis.NeedleLogConcave1D

@[expose] public section


/-!
# The shift identity along the rays (WP-H, step E of the review)

For a `1`-Lipschitz `u`, `ε > 0`, a Hessian `H` of the ray direction field away from a null set `N`
(`IsRayHessian u ε H N`), the measure `μ = ρ dx` and a disintegration `(q, κ)` of `μ` along the
rays, we prove, for `|s| < ε`, a window `[α, β]` with `α < β`, a measurable set `A` of ray invariants
in `WindowSet u ε α β` and a measurable `I ⊆ [α, β]`:

`∫_A κ_ω ((I ∩ D_ω) + s) dq = ∫_A ∫_{I ∩ D_ω} ρ(x_ω(t+s)) / ρ(x_ω(t)) · det(1 + s H(x_ω(t))) dκ_ω(t) dq(ω)`,

where `D_ω = {t | x_ω(t) ∈ D₀}` and `D₀ ⊆ {ρ > 0}` is open (`shift_identity`).  The proof applies the
area formula of `RayShift.lean` to `B = {x ∈ raySet u ε ∩ D₀ \ N | rayInv x ∈ A, u x ∈ I}` and
rewrites both sides with the disintegration.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open OAI.LeanBlast.KLS CvxBody.Geometry
open scoped ENNReal RealInnerProductSpace InnerProductSpace

namespace CvxBody.NeedleLC

variable {n : ℕ} {u : Space n → ℝ}

/-- The parameters `t` with `rayPt ω t ∈ D₀`. -/
def Dray (D₀ : Set (Space n)) (ω : Space n × Space n) : Set ℝ := (fun t => rayPt ω t) ⁻¹' D₀

theorem isOpen_Dray {D₀ : Set (Space n)} (hD₀ : IsOpen D₀) (ω : Space n × Space n) :
    IsOpen (Dray D₀ ω) := hD₀.preimage (continuous_rayPt_right ω)

/-- The shift density along the ray `ω`: `ρ(x_ω(t+s)) / ρ(x_ω(t)) · det(1 + s H(x_ω(t)))`. -/
noncomputable def shiftDens (ρ : Space n → ℝ) (H : Space n → (Space n →L[ℝ] Space n)) (s : ℝ)
    (ω : Space n × Space n) (t : ℝ) : ℝ :=
  ρ (rayPt ω (t + s)) / ρ (rayPt ω t) * shiftJac H s (rayPt ω t)

/-- Facts at a point `rayPt ω t` which is a strain point with invariant `ω`. -/
theorem K_facts {ω : Space n × Space n} {t : ℝ} (h1 : rayInv u (rayPt ω t) = ω)
    (h2 : rayPt ω t ∈ Strain u) :
    ‖ω.1‖ = 1 ∧ u (rayPt ω t) = t ∧ strainDir u (rayPt ω t) = ω.1 := by
  have hω1 : ‖ω.1‖ = 1 := by rw [← h1]; exact norm_strainDir h2
  exact ⟨hω1, u_eq_of_rayInv hω1 h1 rfl, congrArg Prod.fst h1⟩

section Step1

variable (hu : LipschitzWith 1 u) {ε α β s : ℝ} (hε : 0 < ε) (hs : |s| < ε) (hαβ : α < β)

include hu hε hs hαβ in
/-- The image of `B⁺` under the shift is the set `T`. -/
theorem image_rayShift_eq {D₀ : Set (Space n)} {A : Set (Space n × Space n)}
    (hAΩ : A ⊆ WindowSet u ε α β) {I : Set ℝ} (hIαβ : I ⊆ Icc α β) :
    rayShift u s '' {x | x ∈ raySet u ε ∧ x ∈ D₀ ∧ rayInv u x ∈ A ∧ u x ∈ I} =
      {y | y ∈ Strain u ∧ rayInv u y ∈ A ∧ u y - s ∈ I ∧ y - s • strainDir u y ∈ D₀} := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxS, hxD, hxA, hxI⟩, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := rayShift_spec hu hε hxS hs
    have hpos : 0 < ε - |s| := by linarith
    refine ⟨raySet_subset_strain hpos h3, by rw [h1]; exact hxA, by rw [h2]; simpa using hxI, ?_⟩
    rw [h4, rayShift_apply]
    simpa using hxD
  · rintro ⟨hyS, hyA, hyI, hyD⟩
    set ω := rayInv u y with hω
    have hω1 : ‖ω.1‖ = 1 := norm_strainDir hyS
    have hy : y = rayPt ω (u y) := eq_rayPt_of_rayInv hω.symm
    have hθ : strainDir u y = ω.1 := rfl
    have hτ : u y - s ∈ Icc α β := hIαβ hyI
    obtain ⟨hxS, hxu⟩ := hAΩ hyA (u y - s) hτ
    obtain ⟨hxinv, -⟩ := rayInv_rayPt_of_window hu hε hαβ hω1 (hAΩ hyA) hτ
    have hxdir := strainDir_rayPt_of_window hu hε hαβ hω1 (hAΩ hyA) hτ
    have hx : rayPt ω (u y - s) = y - s • strainDir u y := by
      rw [hθ]
      have := rayPt_add_smul ω (u y) (-s)
      rw [← sub_eq_add_neg, neg_smul, ← sub_eq_add_neg] at this
      rw [← this, ← hy]
    refine ⟨rayPt ω (u y - s), ⟨hxS, by rw [hx]; exact hyD, by rw [hxinv]; exact hyA,
      by rw [hxu]; exact hyI⟩, ?_⟩
    rw [rayShift_apply, hxdir, rayPt_add_smul, sub_add_cancel, ← hy]

end Step1

section Identity

variable {ρ : Space n → ℝ} {D₀ : Set (Space n)} {μ : Measure (Space n)}
  {q : Measure (Space n × Space n)} {κ : Kernel (Space n × Space n) ℝ}
  [IsProbabilityMeasure q] [IsMarkovKernel κ]

theorem measurable_rayShift (hu : LipschitzWith 1 u) (s : ℝ) : Measurable (rayShift u s) :=
  measurable_id.add ((measurable_strainDir hu).const_smul s)

theorem measurable_shiftJac {H : Space n → (Space n →L[ℝ] Space n)} (hHm : Measurable H) (s : ℝ) :
    Measurable (shiftJac H s) :=
  ContinuousLinearMap.continuous_det.measurable.comp
    (measurable_const.add (hHm.const_smul s))

theorem hIDm_aux {D₀ : Set (Space n)} (hD₀ : IsOpen D₀) {I : Set ℝ} (hI : MeasurableSet I)
    (ω : Space n × Space n) : MeasurableSet (I ∩ Dray D₀ ω) :=
  hI.inter (isOpen_Dray hD₀ ω).measurableSet

/-- Membership of `rayPt ω t` in the set `T` in terms of the ray coordinate. -/
theorem rayPt_mem_T_iff {A : Set (Space n × Space n)} {I : Set ℝ} {D₀ : Set (Space n)} {s : ℝ}
    {ω : Space n × Space n} {t : ℝ} (h1 : rayInv u (rayPt ω t) = ω) (h2 : rayPt ω t ∈ Strain u) :
    rayPt ω t ∈ {y | y ∈ Strain u ∧ rayInv u y ∈ A ∧ u y - s ∈ I ∧
        y - s • strainDir u y ∈ D₀} ↔ ω ∈ A ∧ t - s ∈ I ∧ t - s ∈ Dray D₀ ω := by
  obtain ⟨-, hut, hdir⟩ := K_facts h1 h2
  have hx : rayPt ω t - s • strainDir u (rayPt ω t) = rayPt ω (t - s) := by
    rw [hdir]
    have := rayPt_add_smul ω t (-s)
    rw [neg_smul, ← sub_eq_add_neg, ← sub_eq_add_neg] at this
    exact this
  simp only [mem_ofPred_eq, h1, hut, hx, h2, true_and, Dray, mem_preimage]

/-- **Shift identity along the rays.** -/
theorem shift_identity (hu : LipschitzWith 1 u) (hρm : Measurable ρ) (hD₀ : IsOpen D₀)
    (hρD₀ : ∀ x ∈ D₀, 0 < ρ x) (hμ : μ = volume.withDensity fun x => ENNReal.ofReal (ρ x))
    (hdis : IsRayDisintegrationH μ u q κ) {ε : ℝ} (hε : 0 < ε)
    {H : Space n → (Space n →L[ℝ] Space n)} {N : Set (Space n)} (hH : IsRayHessian u ε H N)
    (hHm : Measurable H) (hNm : MeasurableSet N) (hN0 : volume N = 0) {s : ℝ} (hs : |s| < ε)
    {α β : ℝ} (hαβ : α < β) {A : Set (Space n × Space n)} (hA : MeasurableSet A)
    (hAΩ : A ⊆ WindowSet u ε α β) {I : Set ℝ} (hI : MeasurableSet I) (hIαβ : I ⊆ Icc α β) :
    ∫⁻ ω in A, κ ω (shiftSet s (I ∩ Dray D₀ ω)) ∂q =
      ∫⁻ ω in A, ∫⁻ t in I ∩ Dray D₀ ω, ENNReal.ofReal (shiftDens ρ H s ω t) ∂κ ω ∂q := by
  have hSm : MeasurableSet (raySet u ε) := (isClosed_raySet hu ε).measurableSet
  set Bp : Set (Space n) := {x | x ∈ raySet u ε ∧ x ∈ D₀ ∧ rayInv u x ∈ A ∧ u x ∈ I} with hBp
  have hBpm : MeasurableSet Bp := by
    have : Bp = raySet u ε ∩ (D₀ ∩ (rayInv u ⁻¹' A ∩ u ⁻¹' I)) := by
      ext x
      simp only [hBp, mem_ofPred_eq, mem_inter_iff, mem_preimage]
    rw [this]
    exact hSm.inter (hD₀.measurableSet.inter (((measurable_rayInv hu) hA).inter
      (hu.continuous.measurable hI)))
  set T : Set (Space n) :=
    {y | y ∈ Strain u ∧ rayInv u y ∈ A ∧ u y - s ∈ I ∧ y - s • strainDir u y ∈ D₀} with hT
  have hTm : MeasurableSet T := by
    have : T = Strain u ∩ (rayInv u ⁻¹' A ∩ ((fun y => u y - s) ⁻¹' I ∩
        ((fun y => y - s • strainDir u y) ⁻¹' D₀))) := by
      ext y
      simp only [hT, mem_ofPred_eq, mem_inter_iff, mem_preimage]
    rw [this]
    exact (measurableSet_strain hu).inter (((measurable_rayInv hu) hA).inter
      (((hu.continuous.measurable.sub_const s) hI).inter
        ((measurable_id.sub ((measurable_strainDir hu).const_smul s)) hD₀.measurableSet)))
  have hTeq : rayShift u s '' Bp = T := image_rayShift_eq hu hε hs hαβ hAΩ hIαβ
  have hIDm : ∀ ω : Space n × Space n, MeasurableSet (I ∩ Dray D₀ ω) := fun ω =>
    hI.inter (isOpen_Dray hD₀ ω).measurableSet
  set g : Space n → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (ρ (rayShift u s x) / ρ x * shiftJac H s x) with hg
  have hgm : Measurable g :=
    ENNReal.measurable_ofReal.comp (((hρm.comp (measurable_rayShift hu s)).div hρm).mul
      (measurable_shiftJac hHm s))
  have hμN : μ N = 0 := by rw [hμ]; exact withDensity_absolutelyContinuous _ _ hN0
  -- Step 2: the area formula
  have hBsub : Bp \ N ⊆ raySet u ε \ N := fun x hx => ⟨hx.1.1, hx.2⟩
  have hBm : MeasurableSet (Bp \ N) := hBpm.diff hNm
  have hmu1 : μ (rayShift u s '' (Bp \ N)) = ∫⁻ x in Bp \ N, g x ∂μ := by
    rw [hμ]
    exact measure_image_rayShift_withDensity hu hε hH hs hBm hBsub hρm
      (fun x hx => hρD₀ x hx.1.2.1)
  have hnull : μ (rayShift u s '' (Bp ∩ N)) = 0 := by
    rw [hμ]
    refine withDensity_absolutelyContinuous _ _ ?_
    refine volume_image_rayShift_eq_zero hu hε s (fun x hx => hx.1.1) ?_
    exact measure_mono_null inter_subset_right hN0
  have hmu2 : μ T = μ (rayShift u s '' (Bp \ N)) := by
    rw [← hTeq]
    apply le_antisymm
    · calc μ (rayShift u s '' Bp)
          ≤ μ (rayShift u s '' (Bp \ N) ∪ rayShift u s '' (Bp ∩ N)) := by
            apply measure_mono
            rw [← image_union]
            apply image_mono
            intro x hx
            by_cases hxN : x ∈ N
            · exact Or.inr ⟨hx, hxN⟩
            · exact Or.inl ⟨hx, hxN⟩
        _ ≤ μ (rayShift u s '' (Bp \ N)) + μ (rayShift u s '' (Bp ∩ N)) := measure_union_le _ _
        _ = μ (rayShift u s '' (Bp \ N)) := by rw [hnull, add_zero]
    · exact measure_mono (image_mono sdiff_subset)
  have hmu3 : ∫⁻ x in Bp \ N, g x ∂μ = ∫⁻ x in Bp, g x ∂μ :=
    setLIntegral_congr (sdiff_null_ae_eq_self hμN)
  -- Step 3: the left-hand side through the disintegration
  have hL : μ T = ∫⁻ ω in A, κ ω (shiftSet s (I ∩ Dray D₀ ω)) ∂q := by
    have hTsub : T ⊆ Strain u := fun y hy => hy.1
    have h1 : μ T = ∫⁻ y in Strain u, T.indicator (fun _ => (1 : ℝ≥0∞)) y ∂μ := by
      rw [lintegral_indicator_const hTm, one_mul, Measure.restrict_apply hTm,
        inter_eq_left.2 hTsub]
    rw [h1, lintegral_strain hu hdis (measurable_const.indicator hTm), ← lintegral_indicator hA]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_rayInv_rayPt hu hdis] with ω hω
    by_cases hωA : ω ∈ A
    · rw [indicator_of_mem hωA]
      have : ∀ᵐ t ∂κ ω, T.indicator (fun _ => (1 : ℝ≥0∞)) (rayPt ω t) =
          (shiftSet s (I ∩ Dray D₀ ω)).indicator (fun _ => (1 : ℝ≥0∞)) t := by
        filter_upwards [hω] with t ht
        have hiff := rayPt_mem_T_iff (A := A) (I := I) (D₀ := D₀) (s := s) ht.1 ht.2
        by_cases hmem : t ∈ shiftSet s (I ∩ Dray D₀ ω)
        · rw [indicator_of_mem hmem, indicator_of_mem]
          exact hiff.2 ⟨hωA, hmem.1, hmem.2⟩
        · rw [indicator_of_notMem hmem, indicator_of_notMem]
          intro hT'
          obtain ⟨-, h2, h3⟩ := hiff.1 hT'
          exact hmem ⟨h2, h3⟩
      rw [lintegral_congr_ae this, lintegral_indicator_const
        (measurableSet_shiftSet s (hIDm ω)), one_mul]
    · rw [indicator_of_notMem hωA]
      have : ∀ᵐ t ∂κ ω, T.indicator (fun _ => (1 : ℝ≥0∞)) (rayPt ω t) = 0 := by
        filter_upwards [hω] with t ht
        rw [indicator_of_notMem]
        intro hT'
        exact hωA ((rayPt_mem_T_iff (A := A) (I := I) (D₀ := D₀) (s := s) ht.1 ht.2).1 hT').1
      rw [lintegral_congr_ae this, lintegral_zero]
  -- Step 4: the right-hand side through the disintegration
  have hR : ∫⁻ x in Bp, g x ∂μ =
      ∫⁻ ω in A, ∫⁻ t in I ∩ Dray D₀ ω, ENNReal.ofReal (shiftDens ρ H s ω t) ∂κ ω ∂q := by
    have hBpS : Bp ⊆ Strain u := fun x hx => raySet_subset_strain hε hx.1
    have h1 : ∫⁻ x in Bp, g x ∂μ = ∫⁻ y in Strain u, Bp.indicator g y ∂μ := by
      rw [← lintegral_indicator hBpm, ← lintegral_indicator (measurableSet_strain hu)]
      refine lintegral_congr fun y => ?_
      rw [indicator_indicator, inter_eq_right.2 hBpS]
    rw [h1, lintegral_strain hu hdis (hgm.indicator hBpm), ← lintegral_indicator hA]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_rayInv_rayPt hu hdis] with ω hω
    by_cases hωA : ω ∈ A
    · rw [indicator_of_mem hωA]
      have : ∀ᵐ t ∂κ ω, Bp.indicator g (rayPt ω t) =
          (I ∩ Dray D₀ ω).indicator (fun t => ENNReal.ofReal (shiftDens ρ H s ω t)) t := by
        filter_upwards [hω] with t ht
        obtain ⟨-, hut, hdir⟩ := K_facts ht.1 ht.2
        by_cases hmem : t ∈ I ∩ Dray D₀ ω
        · rw [indicator_of_mem hmem, indicator_of_mem]
          · simp only [hg, shiftDens, rayShift_apply, hdir, rayPt_add_smul]
          · exact ⟨(hAΩ hωA t (hIαβ hmem.1)).1, hmem.2, by rw [ht.1]; exact hωA, by
              rw [hut]; exact hmem.1⟩
        · rw [indicator_of_notMem hmem, indicator_of_notMem]
          rintro ⟨-, hD, -, hI'⟩
          exact hmem ⟨by rw [← hut]; exact hI', hD⟩
      rw [lintegral_congr_ae this, lintegral_indicator (hIDm ω)]
    · rw [indicator_of_notMem hωA]
      have : ∀ᵐ t ∂κ ω, Bp.indicator g (rayPt ω t) = 0 := by
        filter_upwards [hω] with t ht
        rw [indicator_of_notMem]
        rintro ⟨-, -, hA', -⟩
        rw [ht.1] at hA'
        exact hωA hA'
      rw [lintegral_congr_ae this, lintegral_zero]
  rw [← hL, hmu2, hmu1, hmu3, hR]

theorem measurable_shiftJac_joint {H : Space n → (Space n →L[ℝ] Space n)} (hHm : Measurable H) :
    Measurable fun p : ℝ × Space n => shiftJac H p.1 p.2 := by
  unfold shiftJac
  exact ContinuousLinearMap.continuous_det.measurable.comp
    (measurable_const.add (measurable_fst.smul (hHm.comp measurable_snd)))

theorem measurable_shiftDens_joint (hρm : Measurable ρ) {H : Space n → (Space n →L[ℝ] Space n)}
    (hHm : Measurable H) :
    Measurable fun z : ((Space n × Space n) × ℝ) × ℝ => shiftDens ρ H z.1.2 z.1.1 z.2 := by
  unfold shiftDens
  have hpt : Measurable fun z : ((Space n × Space n) × ℝ) × ℝ => rayPt z.1.1 z.2 :=
    measurable_rayPt.comp (measurable_fst.fst.prodMk measurable_snd)
  have hpt2 : Measurable fun z : ((Space n × Space n) × ℝ) × ℝ => rayPt z.1.1 (z.2 + z.1.2) :=
    measurable_rayPt.comp (measurable_fst.fst.prodMk (measurable_snd.add measurable_fst.snd))
  exact ((hρm.comp hpt2).div (hρm.comp hpt)).mul
    ((measurable_shiftJac_joint hHm).comp (measurable_fst.snd.prodMk hpt))

/-- The left-hand side of the shift identity as a function of `(ω, s)`. -/
noncomputable def Phi1 (κ : Kernel (Space n × Space n) ℝ) (D₀ : Set (Space n)) (I : Set ℝ)
    (p : (Space n × Space n) × ℝ) : ℝ≥0∞ := κ p.1 (shiftSet p.2 (I ∩ Dray D₀ p.1))

/-- The right-hand side of the shift identity as a function of `(ω, s)`. -/
noncomputable def Phi2 (κ : Kernel (Space n × Space n) ℝ) (ρ : Space n → ℝ)
    (H : Space n → (Space n →L[ℝ] Space n)) (D₀ : Set (Space n)) (I : Set ℝ)
    (p : (Space n × Space n) × ℝ) : ℝ≥0∞ :=
  ∫⁻ t in I ∩ Dray D₀ p.1, ENNReal.ofReal (shiftDens ρ H p.2 p.1 t) ∂κ p.1

theorem measurable_Phi1 (hD₀ : IsOpen D₀) {κ : Kernel (Space n × Space n) ℝ} [IsMarkovKernel κ]
    {I : Set ℝ} (hI : MeasurableSet I) : Measurable (Phi1 κ D₀ I) := by
  unfold Phi1
  set κ' : Kernel ((Space n × Space n) × ℝ) ℝ := κ.comap Prod.fst measurable_fst with hκ'
  have hM1 : MeasurableSet {z : ((Space n × Space n) × ℝ) × ℝ |
      z.2 - z.1.2 ∈ I ∧ rayPt z.1.1 (z.2 - z.1.2) ∈ D₀} := by
    have h1 : Measurable fun z : ((Space n × Space n) × ℝ) × ℝ => z.2 - z.1.2 :=
      measurable_snd.sub measurable_fst.snd
    have h2 : Measurable fun z : ((Space n × Space n) × ℝ) × ℝ => rayPt z.1.1 (z.2 - z.1.2) :=
      measurable_rayPt.comp (measurable_fst.fst.prodMk h1)
    exact (h1 hI).inter (h2 hD₀.measurableSet)
  have := Kernel.measurable_kernel_prodMk_left (κ := κ') hM1
  convert this using 2 with p
  simp only [hκ', Kernel.comap_apply]
  congr 1

theorem measurable_Phi2 (hρm : Measurable ρ) (hD₀ : IsOpen D₀)
    {κ : Kernel (Space n × Space n) ℝ} [IsMarkovKernel κ]
    {H : Space n → (Space n →L[ℝ] Space n)} (hHm : Measurable H) {I : Set ℝ}
    (hI : MeasurableSet I) : Measurable (Phi2 κ ρ H D₀ I) := by
  unfold Phi2
  set κ' : Kernel ((Space n × Space n) × ℝ) ℝ := κ.comap Prod.fst measurable_fst with hκ'
  set M2 : Set (((Space n × Space n) × ℝ) × ℝ) :=
    {z | z.2 ∈ I ∧ rayPt z.1.1 z.2 ∈ D₀} with hM2def
  have hM2 : MeasurableSet M2 := by
    have h2 : Measurable fun z : ((Space n × Space n) × ℝ) × ℝ => rayPt z.1.1 z.2 :=
      measurable_rayPt.comp (measurable_fst.fst.prodMk measurable_snd)
    exact (measurable_snd hI).inter (h2 hD₀.measurableSet)
  have hF : Measurable (Function.uncurry fun (p : (Space n × Space n) × ℝ) (t : ℝ) =>
      M2.indicator (fun z => ENNReal.ofReal (shiftDens ρ H z.1.2 z.1.1 z.2)) (p, t)) :=
    (ENNReal.measurable_ofReal.comp (measurable_shiftDens_joint hρm hHm)).indicator hM2
  have := Measurable.lintegral_kernel_prod_right (κ := κ') hF
  convert this using 2 with p
  rw [← lintegral_indicator (hIDm_aux hD₀ hI p.1)]
  simp only [hκ', Kernel.comap_apply]
  refine lintegral_congr fun t => ?_
  by_cases ht : t ∈ I ∩ Dray D₀ p.1
  · rw [indicator_of_mem ht, indicator_of_mem]
    exact ht
  · rw [indicator_of_notMem ht, indicator_of_notMem]
    exact ht

/-- **Shift identity, almost everywhere form.**  For `q`-a.e. `ω` in the window and Lebesgue-a.e.
`s ∈ (-ε, ε)`, the shift identity holds along the ray `ω` for the fixed set `I`. -/
theorem ae_shift_identity (hu : LipschitzWith 1 u) (hρm : Measurable ρ) (hD₀ : IsOpen D₀)
    (hρD₀ : ∀ x ∈ D₀, 0 < ρ x) (hμ : μ = volume.withDensity fun x => ENNReal.ofReal (ρ x))
    (hdis : IsRayDisintegrationH μ u q κ) {ε : ℝ} (hε : 0 < ε)
    {H : Space n → (Space n →L[ℝ] Space n)} {N : Set (Space n)} (hH : IsRayHessian u ε H N)
    (hHm : Measurable H) (hNm : MeasurableSet N) (hN0 : volume N = 0)
    {α β : ℝ} (hαβ : α < β) {I : Set ℝ} (hI : MeasurableSet I) (hIαβ : I ⊆ Icc α β) :
    ∀ᵐ ω ∂q, ω ∈ WindowSet u ε α β → ∀ᵐ s ∂(volume : Measure ℝ), |s| < ε →
      κ ω (shiftSet s (I ∩ Dray D₀ ω)) =
        ∫⁻ t in I ∩ Dray D₀ ω, ENNReal.ofReal (shiftDens ρ H s ω t) ∂κ ω := by
  set Win := WindowSet u ε α β with hWin
  have hWm : MeasurableSet Win := measurableSet_windowSet hu ε α β
  have hΦ1 := measurable_Phi1 (κ := κ) hD₀ hI
  have hΦ2 := measurable_Phi2 (κ := κ) hρm hD₀ hHm hI
  -- Step A: for each fixed `s`, equality for `q`-a.e. `ω` in the window
  have hA : ∀ s : ℝ, |s| < ε → ∀ᵐ ω ∂q, ω ∈ Win →
      Phi1 κ D₀ I (ω, s) = Phi2 κ ρ H D₀ I (ω, s) := by
    intro s hs
    have hmk : Measurable fun ω : Space n × Space n => (ω, s) :=
      measurable_id.prodMk measurable_const
    have h1 : Measurable fun ω : Space n × Space n => Phi1 κ D₀ I (ω, s) := hΦ1.comp hmk
    have h2 : Measurable fun ω : Space n × Space n => Phi2 κ ρ H D₀ I (ω, s) := hΦ2.comp hmk
    have key : ∀ K : Set (Space n × Space n), MeasurableSet K →
        ∫⁻ ω in K ∩ Win, Phi1 κ D₀ I (ω, s) ∂q = ∫⁻ ω in K ∩ Win, Phi2 κ ρ H D₀ I (ω, s) ∂q :=
      fun K hK =>
        shift_identity hu hρm hD₀ hρD₀ hμ hdis hε hH hHm hNm hN0 hs hαβ (hK.inter hWm)
          inter_subset_right hI hIαβ
    have := ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (μ := q.restrict Win) h1 h2
      (fun K hK _ => by
        rw [Measure.restrict_restrict hK]
        exact key K hK)
    exact (ae_restrict_iff' hWm).1 this
  -- Step B: Fubini in `(s, ω)`
  have hset : MeasurableSet {z : ℝ × (Space n × Space n) | z.2 ∈ Win → |z.1| < ε →
      Phi1 κ D₀ I (z.2, z.1) = Phi2 κ ρ H D₀ I (z.2, z.1)} := by
    have e1 : MeasurableSet {z : ℝ × (Space n × Space n) | z.2 ∈ Win} := measurable_snd hWm
    have e2 : MeasurableSet {z : ℝ × (Space n × Space n) | |z.1| < ε} :=
      measurableSet_lt measurable_fst.abs measurable_const
    have e3 : MeasurableSet {z : ℝ × (Space n × Space n) |
        Phi1 κ D₀ I (z.2, z.1) = Phi2 κ ρ H D₀ I (z.2, z.1)} :=
      measurableSet_eq_fun (hΦ1.comp measurable_swap) (hΦ2.comp measurable_swap)
    exact e1.imp (e2.imp e3)
  have hall : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ ω ∂q, (ω ∈ Win → |s| < ε →
      Phi1 κ D₀ I (ω, s) = Phi2 κ ρ H D₀ I (ω, s)) :=
    Filter.Eventually.of_forall fun s => by
      by_cases hs : |s| < ε
      · filter_upwards [hA s hs] with ω hω hωW _ using hω hωW
      · exact Filter.Eventually.of_forall fun ω _ h => absurd h hs
  have := (Measure.ae_ae_comm (μ := (volume : Measure ℝ)) (ν := q)
    (p := fun s ω => ω ∈ Win → |s| < ε → Phi1 κ D₀ I (ω, s) = Phi2 κ ρ H D₀ I (ω, s)) hset).1 hall
  filter_upwards [this] with ω hω hωW
  filter_upwards [hω] with s hs hsε
  exact hs hωW hsε

end Identity

end CvxBody.NeedleLC
