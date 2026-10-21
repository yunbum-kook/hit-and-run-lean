module
public import CvxBody.Analysis.NeedleLogConcaveShift
public import CvxBody.Analysis.NeedleLogConcave1D

@[expose] public section


/-!
# Needle densities are log-concave (L12 of `docs/part1/P02-NEEDLE-BLUEPRINT.md`, WP-H)

Let `u` be `1`-Lipschitz on `Space n`, `ρ` a measurable log-concave function and `μ = ρ dx`.  Suppose
`(q, κ)` disintegrates `μ` along the rays of `u` (`IsRayDisintegrationH`).  Then for `q`-a.e. ray
invariant `ω`, the conditional law `κ ω` of the `u`-coordinate along the ray has a log-concave
density with respect to Lebesgue measure: `needleDensity_logConcave`.

The proof follows `docs/part1/P02-NEEDLE-REVIEW-M0.md`, Section 8:

* `NeedleLogConcaveShift.lean` proves the shift identity (E) of the review from the area formula
  `RayShift.lean` and the disintegration;
* this file turns it, for `q`-a.e. `ω`, into the hypotheses of the one-dimensional theorem
  `exists_logConcave_density` of `NeedleLogConcave1D.lean` (absolute continuity, the shift relation,
  the explicit formula near a good base point, gluing along the ray), using that the Jacobian
  `det (1 + s H)` of the symmetric operator `H` factors into positive affine functions.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open OAI.LeanBlast.KLS CvxBody.Geometry
open scoped ENNReal RealInnerProductSpace InnerProductSpace

namespace CvxBody.NeedleLC

/-- Two finite measures on `ℝ` that agree on all open intervals with rational endpoints agree. -/
theorem measure_eq_of_Ioo_rat {μ₁ μ₂ : Measure ℝ} [IsFiniteMeasure μ₁]
    (h : ∀ a b : ℚ, μ₁ (Ioo (a : ℝ) b) = μ₂ (Ioo (a : ℝ) b)) : μ₁ = μ₂ := by
  refine Measure.ext_of_generateFrom_of_iUnion (⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Ioo (a : ℝ) b})
    (fun k : ℕ => Ioo (((-((k : ℚ) + 1) : ℚ)) : ℝ) (((k : ℚ) + 1 : ℚ) : ℝ))
    Real.borel_eq_generateFrom_Ioo_rat Real.isPiSystem_Ioo_rat ?_ ?_ (fun _ => measure_ne_top _ _) ?_
  · refine eq_univ_of_forall fun x => mem_iUnion.2 ⟨⌈|x|⌉₊, ?_⟩
    have h1 : |x| ≤ (⌈|x|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 := abs_le.1 h1
    simp only [Rat.cast_neg, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, mem_Ioo]
    constructor <;> linarith [h2.1, h2.2]
  · intro k
    simp only [mem_iUnion, mem_singleton_iff]
    exact ⟨-((k : ℚ) + 1), (k : ℚ) + 1, by linarith [(Nat.cast_nonneg k : (0 : ℚ) ≤ k)], rfl⟩
  · intro s hs
    simp only [mem_iUnion, mem_singleton_iff] at hs
    obtain ⟨a, b, -, rfl⟩ := hs
    exact h a b

/-- From the shift identity for rational intervals to all measurable subsets of the window. -/
theorem shift_extend {ν : Measure ℝ} [IsFiniteMeasure ν] {D : Set ℝ} (hD : MeasurableSet D)
    {α β s : ℝ} (G : ℝ → ℝ)
    (h : ∀ a b : ℚ, ν (shiftSet s ((Ioo (a : ℝ) b ∩ Icc α β) ∩ D)) =
      ∫⁻ t in (Ioo (a : ℝ) b ∩ Icc α β) ∩ D, ENNReal.ofReal (G t) ∂ν) :
    ∀ I : Set ℝ, MeasurableSet I → I ⊆ Icc α β →
      ν (shiftSet s (I ∩ D)) = ∫⁻ t in I ∩ D, ENNReal.ofReal (G t) ∂ν := by
  set E := Icc α β ∩ D with hE
  have hEm : MeasurableSet E := measurableSet_Icc.inter hD
  set μ₁ : Measure ℝ := (ν.map (fun t => t - s)).restrict E with hμ₁
  set μ₂ : Measure ℝ := (ν.restrict E).withDensity (fun t => ENNReal.ofReal (G t)) with hμ₂
  have h1 : ∀ X : Set ℝ, MeasurableSet X → μ₁ X = ν (shiftSet s (X ∩ E)) := by
    intro X hX
    rw [hμ₁, Measure.restrict_apply hX, Measure.map_apply (measurable_sub_const s)
      (hX.inter hEm)]
    rfl
  have h2 : ∀ X : Set ℝ, MeasurableSet X → μ₂ X = ∫⁻ t in X ∩ E, ENNReal.ofReal (G t) ∂ν := by
    intro X hX
    rw [hμ₂, withDensity_apply _ hX, Measure.restrict_restrict hX]
  have hμ : μ₁ = μ₂ := by
    refine measure_eq_of_Ioo_rat fun a b => ?_
    rw [h1 _ measurableSet_Ioo, h2 _ measurableSet_Ioo]
    have := h a b
    rwa [inter_assoc] at this
  intro I hI hIαβ
  have e : I ∩ E = I ∩ D := by
    ext x
    simp only [hE, mem_inter_iff]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hIαβ h.1, h.2⟩⟩
  have := congrArg (fun μ => μ I) hμ
  simp only [h1 I hI, h2 I hI, e] at this
  exact this

section Main

variable {n : ℕ} {u : Space n → ℝ} {ρ : Space n → ℝ}

theorem rayPt_convex_comb (ω : Space n × Space n) {a b : ℝ} (x y : ℝ) (hab : a + b = 1) :
    rayPt ω (a * x + b * y) = a • rayPt ω x + b • rayPt ω y := by
  have h1 : ω.2 = a • ω.2 + b • ω.2 := by rw [← add_smul, hab, one_smul]
  simp only [rayPt, smul_add, smul_smul]
  conv_lhs => rw [h1]
  module

theorem isLogConcaveFunction_rayPt (hρ : IsLogConcaveFunction ρ) (ω : Space n × Space n) :
    IsLogConcaveFunction (fun t : ℝ => ρ (rayPt ω t)) := by
  refine isLogConcaveFunction_of_rpow_le (fun t => hρ.nonnegative _) fun x y t ht0 ht1 => ?_
  have := hρ.rpow_le (rayPt ω x) (rayPt ω y) ht0 ht1
  have e : rayPt ω (t • x + (1 - t) • y) = t • rayPt ω x + (1 - t) • rayPt ω y := by
    simpa only [smul_eq_mul] using rayPt_convex_comb ω (a := t) (b := 1 - t) x y (by ring)
  rw [e]
  exact this

theorem measure_compl_interior_posSet (hρ : IsLogConcaveFunction ρ) (hρm : Measurable ρ) :
    (volume.withDensity fun x => ENNReal.ofReal (ρ x)) (interior {x : Space n | 0 < ρ x})ᶜ = 0 := by
  set C : Set (Space n) := {x | 0 < ρ x} with hC
  have hCm : MeasurableSet C := measurableSet_lt measurable_const hρm
  have hCc : Convex ℝ C := hρ.log_concave.1
  have h1 : (volume.withDensity fun x => ENNReal.ofReal (ρ x)) Cᶜ = 0 := by
    rw [withDensity_apply _ hCm.compl]
    refine setLIntegral_eq_zero hCm.compl fun x hx => ?_
    have : ρ x ≤ 0 := not_lt.1 hx
    simp [ENNReal.ofReal_eq_zero, this]
  have h2 : (volume.withDensity fun x => ENNReal.ofReal (ρ x)) (frontier C) = 0 :=
    withDensity_absolutelyContinuous _ _ (hCc.addHaar_frontier volume)
  refine measure_mono_null (fun x hx => ?_) (measure_union_null h1 h2)
  by_cases hxC : x ∈ C
  · refine Or.inr ?_
    exact ⟨subset_closure hxC, hx⟩
  · exact Or.inl hxC

/-- **L12. Needle densities are log-concave.**  Let `u` be `1`-Lipschitz, `ρ` a measurable
log-concave function, `μ = ρ dx`, and `(q, κ)` a disintegration of `μ` along the rays of `u`
(`IsRayDisintegrationH`, with `q` a probability measure and `κ` a Markov kernel).  Then for `q`-a.e.
ray invariant `ω` the law `κ ω` of the `u`-coordinate along the ray has a measurable log-concave
density with respect to Lebesgue measure. -/
theorem needleDensity_logConcave (hu : LipschitzWith 1 u) (hρ : IsLogConcaveFunction ρ)
    (hρm : Measurable ρ) {q : Measure (Space n × Space n)} [IsProbabilityMeasure q]
    {κ : Kernel (Space n × Space n) ℝ} [IsMarkovKernel κ]
    (hdis : IsRayDisintegrationH (volume.withDensity fun x => ENNReal.ofReal (ρ x)) u q κ) :
    ∀ᵐ ω ∂q, ∃ h : ℝ → ℝ, Measurable h ∧ IsLogConcaveFunction h ∧
      κ ω = volume.withDensity (fun t => ENNReal.ofReal (h t)) := by
  set μ : Measure (Space n) := volume.withDensity fun x => ENNReal.ofReal (ρ x) with hμ
  set C : Set (Space n) := {x | 0 < ρ x} with hC
  set D₀ : Set (Space n) := interior C with hD₀
  have hD₀o : IsOpen D₀ := isOpen_interior
  have hD₀c : Convex ℝ D₀ := (hρ.log_concave.1 : Convex ℝ C).interior
  have hρD₀ : ∀ x ∈ D₀, 0 < ρ x := fun x hx => (interior_subset hx : x ∈ C)
  have hμD : μ D₀ᶜ = 0 := measure_compl_interior_posSet hρ hρm
  obtain ⟨H, N, hHm, hNm, hN0, hH⟩ : ∃ (H : ℕ → Space n → (Space n →L[ℝ] Space n))
      (N : ℕ → Set (Space n)), (∀ m : ℕ, Measurable (H m)) ∧
      (∀ m : ℕ, MeasurableSet (N m)) ∧ (∀ m : ℕ, volume (N m) = 0) ∧ ∀ m : ℕ, IsRayHessian u (1 / ((m : ℝ) + 1)) (H m) (N m) := by
    choose H N hHm hNm hN0 hH using fun m : ℕ =>
      exists_measurable_hessian_strainDir hu (show (0 : ℝ) < 1 / ((m : ℝ) + 1) by positivity)
    exact ⟨H, N, hHm, hNm, hN0, hH⟩
  have hμN : ∀ m, μ (N m) = 0 := fun m => withDensity_absolutelyContinuous _ _ (hN0 m)
  have hK := ae_rayInv_rayPt hu hdis
  have hnorm := ae_norm_eq_one hu hdis
  have hD := ae_notMem_of_null hu hdis hD₀o.measurableSet.compl hμD
  have hNall : ∀ᵐ ω ∂q, ∀ m, ∀ᵐ t ∂κ ω, rayPt ω t ∉ N m :=
    ae_all_iff.2 fun m => ae_notMem_of_null hu hdis (hNm m) (hμN m)
  have hshift : ∀ᵐ ω ∂q, ∀ (m : ℕ) (α β a b : ℚ), (α : ℝ) < β →
      ω ∈ WindowSet u (1 / ((m : ℝ) + 1)) α β → ∀ᵐ s ∂(volume : Measure ℝ),
        |s| < 1 / ((m : ℝ) + 1) →
          κ ω (shiftSet s ((Ioo (a : ℝ) b ∩ Icc (α : ℝ) β) ∩ Dray D₀ ω)) =
            ∫⁻ t in (Ioo (a : ℝ) b ∩ Icc (α : ℝ) β) ∩ Dray D₀ ω,
              ENNReal.ofReal (shiftDens ρ (H m) s ω t) ∂κ ω := by
    refine ae_all_iff.2 fun m => ae_all_iff.2 fun α => ae_all_iff.2 fun β =>
      ae_all_iff.2 fun a => ae_all_iff.2 fun b => ?_
    by_cases hαβ : (α : ℝ) < β
    · filter_upwards [ae_shift_identity (κ := κ) hu hρm hD₀o hρD₀ rfl hdis
        (ε := 1 / ((m : ℝ) + 1)) (by positivity) (hH m) (hHm m) (hNm m) (hN0 m) hαβ
        (I := Ioo (a : ℝ) b ∩ Icc (α : ℝ) β) (measurableSet_Ioo.inter measurableSet_Icc)
        inter_subset_right] with ω hω _ hωW using hω hωW
    · exact Filter.Eventually.of_forall fun ω h => absurd h hαβ
  filter_upwards [hK, hnorm, hD, hNall, hshift] with ω hKω hω1 hDω hNω hshω
  set ρ' : ℝ → ℝ := fun t => ρ (rayPt ω t) with hρ'
  have hρ'm : Measurable ρ' := hρm.comp (continuous_rayPt_right ω).measurable
  have hρ'lc : IsLogConcaveFunction ρ' := isLogConcaveFunction_rayPt hρ ω
  have hDo : IsOpen (Dray D₀ ω) := isOpen_Dray hD₀o ω
  have hρ'D : ∀ t ∈ Dray D₀ ω, 0 < ρ' t := fun t ht => hρD₀ _ ht
  have hJo : IsOpen (rayJ u D₀ ω) := isOpen_rayJ hD₀o ω
  have hJc : Convex ℝ (rayJ u D₀ ω) := convex_rayJ hu hD₀c hω1
  have hJD : rayJ u D₀ ω ⊆ Dray D₀ ω := rayJ_subset D₀ ω
  have hνJ : κ ω (rayJ u D₀ ω)ᶜ = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hKω, hDω] with t ht1 ht2 ht3
    exact ht3 (mem_rayJ_of_rayInv hu ht1.1 ht1.2 (not_not.1 ht2))
  let ι := {i : ℕ × ℚ × ℚ // ((i.2.1 : ℝ) < (i.2.2 : ℝ)) ∧
    ω ∈ WindowSet u (1 / ((i.1 : ℝ) + 1)) i.2.1 i.2.2}
  let S : ShiftData n (κ ω) ρ' (Dray D₀ ω) (rayJ u D₀ ω) ι :=
    { ε := fun i => 1 / ((i.1.1 : ℝ) + 1)
      α := fun i => (i.1.2.1 : ℝ)
      β := fun i => (i.1.2.2 : ℝ)
      Jac := fun i s t => shiftJac (H i.1.1) s (rayPt ω t)
      ε_pos := fun i => by positivity
      α_lt := fun i => i.2.1
      jac_meas := fun i =>
        (measurable_shiftJac_joint (hHm i.1.1)).comp
          (measurable_fst.prodMk ((continuous_rayPt_right ω).measurable.comp measurable_snd))
      cover := fun t ht => by
        obtain ⟨m, α, β, hαβ, hα, hβ, hW⟩ := exists_window_of_mem_rayJ hω1 ht
        exact ⟨⟨(m, α, β), hαβ, hW⟩, hα, hβ⟩
      shift := fun i => by
        obtain ⟨⟨m, α, β⟩, hαβ, hW⟩ := i
        have h' : ∀ᵐ s ∂(volume : Measure ℝ), ∀ a b : ℚ, |s| < 1 / ((m : ℝ) + 1) →
            κ ω (shiftSet s ((Ioo (a : ℝ) b ∩ Icc (α : ℝ) β) ∩ Dray D₀ ω)) =
              ∫⁻ t in (Ioo (a : ℝ) b ∩ Icc (α : ℝ) β) ∩ Dray D₀ ω,
                ENNReal.ofReal (shiftDens ρ (H m) s ω t) ∂κ ω :=
          ae_all_iff.2 fun a => ae_all_iff.2 fun b => (hshω m α β a b hαβ hW).mono fun s hs hsε =>
            hs hsε
        filter_upwards [h'] with s hs hsε I hI hIαβ
        exact shift_extend hDo.measurableSet (fun t => shiftDens ρ (H m) s ω t)
          (fun a b => hs a b hsε) I hI hIαβ
      jac := fun i => by
        obtain ⟨⟨m, α, β⟩, hαβ, hW⟩ := i
        filter_upwards [hNω m] with t ht hmem
        have hx : rayPt ω t ∈ raySet u (1 / ((m : ℝ) + 1)) := (hW t hmem.1).1
        obtain ⟨-, hsymm, hbd⟩ := hH m (rayPt ω t) ⟨hx, ht⟩
        obtain ⟨lam, hlam, hdet⟩ := exists_eigen_det (H m (rayPt ω t)) hsymm hbd
        exact ⟨lam, hlam, fun s _ => hdet s⟩ }
  exact exists_logConcave_density S hDo hρ'm hρ'lc hρ'D hJo hJc hJD hνJ

/-- A probability measure with density `h` has `∫ h = 1`. -/
theorem integral_eq_one_of_eq_withDensity {ν : Measure ℝ} [IsProbabilityMeasure ν] {h : ℝ → ℝ}
    (hm : Measurable h) (h0 : ∀ t, 0 ≤ h t)
    (hν : ν = volume.withDensity fun t => ENNReal.ofReal (h t)) : ∫ t, h t = 1 := by
  have hlin : ∫⁻ t, ENNReal.ofReal (h t) = 1 := by
    have := measure_univ (μ := ν)
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    exact this
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0)
    hm.aestronglyMeasurable, hlin]
  simp

/-- **L12, with normalization.**  The log-concave needle density of `needleDensity_logConcave`
can be taken to be a probability density: `∫ h = 1`. -/
theorem needleDensity_logConcave_integral (hu : LipschitzWith 1 u)
    (hρ : IsLogConcaveFunction ρ) (hρm : Measurable ρ) {q : Measure (Space n × Space n)}
    [IsProbabilityMeasure q] {κ : Kernel (Space n × Space n) ℝ} [IsMarkovKernel κ]
    (hdis : IsRayDisintegrationH (volume.withDensity fun x => ENNReal.ofReal (ρ x)) u q κ) :
    ∀ᵐ ω ∂q, ∃ h : ℝ → ℝ, Measurable h ∧ IsLogConcaveFunction h ∧ ∫ t, h t = 1 ∧
      κ ω = volume.withDensity (fun t => ENNReal.ofReal (h t)) := by
  filter_upwards [needleDensity_logConcave hu hρ hρm hdis] with ω ⟨h, hm, hlc, hω⟩
  exact ⟨h, hm, hlc, integral_eq_one_of_eq_withDensity hm hlc.nonnegative hω, hω⟩

end Main

end CvxBody.NeedleLC
