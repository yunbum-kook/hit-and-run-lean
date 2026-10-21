module
public import HitAndRun.Sobolev.BoundaryTest
public import HitAndRun.Sobolev.SmoothGraph

/-! Compact interior localization of a genuine locally weak weighted gradient.
No global unweighted Sobolev assumption is made on the original function. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

/-- The actual vector gradient of the localized rough function. -/
def weightedCutoffGradient (η h : E → ℝ) (q : E → E) (x : E) : E :=
  (η x / interiorDistance Ω x) • q x + h x • gradient η x

theorem weightedCutoffGradient_memLp (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    {η h : E → ℝ} {q : E → E} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω)
    (hh : MemLp h 2 (μ.restrict Ω)) (hq : MemLp q 2 (μ.restrict Ω)) :
    MemLp (weightedCutoffGradient (Ω := Ω) η h q) 2 (μ.restrict Ω) := by
  let φ : testFunctions Ω := ⟨η, hη, hηc, hηs⟩
  have ha := (boundaryTest_continuous ho hc φ).memLp_top_of_hasCompactSupport
    (boundaryTest_compact φ) (μ.restrict Ω)
  have hg : Continuous (gradient η) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hη.continuous_fderiv (by simp))
  have hgc : HasCompactSupport (gradient η) := by
    apply hηc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport η)
    intro x hx
    have : fderiv ℝ η x ≠ 0 := by
      intro hz
      exact hx (by simp [gradient, hz])
    exact tsupport_fderiv_subset ℝ (subset_closure this)
  exact (ha.smul hq).add (hh.smul (hg.memLp_top_of_hasCompactSupport hgc _))

theorem weightedCutoff_hasWeakFDerivOn_top (ho : IsOpen Ω)
    {η h : E → ℝ} {q : E → E} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω)
    (hw : HasWeakFDerivOn ⟨Ω, ho⟩ h
      (fun x => innerSL ℝ ((interiorDistance Ω x)⁻¹ • q x)) μ) :
    HasWeakFDerivOn ⊤ (fun x => η x * h x)
      (fun x => innerSL ℝ (weightedCutoffGradient (Ω := Ω) η h q x)) μ := by
  have hp := hw.smul_left hη
  have he : (fun x => η x • innerSL ℝ ((interiorDistance Ω x)⁻¹ • q x) +
      (fderiv ℝ η x).smulRight (h x)) =
      (fun x => innerSL ℝ (weightedCutoffGradient (Ω := Ω) η h q x)) := by
    funext x
    ext v
    simp only [weightedCutoffGradient, map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, real_inner_smul_left, smul_eq_mul, div_eq_mul_inv]
    rw [show inner ℝ (gradient η x) v = fderiv ℝ η x v from
      InnerProductSpace.toDual_symm_apply]
    ring
  rw [he] at hp
  apply hp.top_of_forall_notMem_eq_zero hηc hηs
  · intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  · intro x hx
    have hz : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    have hd : fderiv ℝ η x = 0 := fderiv_of_notMem_tsupport ℝ hx
    simp [weightedCutoffGradient, hz, gradient, hd]

/-- A compact interior cutoff of weighted weak data is a genuine W12 function. -/
theorem exists_weightedCutoff_W12 (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    {η h : E → ℝ} {q : E → E} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω)
    (hh : MemLp h 2 (μ.restrict Ω)) (hq : MemLp q 2 (μ.restrict Ω))
    (hw : HasWeakFDerivOn ⟨Ω, ho⟩ h
      (fun x => innerSL ℝ ((interiorDistance Ω x)⁻¹ • q x)) μ) :
    ∃ U : W12 μ Ω,
      (fnL (U : H1Graph μ Ω) : E → ℝ) =ᵐ[μ.restrict Ω] (fun x => η x * h x) ∧
      (gradL (U : H1Graph μ Ω) : E → E) =ᵐ[μ.restrict Ω]
        weightedCutoffGradient (Ω := Ω) η h q := by
  have hf : MemLp (fun x => η x * h x) 2 (μ.restrict Ω) :=
    (hη.continuous.memLp_top_of_hasCompactSupport hηc _).mul hh
  have hg := weightedCutoffGradient_memLp ho hc hη hηc hηs hh hq
  let U : H1Graph μ Ω := mk (hf.toLp _) (hg.toLp _)
  have huf : (fnL U : E → ℝ) =ᵐ[μ.restrict Ω] (fun x => η x * h x) := hf.coeFn_toLp
  have hug : (gradL U : E → E) =ᵐ[μ.restrict Ω]
      weightedCutoffGradient (Ω := Ω) η h q := hg.coeFn_toLp
  refine ⟨⟨U, (mem_W12_iff_hasWeakFDerivOn ho U).mpr ?_⟩, huf, hug⟩
  have ht := (weightedCutoff_hasWeakFDerivOn_top ho hη hηc hηs hw).mono
    (show (⟨Ω, ho⟩ : TopologicalSpace.Opens E) ≤ ⊤ from le_top)
  apply ht.congr_ae huf.symm
  exact hug.symm.mono fun x hx => congrArg (innerSL ℝ) hx

/-- Vanishing off the domain turns a restricted L2 bound into a global one. -/
theorem memLp_of_restrict_of_zero_off {F : Type*} [NormedAddCommGroup F]
    {f : E → F} (ho : IsOpen Ω) (hf : MemLp f 2 (μ.restrict Ω))
    (hz : ∀ x ∉ Ω, f x = 0) : MemLp f 2 μ := by
  have hi := (memLp_indicator_iff_restrict ho.measurableSet.nullMeasurableSet).mpr hf
  have he : Ω.indicator f = f := by
    funext x
    by_cases hx : x ∈ Ω
    · simp [hx]
    · simp [hx, hz x hx]
  rwa [he] at hi

/-- The localized data actually have a global W12 zero extension, not merely
an abstract graph or a locally Sobolev representative. -/
theorem exists_weightedCutoff_globalW12 (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    {η h : E → ℝ} {q : E → E} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω)
    (hh : MemLp h 2 (μ.restrict Ω)) (hq : MemLp q 2 (μ.restrict Ω))
    (hw : HasWeakFDerivOn ⟨Ω, ho⟩ h
      (fun x => innerSL ℝ ((interiorDistance Ω x)⁻¹ • q x)) μ) :
    ∃ U : W12 μ Set.univ,
      (fnL (U : H1Graph μ Set.univ) : E → ℝ) =ᵐ[μ] (fun x => η x * h x) ∧
      (gradL (U : H1Graph μ Set.univ) : E → E) =ᵐ[μ]
        weightedCutoffGradient (Ω := Ω) η h q := by
  have hf : MemLp (fun x => η x * h x) 2 μ := by
    apply memLp_of_restrict_of_zero_off ho
      ((hη.continuous.memLp_top_of_hasCompactSupport hηc _).mul hh)
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport (fun hn => hx (hηs hn))]
  have hg : MemLp (weightedCutoffGradient (Ω := Ω) η h q) 2 μ := by
    apply memLp_of_restrict_of_zero_off ho
      (weightedCutoffGradient_memLp ho hc hη hηc hηs hh hq)
    intro x hx
    have hn : x ∉ tsupport η := fun hn => hx (hηs hn)
    simp [weightedCutoffGradient, image_eq_zero_of_notMem_tsupport hn,
      gradient, fderiv_of_notMem_tsupport ℝ hn]
  have hfr : MemLp (fun x => η x * h x) 2 (μ.restrict Set.univ) := by simpa using hf
  have hgr : MemLp (weightedCutoffGradient (Ω := Ω) η h q) 2
      (μ.restrict Set.univ) := by simpa using hg
  let U : H1Graph μ Set.univ := mk (hfr.toLp _) (hgr.toLp _)
  have huf : (fnL U : E → ℝ) =ᵐ[μ.restrict Set.univ] (fun x => η x * h x) :=
    hfr.coeFn_toLp
  have hug : (gradL U : E → E) =ᵐ[μ.restrict Set.univ]
      weightedCutoffGradient (Ω := Ω) η h q := hgr.coeFn_toLp
  refine ⟨⟨U, (mem_W12_iff_hasWeakFDerivOn isOpen_univ U).mpr ?_⟩,
    by simpa using huf, by simpa using hug⟩
  apply (weightedCutoff_hasWeakFDerivOn_top ho hη hηc hηs hw).congr_ae huf.symm
  exact hug.symm.mono fun x hx => congrArg (innerSL ℝ) hx
end HitAndRun.Sobolev
