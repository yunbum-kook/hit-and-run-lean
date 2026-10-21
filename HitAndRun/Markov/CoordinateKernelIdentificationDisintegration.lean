module
public import Mathlib.Probability.Kernel.Disintegration.Unique
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Kernel.CondDistrib
@[expose] public section

/-! Normalized sections disintegrate restricted product measure. -/
namespace HitAndRun.Markov
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite ν]

noncomputable def normalizedSectionKernel (S : Set (A × B)) (hS : MeasurableSet S) :
    Kernel A B where
  toFun a := (ν (Prod.mk a ⁻¹' S))⁻¹ • ν.restrict (Prod.mk a ⁻¹' S)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro T hT
    have hm := (measurable_measure_prodMk_left hS (ν := ν)).inv.mul
      (measurable_measure_prodMk_left ((measurable_snd hT).inter hS) (ν := ν))
    convert hm using 1
    funext a
    simp only [Measure.smul_apply, Measure.restrict_apply hT, smul_eq_mul]
    rfl

instance normalizedSectionKernel_finite (S : Set (A × B)) (hS : MeasurableSet S) :
    IsFiniteKernel (normalizedSectionKernel ν S hS) := by
  constructor
  refine ⟨1, ENNReal.one_lt_top, fun a => ?_⟩
  change ((ν (Prod.mk a ⁻¹' S))⁻¹ • ν.restrict (Prod.mk a ⁻¹' S)) univ ≤ 1
  simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_le_one _

/-- The first marginal of the restricted product has density equal to section mass. -/
theorem restricted_product_fst (S : Set (A × B)) (hS : MeasurableSet S) :
    ((μ.prod ν).restrict S).fst = μ.withDensity (fun a => ν (Prod.mk a ⁻¹' S)) := by
  ext T hT
  rw [Measure.fst_apply hT, Measure.restrict_apply (measurable_fst hT),
    Measure.prod_apply ((measurable_fst hT).inter hS), withDensity_apply _ hT,
    ← lintegral_indicator hT]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ T
  · have he : Prod.mk a ⁻¹' (Prod.fst ⁻¹' T ∩ S) = Prod.mk a ⁻¹' S := by
      ext b
      simp [ha]
    rw [he, indicator_of_mem ha]
  · have he : Prod.mk a ⁻¹' (Prod.fst ⁻¹' T ∩ S) = ∅ := by
      ext b
      simp [ha]
    rw [he, measure_empty, indicator_of_notMem ha]

/-- Finite sections suffice, including zero-mass sections. No probability fallback is assumed. -/
theorem restricted_product_disintegration (S : Set (A × B)) (hS : MeasurableSet S)
    [IsFiniteMeasure ((μ.prod ν).restrict S)]
    (hfinite : ∀ a, ν (Prod.mk a ⁻¹' S) ≠ ⊤) :
    (μ.prod ν).restrict S = ((μ.prod ν).restrict S).fst ⊗ₘ normalizedSectionKernel ν S hS := by
  apply Measure.ext_prod
  intro T U hT hU
  rw [Measure.restrict_apply (hT.prod hU), Measure.prod_apply ((hT.prod hU).inter hS),
    Measure.compProd_apply_prod hT hU, restricted_product_fst μ ν S hS,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_measure_prodMk_left hS)
      ((normalizedSectionKernel ν S hS).measurable_coe hU) hT,
    ← lintegral_indicator hT]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ T
  · simp only [indicator_of_mem ha, Pi.mul_apply]
    change ν (Prod.mk a ⁻¹' (T ×ˢ U ∩ S)) =
      ν (Prod.mk a ⁻¹' S) * ((ν (Prod.mk a ⁻¹' S))⁻¹ •
        ν.restrict (Prod.mk a ⁻¹' S)) U
    rw [Measure.smul_apply, Measure.restrict_apply hU, smul_eq_mul]
    have hpre : Prod.mk a ⁻¹' (T ×ˢ U ∩ S) = U ∩ Prod.mk a ⁻¹' S := by
      ext b
      simp [ha]
    rw [hpre]
    by_cases hz : ν (Prod.mk a ⁻¹' S) = 0
    · have hu : ν (U ∩ Prod.mk a ⁻¹' S) = 0 :=
        measure_mono_null inter_subset_right hz
      simp [hz, hu]
    · rw [← mul_assoc, ENNReal.mul_inv_cancel hz (hfinite a), one_mul]
  · have hpre : Prod.mk a ⁻¹' (T ×ˢ U ∩ S) = ∅ := by
      ext b
      simp [ha]
    simp [hpre, ha]

/-- Transport the explicit section disintegration to any pair of measurable coordinates. -/
theorem condDistrib_eq_normalizedSection {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace B] [Nonempty B] (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (X : Ω → A) (Y : Ω → B) (hX : Measurable X) (hY : Measurable Y)
    (S : Set (A × B)) (hS : MeasurableSet S)
    (hmap : ρ.map (fun x => (X x, Y x)) = (μ.prod ν).restrict S)
    (hfinite : ∀ a, ν (Prod.mk a ⁻¹' S) ≠ ⊤) :
    condDistrib Y X ρ =ᵐ[ρ.map X] normalizedSectionKernel ν S hS := by
  haveI : IsFiniteMeasure ((μ.prod ν).restrict S) := by rw [← hmap]; infer_instance
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hX hY
  rw [hmap, restricted_product_disintegration μ ν S hS hfinite]
  congr 1
  rw [← hmap, Measure.fst_map_prodMk hX hY]

/-- The fiber average is the actual conditional expectation, with no cancellation assumption. -/
theorem condExp_eq_normalizedSection {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace B] [Nonempty B] (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (X : Ω → A) (Y : Ω → B) (hX : Measurable X) (hY : Measurable Y)
    (S : Set (A × B)) (hS : MeasurableSet S)
    (hmap : ρ.map (fun x => (X x, Y x)) = (μ.prod ν).restrict S)
    (hfinite : ∀ a, ν (Prod.mk a ⁻¹' S) ≠ ⊤)
    (f : A × B → ℝ) (hf : Integrable f (ρ.map (fun x => (X x, Y x)))) :
    ρ[fun x => f (X x, Y x) | MeasurableSpace.comap X inferInstance] =ᵐ[ρ]
      fun x => ∫ y, f (X x, y) ∂normalizedSectionKernel ν S hS (X x) := by
  have hcond := condExp_prod_ae_eq_integral_condDistrib' hX hY.aemeasurable hf
  have hk := condDistrib_eq_normalizedSection μ ν ρ X Y hX hY S hS hmap hfinite
  have hk' := ae_of_ae_map hX.aemeasurable hk
  exact hcond.trans (hk'.mono (fun x hx => by dsimp only; rw [hx]))

end HitAndRun.Markov
