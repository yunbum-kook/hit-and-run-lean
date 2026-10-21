module
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import CvxBody.Geometry.RayShift

@[expose] public section


/-!
# Consequences of the disintegration of `μ` along rays (WP-H)

For a `1`-Lipschitz `u` on `Space n`, a probability measure `q` on the ray-invariant space
`E × E` (`E = Space n`) and a Markov kernel `κ : Kernel (E × E) ℝ`, the hypothesis
`IsRayDisintegrationH μ u q κ` says that `κ ω` is the law of the `u`-coordinate along the ray with
invariant `ω = (θ, o)`, `t ↦ o + t • θ`.  This file derives the consequences used by
`NeedleLogConcave.lean`:

* `lintegral_strain`: `∫_{Strain} F dμ = ∫ ∫ F (ω.2 + t • ω.1) dκ_ω(t) dq(ω)` for measurable `F`;
* `ae_rayInv_rayPt`: for `q`-a.e. `ω` and `κ ω`-a.e. `t` the point `ω.2 + t • ω.1` is a strain point
  whose invariant is `ω` (so `κ ω` lives on the ray `ω`);
* `ae_notMem_of_null`: `μ`-null sets are null along `κ ω`, for `q`-a.e. `ω`;
* `ae_norm_eq_one`: `‖ω.1‖ = 1` for `q`-a.e. `ω`.
-/

open MeasureTheory ProbabilityTheory Set
open OAI.LeanBlast.KLS CvxBody.Geometry
open scoped ENNReal

namespace CvxBody.NeedleLC

variable {n : ℕ}

/-- The point of the line with invariant `ω = (θ, o)` at parameter `t`: `o + t θ`. -/
def rayPt (ω : Space n × Space n) (t : ℝ) : Space n := ω.2 + t • ω.1

theorem measurable_rayPt : Measurable (fun p : (Space n × Space n) × ℝ => rayPt p.1 p.2) :=
  measurable_fst.snd.add (measurable_snd.smul measurable_fst.fst)

/-- `κ : Kernel (E × E) ℝ` disintegrates `μ` along the rays of `u`, `q` a measure on the
ray-invariant space `E × E`: for every measurable `A ⊆ E` and `B ⊆ E × E`:
`μ (A ∩ Strain u ∩ rayInv u ⁻¹' B) = ∫⁻ ω in B, κ ω {t | ω.2 + t • ω.1 ∈ A} ∂q`. -/
def IsRayDisintegrationH (μ : Measure (Space n)) (u : Space n → ℝ)
    (q : Measure (Space n × Space n)) (κ : Kernel (Space n × Space n) ℝ) : Prop :=
  ∀ A B, MeasurableSet A → MeasurableSet B →
    μ (A ∩ Strain u ∩ rayInv u ⁻¹' B) = ∫⁻ ω in B, κ ω {t | ω.2 + t • ω.1 ∈ A} ∂q

section Disintegration

variable {u : Space n → ℝ} {μ : Measure (Space n)} {q : Measure (Space n × Space n)}
  {κ : Kernel (Space n × Space n) ℝ} [IsProbabilityMeasure q] [IsMarkovKernel κ]

/-- The graph map `(ω, t) ↦ (ω, ω.2 + t ω.1)`. -/
def graphMap (p : (Space n × Space n) × ℝ) : (Space n × Space n) × Space n :=
  (p.1, rayPt p.1 p.2)

theorem measurable_graphMap : Measurable (graphMap (n := n)) :=
  measurable_fst.prodMk measurable_rayPt

theorem compProd_graph_rect {B : Set (Space n × Space n)} {A : Set (Space n)}
    (hB : MeasurableSet B) (hA : MeasurableSet A) :
    (q.compProd κ) (graphMap ⁻¹' (B ×ˢ A)) = ∫⁻ ω in B, κ ω {t | rayPt ω t ∈ A} ∂q := by
  have hS : MeasurableSet (graphMap ⁻¹' (B ×ˢ A)) := measurable_graphMap (hB.prod hA)
  rw [Measure.compProd_apply hS, ← lintegral_indicator hB]
  refine lintegral_congr fun ω => ?_
  by_cases hω : ω ∈ B
  · rw [indicator_of_mem hω]
    congr 1
    ext t
    simp [graphMap, hω]
  · rw [indicator_of_notMem hω]
    have : Prod.mk ω ⁻¹' (graphMap ⁻¹' (B ×ˢ A)) = ∅ := by
      ext t
      simp [graphMap, hω]
    rw [this, measure_empty]

theorem measurable_rayInvGraph (hu : LipschitzWith 1 u) :
    Measurable (fun y : Space n => (rayInv u y, y)) :=
  (measurable_rayInv hu).prodMk measurable_id

theorem map_graph_eq (hu : LipschitzWith 1 u) (hdis : IsRayDisintegrationH μ u q κ) :
    (q.compProd κ).map graphMap =
      (μ.restrict (Strain u)).map (fun y => (rayInv u y, y)) := by
  have hrect : ∀ (B : Set (Space n × Space n)) (A : Set (Space n)), MeasurableSet B →
      MeasurableSet A → ((q.compProd κ).map graphMap) (B ×ˢ A) =
        ((μ.restrict (Strain u)).map (fun y => (rayInv u y, y))) (B ×ˢ A) := by
    intro B A hB hA
    have h : μ (A ∩ Strain u ∩ rayInv u ⁻¹' B) = ∫⁻ ω in B, κ ω {t | rayPt ω t ∈ A} ∂q :=
      hdis A B hA hB
    rw [Measure.map_apply measurable_graphMap (hB.prod hA), compProd_graph_rect hB hA,
      Measure.map_apply (measurable_rayInvGraph hu) (hB.prod hA),
      Measure.restrict_apply ((measurable_rayInvGraph hu) (hB.prod hA)), ← h]
    congr 1
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_prod]
    tauto
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨B, hB, A, hA, rfl⟩
    exact hrect B A hB hA
  · simpa using hrect univ univ MeasurableSet.univ MeasurableSet.univ

/-- For `q`-a.e. `ω` and `κ ω`-a.e. `t`, the point `ω.2 + t • ω.1` is a strain point whose ray
invariant is `ω`. -/
theorem ae_rayInv_rayPt (hu : LipschitzWith 1 u) (hdis : IsRayDisintegrationH μ u q κ) :
    ∀ᵐ ω ∂q, ∀ᵐ t ∂κ ω, rayInv u (rayPt ω t) = ω ∧ rayPt ω t ∈ Strain u := by
  set Gr : Set ((Space n × Space n) × Space n) :=
    {z | rayInv u z.2 = z.1 ∧ z.2 ∈ Strain u} with hGr
  have hGrm : MeasurableSet Gr :=
    (measurableSet_eq_fun ((measurable_rayInv hu).comp measurable_snd) measurable_fst).inter
      ((measurableSet_strain hu).preimage measurable_snd)
  have h0 : ((q.compProd κ).map graphMap) Grᶜ = 0 := by
    rw [map_graph_eq hu hdis, Measure.map_apply (measurable_rayInvGraph hu) hGrm.compl,
      Measure.restrict_apply ((measurable_rayInvGraph hu) hGrm.compl)]
    refine measure_mono_null (fun y hy => ?_) (measure_empty (μ := μ))
    exact absurd ⟨rfl, hy.2⟩ hy.1
  rw [Measure.map_apply measurable_graphMap hGrm.compl] at h0
  have hae : ∀ᵐ p ∂(q.compProd κ), graphMap p ∈ Gr := by
    rw [ae_iff]
    exact h0
  have := Measure.ae_ae_of_ae_compProd hae
  exact this

theorem lintegral_strain (hu : LipschitzWith 1 u) (hdis : IsRayDisintegrationH μ u q κ)
    {F : Space n → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ y in Strain u, F y ∂μ = ∫⁻ ω, ∫⁻ t, F (rayPt ω t) ∂κ ω ∂q := by
  have h1 : ∫⁻ z, F z.2 ∂((μ.restrict (Strain u)).map (fun y => (rayInv u y, y))) =
      ∫⁻ y in Strain u, F y ∂μ :=
    lintegral_map (hF.comp measurable_snd) (measurable_rayInvGraph hu)
  have h2 : ∫⁻ z, F z.2 ∂((q.compProd κ).map graphMap) =
      ∫⁻ p, F (rayPt p.1 p.2) ∂(q.compProd κ) :=
    lintegral_map (hF.comp measurable_snd) measurable_graphMap
  rw [← h1, ← map_graph_eq hu hdis, h2]
  exact Measure.lintegral_compProd (hF.comp measurable_rayPt)

theorem ae_notMem_of_null (hu : LipschitzWith 1 u) (hdis : IsRayDisintegrationH μ u q κ)
    {Z : Set (Space n)} (hZ : MeasurableSet Z) (hZ0 : μ Z = 0) :
    ∀ᵐ ω ∂q, ∀ᵐ t ∂κ ω, rayPt ω t ∉ Z := by
  have h := lintegral_strain hu hdis (F := Z.indicator fun _ => (1 : ℝ≥0∞))
    (measurable_const.indicator hZ)
  have hl : ∫⁻ y in Strain u, Z.indicator (fun _ => (1 : ℝ≥0∞)) y ∂μ = 0 := by
    rw [lintegral_indicator_const hZ, one_mul, Measure.restrict_apply hZ]
    exact measure_mono_null inter_subset_left hZ0
  rw [hl] at h
  have hFm : Measurable fun p : (Space n × Space n) × ℝ =>
      Z.indicator (fun _ => (1 : ℝ≥0∞)) (rayPt p.1 p.2) :=
    (measurable_const.indicator hZ).comp measurable_rayPt
  have hmeas : Measurable fun ω => ∫⁻ t, Z.indicator (fun _ => (1 : ℝ≥0∞)) (rayPt ω t) ∂κ ω :=
    Measurable.lintegral_kernel_prod_right (f := fun ω t =>
      Z.indicator (fun _ => (1 : ℝ≥0∞)) (rayPt ω t)) hFm
  have h1 := (lintegral_eq_zero_iff hmeas).1 h.symm
  filter_upwards [h1] with ω hω
  have hmeas' : Measurable fun t : ℝ => Z.indicator (fun _ => (1 : ℝ≥0∞)) (rayPt ω t) :=
    (measurable_const.indicator hZ).comp (measurable_rayPt.comp (measurable_const.prodMk measurable_id))
  have := (lintegral_eq_zero_iff hmeas').1 hω
  filter_upwards [this] with t ht hmem
  simp [indicator_of_mem hmem] at ht

theorem ae_norm_eq_one (hu : LipschitzWith 1 u) (hdis : IsRayDisintegrationH μ u q κ) :
    ∀ᵐ ω ∂q, ‖ω.1‖ = 1 := by
  filter_upwards [ae_rayInv_rayPt hu hdis] with ω hω
  obtain ⟨t, ht1, ht2⟩ := hω.exists
  have := norm_strainDir ht2
  rw [← ht1]
  exact this

end Disintegration

end CvxBody.NeedleLC
