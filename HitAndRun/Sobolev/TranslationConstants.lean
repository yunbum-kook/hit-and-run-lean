module
public import HitAndRun.Sobolev.TranslationH1
public import HitAndRun.Sobolev.WeightedPoincareTransferEnergy
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory ProbabilityTheory EllipticPdes EllipticPdes.H1Graph Set
open scoped ENNReal
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (c : EuclideanSpace ℝ (Fin n))

theorem translationH1_variance (u : (K.translate c).H1) :
    K.varianceEnergy (K.translationH1 c u) = (K.translate c).varianceEnergy u := by
  apply (ENNReal.toReal_eq_toReal_iff' (K.varianceEnergy_ne_top _)
    ((K.translate c).varianceEnergy_ne_top u)).mp
  change variance (fnL (K.translationH1 c u).val) (K.ambient.restrict K.carrier) =
    variance (fnL u.val) ((K.translate c).ambient.restrict (K.translate c).carrier)
  change variance (K.translationL2 c (fnL u.val)) (K.ambient.restrict K.carrier) = _
  rw [variance_congr (K.translationL2_ae c (fnL u.val))]
  exact K.translate_variance c _ (Lp.aestronglyMeasurable _).aemeasurable

theorem translationH1_gradientEnergy (u : (K.translate c).H1) :
    K.gradientEnergy (K.translationH1 c u) = (K.translate c).gradientEnergy u := by
  simp only [gradientEnergy, translationH1, translationGraph, gradL_mk,
    LinearIsometry.norm_map]

theorem translationH1_weightedGradientEnergy (u : (K.translate c).H1) :
    K.weightedGradientEnergy (K.translationH1 c u) =
      (K.translate c).weightedGradientEnergy u := by
  rw [K.weightedGradientEnergy_eq_norm, (K.translate c).weightedGradientEnergy_eq_norm]
  have he : K.boundaryMultiplier (gradL (K.translationH1 c u).val) =
      K.translationL2 c ((K.translate c).boundaryMultiplier (gradL u.val)) := by
    apply Lp.ext
    filter_upwards [K.boundaryMultiplier_ae (gradL (K.translationH1 c u).val),
      K.translationL2_ae c (gradL u.val),
      K.translationL2_ae c ((K.translate c).boundaryMultiplier (gradL u.val)),
      (K.translate_measurePreserving c).quasiMeasurePreserving.ae
        ((K.translate c).boundaryMultiplier_ae (gradL u.val))] with x h1 h2 h3 h4
    change _ = _ at h4
    rw [h1, h3, h4, K.translate_boundaryDistance]
    change K.boundaryDistance x • (K.translationL2 c (gradL u.val)) x = _
    rw [h2]
  rw [he, LinearIsometry.norm_map]

theorem IsPoincareConstant.translate {C : ℝ≥0∞} (h : K.IsPoincareConstant C) :
    (K.translate c).IsPoincareConstant C := by
  intro u
  have hh := h (K.translationH1 c u)
  rwa [K.translationH1_variance c, K.translationH1_gradientEnergy c] at hh

theorem IsImprovedPoincareConstant.translate {C : ℝ≥0∞}
    (h : K.IsImprovedPoincareConstant C) :
    (K.translate c).IsImprovedPoincareConstant C := by
  intro u
  have hh := h (K.translationH1 c u)
  rwa [K.translationH1_variance c, K.translationH1_weightedGradientEnergy c] at hh

theorem domain_ext {K L : BoundedOpenDomain n} (h : K.carrier = L.carrier) : K = L := by
  cases K
  cases L
  cases h
  rfl

@[simp] theorem translate_neg_cancel : (K.translate c).translate (-c) = K := by
  apply domain_ext
  ext x
  simp only [translate, mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨c + x, ⟨x, hx, rfl⟩, by simp⟩

theorem isPoincareConstant_translate_iff (C : ℝ≥0∞) :
    (K.translate c).IsPoincareConstant C ↔ K.IsPoincareConstant C := by
  constructor
  · intro h
    simpa only [K.translate_neg_cancel c] using h.translate (K.translate c) (-c)
  · exact fun h => h.translate K c

theorem isImprovedPoincareConstant_translate_iff (C : ℝ≥0∞) :
    (K.translate c).IsImprovedPoincareConstant C ↔ K.IsImprovedPoincareConstant C := by
  constructor
  · intro h
    simpa only [K.translate_neg_cancel c] using h.translate (K.translate c) (-c)
  · exact fun h => h.translate K c

theorem poincareConstant_translate : (K.translate c).poincareConstant = K.poincareConstant := by
  unfold poincareConstant
  congr 1
  ext C
  exact K.isPoincareConstant_translate_iff c C

theorem improvedPoincareConstant_translate :
    (K.translate c).improvedPoincareConstant = K.improvedPoincareConstant := by
  unfold improvedPoincareConstant
  congr 1
  ext C
  exact K.isImprovedPoincareConstant_translate_iff c C
end HitAndRun.Sobolev.BoundedOpenDomain
