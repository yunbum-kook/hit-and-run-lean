module
public import HitAndRun.Sobolev.LinearImageH1
public import HitAndRun.Sobolev.TranslationConstants
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory ProbabilityTheory EllipticPdes EllipticPdes.H1Graph Set
open scoped ENNReal
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
  (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))

theorem linearImageH1_variance (u : (K.linearImage L).H1) :
    K.varianceEnergy (K.linearImageH1 L u) = (K.linearImage L).varianceEnergy u := by
  apply (ENNReal.toReal_eq_toReal_iff' (K.varianceEnergy_ne_top _)
    ((K.linearImage L).varianceEnergy_ne_top u)).mp
  change variance (K.linearImageL2 L (fnL u.val)) (K.ambient.restrict K.carrier) =
    variance (fnL u.val) ((K.linearImage L).ambient.restrict (K.linearImage L).carrier)
  rw [variance_congr (K.linearImageL2_ae L (fnL u.val))]
  exact (K.linearImage_restrict_measurePreserving L).variance_fun_comp
    (Lp.aestronglyMeasurable _).aemeasurable

theorem linearImageH1_gradientEnergy (u : (K.linearImage L).H1) :
    K.gradientEnergy (K.linearImageH1 L u) ≤
      ENNReal.ofReal (‖L.toContinuousLinearMap‖^2) * (K.linearImage L).gradientEnergy u := by
  simp only [gradientEnergy, linearImageH1, linearImageGraph, gradL_mk]
  rw [← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow]
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (norm_nonneg _)
  have h := L.toContinuousLinearMap.adjoint.norm_compLp_le (K.linearImageL2 L (gradL u.val))
  simpa only [LinearIsometryEquiv.norm_map, LinearIsometry.norm_map] using h

theorem IsPoincareConstant.linearImage {C : ℝ≥0∞} (h : K.IsPoincareConstant C) :
    (K.linearImage L).IsPoincareConstant (ENNReal.ofReal (‖L.toContinuousLinearMap‖^2) * C) := by
  intro u
  have hh := h (K.linearImageH1 L u)
  rw [K.linearImageH1_variance L] at hh
  calc
    _ ≤ C * K.gradientEnergy (K.linearImageH1 L u) := hh
    _ ≤ C * (ENNReal.ofReal (‖L.toContinuousLinearMap‖^2) * (K.linearImage L).gradientEnergy u) :=
      by gcongr; exact K.linearImageH1_gradientEnergy L u
    _ = _ := by ac_rfl

@[simp] theorem linearImage_symm_cancel : (K.linearImage L).linearImage L.symm = K := by
  apply domain_ext
  ext x
  simp only [linearImage, mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨L x, ⟨x, hx, rfl⟩, L.symm_apply_apply x⟩

theorem poincareConstant_le_linearImage (hfin : (K.linearImage L).poincareConstant < ⊤) :
    K.poincareConstant ≤ ENNReal.ofReal (‖L.symm.toContinuousLinearMap‖^2) *
      (K.linearImage L).poincareConstant := by
  have h := ((K.linearImage L).poincareConstant_admissible_of_lt_top hfin).linearImage
    (K.linearImage L) L.symm
  rw [K.linearImage_symm_cancel L] at h
  exact K.poincareConstant_le h
end HitAndRun.Sobolev.BoundedOpenDomain
