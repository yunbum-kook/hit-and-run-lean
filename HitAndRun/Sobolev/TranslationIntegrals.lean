module
public import HitAndRun.Geometry.TranslatedDomain
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

theorem translate_variance (c : EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : AEMeasurable f ((K.translate c).ambient.restrict (K.translate c).carrier)) :
    variance (fun x => f (c + x)) (K.ambient.restrict K.carrier) =
      variance f ((K.translate c).ambient.restrict (K.translate c).carrier) :=
  (K.translate_measurePreserving c).variance_fun_comp hf

/-- Literal normalized-to-Lebesgue integral conversion, including nonintegrable
functions under the total Bochner integral convention. -/
theorem integral_uniform_eq_volume (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x, f x ∂K.ambient.restrict K.carrier) =
      (volume K.carrier).toReal⁻¹ * ∫ x in K.carrier, f x := by
  rw [K.measure_eq_uniform, uniformMeasure, integral_smul_measure]
  simp [ENNReal.toReal_inv, smul_eq_mul]

theorem integral_volume_eq_uniform (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x in K.carrier, f x) =
      (volume K.carrier).toReal * ∫ x, f x ∂K.ambient.restrict K.carrier := by
  rw [K.integral_uniform_eq_volume]
  have hv := domain_volume_bounds K.isOpen K.nonempty K.isBounded
  have hp : 0 < (volume K.carrier).toReal := ENNReal.toReal_pos hv.1.ne' hv.2.ne
  field_simp

theorem translate_inner_ball {a c : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (h : Metric.ball a r ⊆ K.carrier) :
    Metric.ball (c + a) r ⊆ (K.translate c).carrier := by
  intro x hx
  refine ⟨-c + x, ?_, by simp⟩
  apply h
  change dist (-c + x) a < r
  have he : dist (-c + x) a = dist x (c + a) := by
    simpa only [add_neg_cancel_left] using (isometry_add_left c).dist_eq (-c + x) a |>.symm
  rwa [he]

theorem translate_neg_inner_ball {a : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (h : Metric.ball a r ⊆ K.carrier) :
    Metric.ball 0 r ⊆ (K.translate (-a)).carrier := by
  simpa using K.translate_inner_ball (c := -a) h
end HitAndRun.Sobolev.BoundedOpenDomain
