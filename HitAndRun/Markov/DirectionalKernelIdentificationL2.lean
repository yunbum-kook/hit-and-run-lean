module
public import HitAndRun.Markov.DirectionalKernelIdentificationIntegrability
public import HitAndRun.Markov.DirectionalAnnihilationCertificate
public import HitAndRun.Markov.BodyChordKernelTransport
public import HitAndRun.Sobolev.BodyUniform
@[expose] public section

namespace HitAndRun.Markov
open Set MeasureTheory ProbabilityTheory HitAndRun.Geometry HitAndRun.Sobolev
open scoped ENNReal ProbabilityTheory BigOperators
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

theorem directionalProjection_chord_ae (θ : UnitDirection n)
    (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    conditionalProjection (directionalSigma_le θ) f =ᵐ[K.ambient.restrict K.carrier]
      fun x => ∫ y, f y ∂chordLaw K.carrier x θ := by
  have hi : Integrable f (K.ambient.restrict K.carrier) :=
    memLp_one_iff_integrable.1 ((Lp.memLp f).mono_exponent (by norm_num))
  have hc := (Lp.memLp f).condExpL2_ae_eq_condExp (𝕜 := ℝ) (directionalSigma_le θ)
  simp only [Lp.toLp_coeFn] at hc
  apply hc.trans
  have hi' : Integrable (f : EuclideanSpace ℝ (Fin n) → ℝ) (uniformMeasure K.carrier) :=
    K.measure_eq_uniform ▸ hi
  have hc' := condExp_eq_directionalChord θ K.isOpen K.nonempty K.isBounded f hi'
  simpa only [K.measure_eq_uniform] using hc'

/-- Actual body-valued transition realization of each directional L2 projection. -/
theorem directionalProjection_bodyKernel_ae (θ : UnitDirection n)
    (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    K.bodyL2Isometry (conditionalProjection (directionalSigma_le θ) f) =ᵐ[K.bodyUniform]
      fun x => ∫ y : K.carrier, f y.val ∂directionKernel K.carrier K.isOpen.measurableSet
        θ
        (by simpa only [Metric.mem_sphere, dist_zero_right] using θ.property) x := by
  apply (K.bodyL2Isometry_coe _).trans
  have h := K.bodyUniform_measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (directionalProjection_chord_ae K θ f)
  refine h.trans (Filter.Eventually.of_forall (fun x => ?_))
  dsimp only [Function.comp_def]
  exact (directionKernel_integral_subtype K.isOpen K.isBounded _ _ x f).symm

/-- The scalar action is independent of the choice of integrable representative. -/
theorem directionalChord_congr_ae (θ : UnitDirection n)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Integrable f (uniformMeasure K.carrier))
    (hg : Integrable g (uniformMeasure K.carrier))
    (hfg : f =ᵐ[uniformMeasure K.carrier] g) :
    (fun x => ∫ y, f y ∂chordLaw K.carrier x θ)
      =ᵐ[uniformMeasure K.carrier]
    (fun x => ∫ y, g y ∂chordLaw K.carrier x θ) :=
  (condExp_eq_directionalChord θ K.isOpen K.nonempty K.isBounded f hf).symm.trans
    ((condExp_congr_ae hfg).trans
      (condExp_eq_directionalChord θ K.isOpen K.nonempty K.isBounded g hg))

/-- Stationarity in integral form, for every integrable observable. -/
theorem directionalChord_integral_preserved (θ : UnitDirection n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Integrable f (uniformMeasure K.carrier)) :
    (∫ x, (∫ y, f y ∂chordLaw K.carrier x θ)
      ∂uniformMeasure K.carrier) = ∫ x, f x ∂uniformMeasure K.carrier := by
  letI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  rw [← integral_congr_ae (condExp_eq_directionalChord θ K.isOpen K.nonempty K.isBounded f hf)]
  exact integral_condExp (directionalSigma_le θ)

/-- The actual chord kernel annihilates the genuine weak-derivative sphere certificate. -/
theorem sphereCertificate_chord_ae (θ : UnitDirection n)
    (u : VectorField K.ambient K.carrier) :
    (fun x => ∫ y, (sphereCertificate u θ) y ∂chordLaw K.carrier x θ)
      =ᵐ[K.ambient.restrict K.carrier] 0 := by
  have h := (directionalProjection_chord_ae K θ (sphereCertificate u θ)).symm
  rw [sphereCertificate_directional_projection] at h
  exact h.trans (Lp.coeFn_zero ℝ 2 (K.ambient.restrict K.carrier))

end HitAndRun.Markov
