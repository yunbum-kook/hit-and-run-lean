module
public import HitAndRun.Markov.CoordinateKernelIdentificationIntegrability
public import HitAndRun.Markov.CoordinateAnnihilationGap
public import HitAndRun.Markov.BodyChordKernelTransport
public import HitAndRun.Sobolev.BodyUniform
@[expose] public section

namespace HitAndRun.Markov
open Set MeasureTheory ProbabilityTheory HitAndRun.Geometry HitAndRun.Sobolev
open scoped ENNReal ProbabilityTheory BigOperators
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

theorem coordinateProjection_chord_ae (i : Fin n)
    (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    conditionalProjection (coordinateSigma_le i) f =ᵐ[K.ambient.restrict K.carrier]
      fun x => ∫ y, f y ∂chordLaw K.carrier x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have hi : Integrable f (K.ambient.restrict K.carrier) :=
    memLp_one_iff_integrable.1 ((Lp.memLp f).mono_exponent (by norm_num))
  have hc := (Lp.memLp f).condExpL2_ae_eq_condExp (𝕜 := ℝ) (coordinateSigma_le i)
  simp only [Lp.toLp_coeFn] at hc
  apply hc.trans
  have hi' : Integrable (f : EuclideanSpace ℝ (Fin n) → ℝ) (uniformMeasure K.carrier) :=
    K.measure_eq_uniform ▸ hi
  have hc' := condExp_eq_coordinateChord i K.isOpen K.nonempty K.isBounded f hi'
  simpa only [K.measure_eq_uniform] using hc'

/-- Actual body-valued transition realization of each coordinate L2 projection. -/
theorem coordinateProjection_bodyKernel_ae (i : Fin n)
    (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    K.bodyL2Isometry (conditionalProjection (coordinateSigma_le i) f) =ᵐ[K.bodyUniform]
      fun x => ∫ y : K.carrier, f y.val ∂directionKernel K.carrier K.isOpen.measurableSet
        (EuclideanSpace.basisFun (Fin n) ℝ i)
        ((EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i) x := by
  apply (K.bodyL2Isometry_coe _).trans
  have h := K.bodyUniform_measurePreserving.quasiMeasurePreserving.ae_eq_comp
    (coordinateProjection_chord_ae K i f)
  refine h.trans (Filter.Eventually.of_forall (fun x => ?_))
  dsimp only [Function.comp_def]
  exact (directionKernel_integral_subtype K.isOpen K.isBounded _ _ x f).symm

/-- The scalar action is independent of the choice of integrable representative. -/
theorem coordinateChord_congr_ae (i : Fin n)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Integrable f (uniformMeasure K.carrier))
    (hg : Integrable g (uniformMeasure K.carrier))
    (hfg : f =ᵐ[uniformMeasure K.carrier] g) :
    (fun x => ∫ y, f y ∂chordLaw K.carrier x (EuclideanSpace.basisFun (Fin n) ℝ i))
      =ᵐ[uniformMeasure K.carrier]
    (fun x => ∫ y, g y ∂chordLaw K.carrier x (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
  (condExp_eq_coordinateChord i K.isOpen K.nonempty K.isBounded f hf).symm.trans
    ((condExp_congr_ae hfg).trans
      (condExp_eq_coordinateChord i K.isOpen K.nonempty K.isBounded g hg))

/-- Stationarity in integral form, for every integrable observable. -/
theorem coordinateChord_integral_preserved (i : Fin n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Integrable f (uniformMeasure K.carrier)) :
    (∫ x, (∫ y, f y ∂chordLaw K.carrier x (EuclideanSpace.basisFun (Fin n) ℝ i))
      ∂uniformMeasure K.carrier) = ∫ x, f x ∂uniformMeasure K.carrier := by
  letI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  rw [← integral_congr_ae (condExp_eq_coordinateChord i K.isOpen K.nonempty K.isBounded f hf)]
  exact integral_condExp (coordinateSigma_le i)

theorem finiteAverageKernel_integral {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Fintype ι] (κ : ι → Kernel A B) (x : A) (f : B → ℝ)
    (hf : ∀ i, Integrable f (κ i x)) :
    (∫ y, f y ∂finiteAverageKernel κ x) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∫ y, f y ∂κ i x := by
  change (∫ y, f y ∂((Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, κ i x)) = _
  rw [integral_smul_measure, integral_finsetSum_measure (fun i _ => hf i)]
  simp

/-- The actual coordinate Hit-and-Run kernel realizes the verified L2 heat-bath operator. -/
theorem coordinateHeatBath_bodyKernel_ae
    (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    K.bodyL2Isometry (coordinateHeatBath K f) =ᵐ[K.bodyUniform]
      fun x => ∫ y : K.carrier, f y.val ∂coordinateHitAndRun K.carrier K.isOpen.measurableSet x := by
  have hi : Integrable f (uniformMeasure K.carrier) := by
    rw [← K.measure_eq_uniform]
    exact memLp_one_iff_integrable.1 ((Lp.memLp f).mono_exponent (by norm_num))
  have hib : ∀ᵐ x ∂K.bodyUniform, ∀ i : Fin n,
      Integrable f (chordLaw K.carrier x.val (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
    have hia : ∀ᵐ x ∂uniformMeasure K.carrier, ∀ i : Fin n,
        Integrable f (chordLaw K.carrier x (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
      Filter.eventually_all.2 (fun i =>
        integrable_coordinateChord_ae i K.isOpen K.nonempty K.isBounded f hi)
    have himap : ∀ᵐ x ∂K.bodyUniform.map Subtype.val, ∀ i : Fin n,
        Integrable f (chordLaw K.carrier x (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
      simpa only [K.bodyUniform_map] using hia
    exact ae_of_ae_map measurable_subtype_coe.aemeasurable himap
  have hp := Filter.eventually_all.2 (fun i : Fin n => coordinateProjection_bodyKernel_ae K i f)
  have he : K.bodyL2Isometry (coordinateHeatBath K f) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, K.bodyL2Isometry (conditionalProjection (coordinateSigma_le i) f) := by
    simp only [coordinateHeatBath, coordinateAverage, map_smul, map_sum, Fintype.card_fin]
  rw [he]
  filter_upwards [hib, hp, Lp.coeFn_smul (n : ℝ)⁻¹
    (∑ i : Fin n, K.bodyL2Isometry (conditionalProjection (coordinateSigma_le i) f)),
    Lp.coeFn_fun_finsetSum (Finset.univ) (fun i : Fin n =>
      K.bodyL2Isometry (conditionalProjection (coordinateSigma_le i) f))]
    with x hix hpx hsm hsum
  rw [hsm, Pi.smul_apply, smul_eq_mul, hsum]
  simp_rw [hpx]
  symm
  have hid : ∀ i : Fin n, Integrable (fun y : K.carrier => f y.val)
      (directionKernel K.carrier K.isOpen.measurableSet
        (EuclideanSpace.basisFun (Fin n) ℝ i)
        ((EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i) x) := by
    intro i
    have hii := hix i
    rw [← directionKernel_map_subtype K.isOpen K.isBounded _
      ((EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i) x,
      (MeasurableEmbedding.subtype_coe K.isOpen.measurableSet).integrable_map_iff] at hii
    exact hii
  simpa only [coordinateHitAndRun, Fintype.card_fin] using
    finiteAverageKernel_integral (fun i : Fin n =>
      directionKernel K.carrier K.isOpen.measurableSet
        (EuclideanSpace.basisFun (Fin n) ℝ i)
        ((EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i)) x (fun y : K.carrier => f y.val) hid

/-- Proposition 2.2: the literal gap bound together with the actual kernel realization. -/
theorem coordinateHitAndRun_source_gap (hC : K.constant < ⊤) :
    (∀ f : Lp ℝ 2 (K.ambient.restrict K.carrier),
      K.bodyL2Isometry (coordinateHeatBath K f) =ᵐ[K.bodyUniform]
        fun x => ∫ y : K.carrier, f y.val ∂coordinateHitAndRun K.carrier K.isOpen.measurableSet x) ∧
    1 / ((n : ℝ) * K.constant.toReal) ≤ spectralGap K (coordinateHeatBath K) :=
  ⟨coordinateHeatBath_bodyKernel_ae K, coordinateHeatBath_spectralGap K hC⟩

end HitAndRun.Markov
