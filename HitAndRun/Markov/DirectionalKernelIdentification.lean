module
public import HitAndRun.Markov.DirectionalKernelIdentificationChart
@[expose] public section

namespace HitAndRun.Markov
open Set MeasureTheory HitAndRun.Geometry HitAndRun.Sobolev
variable {n : ℕ} [NeZero n] (θ : UnitDirection n)

/-- Orthogonal changes of variables preserve the literal normalized chord law. -/
theorem chordLaw_directionRotation (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    chordLaw K x θ =
      (chordLaw (directionRotation θ ⁻¹' K) ((directionRotation θ).symm x)
        (EuclideanSpace.basisFun (Fin n) ℝ (0 : Fin n))).map (directionRotation θ) := by
  have hl : lineChord K x θ = lineChord (directionRotation θ ⁻¹' K)
      ((directionRotation θ).symm x) (EuclideanSpace.basisFun (Fin n) ℝ (0 : Fin n)) := by
    ext t
    simp only [lineChord, mem_setOf_eq, mem_preimage, map_add, map_smul,
      LinearIsometryEquiv.apply_symm_apply, directionRotation_basis]
  ext A hA
  rw [Measure.map_apply (directionRotation θ).continuous.measurable hA,
    chordLaw_apply _ _ _ hA,
    chordLaw_apply _ _ _ (hA.preimage (directionRotation θ).continuous.measurable), ← hl]
  congr 2
  ext t
  simp only [mem_inter_iff, mem_preimage, map_add, map_smul,
    LinearIsometryEquiv.apply_symm_apply, directionRotation_basis]

/-- The actual chord law is an absolute-coordinate section law in the orthogonal chart. -/
theorem chordLaw_eq_directionalSliceLaw (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    chordLaw K x θ =
      (coordinateSliceLaw (0 : Fin n) (directionRotation θ ⁻¹' K)
        (directionalChart θ x).1).map (directionRotation θ) := by
  rw [chordLaw_directionRotation, chordLaw_eq_coordinateSliceLaw]
  rfl

/-- The body's literal pullback to the orthogonal coordinate-product chart. -/
def directionalBody (K : Set (EuclideanSpace ℝ (Fin n))) : Set (OtherCoordinates (0 : Fin n) × ℝ) :=
  directionalInsert θ ⁻¹' K

theorem directionalBody_measurable {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) : MeasurableSet (directionalBody θ K) :=
  hK.preimage (directionalInsert θ).continuous.measurable

theorem directionalChart_preimage_body (K : Set (EuclideanSpace ℝ (Fin n))) :
    directionalChart θ ⁻¹' directionalBody θ K = K := by
  ext x
  change ((directionalChart θ).symm (directionalChart θ x) ∈ K) ↔ x ∈ K
  rw [MeasurableEquiv.symm_apply_apply]

theorem directionalChart_uniform (K : Set (EuclideanSpace ℝ (Fin n))) :
    (uniformMeasure K).map (directionalChart θ) =
      (((volume K)⁻¹ • (volume : Measure (OtherCoordinates (0 : Fin n)))).prod volume).restrict
        (directionalBody θ K) := by
  rw [uniformMeasure, Measure.map_smul, Measure.prod_smul_left, Measure.restrict_smul]
  congr 1
  have hm := (directionalChart_volume θ).map_eq
  rw [← hm, (directionalChart θ).restrict_map, directionalChart_preimage_body]
  exact (directionalChart θ).measurable.aemeasurable

theorem directionalBody_finite_sections {K : Set (EuclideanSpace ℝ (Fin n))}
    (hb : Bornology.IsBounded K) (a : OtherCoordinates (0 : Fin n)) :
    volume (Prod.mk a ⁻¹' directionalBody θ K) ≠ ⊤ := by
  exact coordinateBody_finite_sections (0 : Fin n)
    ((directionRotation θ).isometry.antilipschitzWith.isBounded_preimage hb) a

end HitAndRun.Markov
