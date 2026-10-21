module
public import HitAndRun.Markov.DirectionalAnnihilationChart
@[expose] public section

namespace HitAndRun.Markov
open MeasureTheory Set EllipticPdes EllipticPdes.H1Graph
variable {n : ℕ} [NeZero n]

/-- Pullback is used only for compact smooth tests, not assumed for Sobolev functions. -/
noncomputable def rotatedTest {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (θ : HitAndRun.Geometry.UnitDirection n) (φ : testFunctions Ω) :
    testFunctions (univ : Set (EuclideanSpace ℝ (Fin n))) :=
  ⟨(φ : EuclideanSpace ℝ (Fin n) → ℝ) ∘ directionRotation θ,
    φ.2.1.comp (directionRotation θ).toContinuousLinearEquiv.contDiff,
    φ.2.2.1.comp_homeomorph (directionRotation θ).toHomeomorph, subset_univ _⟩

theorem rotatedTest_partial {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (θ : HitAndRun.Geometry.UnitDirection n) (φ : testFunctions Ω)
    (y : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (rotatedTest θ φ : EuclideanSpace ℝ (Fin n) → ℝ) y
      (EuclideanSpace.basisFun (Fin n) ℝ (0 : Fin n)) =
    fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) (directionRotation θ y) θ := by
  have h := ((φ.2.1.differentiable (by simp) _).hasFDerivAt.comp y
    (directionRotation θ).toContinuousLinearEquiv.hasFDerivAt).fderiv
  have h' := congrArg (fun l => l (EuclideanSpace.basisFun (Fin n) ℝ (0 : Fin n))) h
  change fderiv ℝ (rotatedTest θ φ : EuclideanSpace ℝ (Fin n) → ℝ) y
    (EuclideanSpace.basisFun (Fin n) ℝ (0 : Fin n)) =
      fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) (directionRotation θ y)
        (directionRotation θ (EuclideanSpace.basisFun (Fin n) ℝ (0 : Fin n))) at h'
  rw [directionRotation_basis] at h'
  exact h' 

/-- Coordinate cancellation transported by an orthogonal map; no new coarea assertion. -/
theorem integral_directional_cylinder_zero {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (θ : HitAndRun.Geometry.UnitDirection n) (φ : testFunctions Ω)
    (s : Set (EuclideanSpace ℝ (Fin n))) :
    (∫ x in directionQuotient θ ⁻¹' s,
      fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x θ) = 0 := by
  let R := (directionRotation θ).toHomeomorph.toMeasurableEquiv
  let d : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x θ
  have hm := setIntegral_map_equiv (μ := volume) R d (directionQuotient θ ⁻¹' s)
  have hR : MeasurePreserving R volume volume := (directionRotation θ).measurePreserving
  rw [hR.map_eq] at hm
  change (∫ x in directionQuotient θ ⁻¹' s, d x) = 0
  rw [hm]
  let t : Set (OtherCoordinates (0 : Fin n)) :=
    (fun z => directionQuotient θ (directionRotation θ (coordinateInsert (0 : Fin n) (z, 0)))) ⁻¹' s
  have he : R ⁻¹' (directionQuotient θ ⁻¹' s) =
      (fun y => (coordinateChart (0 : Fin n) y).1) ⁻¹' t := by
    ext y
    change directionQuotient θ (R y) ∈ s ↔ _
    simpa [R, t] using (congrArg (fun z => z ∈ s)
      (directionQuotient_rotation_factor θ y)).to_iff
  rw [he]
  have hz := integral_coordinate_cylinder_zero (0 : Fin n) (rotatedTest θ φ) t
  simp only [rotatedTest_partial] at hz
  simpa [d, R] using hz

end HitAndRun.Markov
