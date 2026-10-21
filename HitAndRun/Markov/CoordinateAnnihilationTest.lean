module
public import HitAndRun.Markov.CoordinateAnnihilation
public import HitAndRun.Markov.CoordinateAnnihilationChart
public import HitAndRun.Sobolev.CurlEnergyIBP
public import Mathlib.Analysis.Calculus.Deriv.Prod
@[expose] public section

namespace HitAndRun.Markov
open MeasureTheory Set EllipticPdes EllipticPdes.H1Graph

variable {n : ℕ} (i : Fin n)

@[simp] theorem coordinateInsert_at (z : OtherCoordinates i × ℝ) :
    (coordinateInsert i z) i = z.2 := by
  have h := coordinateChart_snd i ((coordinateChart i).symm z)
  simpa only [MeasurableEquiv.apply_symm_apply, coordinateInsert_apply] using h.symm

@[simp] theorem coordinateInsert_other (z : OtherCoordinates i × ℝ)
    (j : {j : Fin n // j ≠ i}) : (coordinateInsert i z) j = z.1 j := by
  have h := coordinateChart_fst i ((coordinateChart i).symm z) j
  simpa only [MeasurableEquiv.apply_symm_apply, coordinateInsert_apply] using h.symm

@[simp] theorem coordinateInsert_unit :
    coordinateInsert i (0, 1) = EuclideanSpace.basisFun (Fin n) ℝ i := by
  apply PiLp.ext
  intro j
  by_cases hj : j = i
  · subst j
    simpa [EuclideanSpace.basisFun_apply] using
      coordinateInsert_at i (0, 1)
  · have h := coordinateInsert_other i (0, 1) ⟨j, hj⟩
    simpa [EuclideanSpace.basisFun_apply, hj] using h

/-- The chart fiber derivative is precisely the original i-th directional derivative. -/
theorem derivative_coordinate_fiber {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (φ : testFunctions Ω) (x : OtherCoordinates i) (t : ℝ) :
    deriv (fun s => (φ : EuclideanSpace ℝ (Fin n) → ℝ) (coordinateInsert i (x, s))) t =
      fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) (coordinateInsert i (x, t))
        (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have hp := HasDerivAt.prodMk (hasDerivAt_const t x) (hasDerivAt_id t)
  have hl := (coordinateInsert i).hasFDerivAt.comp_hasDerivAt t hp
  have hf := (φ.2.1.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t hl
  simpa only [coordinateInsert_unit, Function.comp_def, id_eq] using hf.deriv

/-- Compact support survives restriction to every coordinate line. -/
theorem compactSupport_coordinate_fiber {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (φ : testFunctions Ω) (x : OtherCoordinates i) :
    HasCompactSupport (fun t : ℝ => (φ : EuclideanSpace ℝ (Fin n) → ℝ) (coordinateInsert i (x, t))) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (φ.2.2.1.image (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i))
  intro t ht
  refine ⟨coordinateInsert i (x, t), ?_, coordinateInsert_at i (x, t)⟩
  exact subset_tsupport _ ht

/-- Actual smooth compact tests have zero integral on each full coordinate fiber. -/
theorem integral_coordinate_fiber_zero {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (φ : testFunctions Ω) (x : OtherCoordinates i) :
    (∫ t : ℝ, fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ)
      (coordinateInsert i (x, t)) (EuclideanSpace.basisFun (Fin n) ℝ i)) = 0 := by
  simp_rw [← derivative_coordinate_fiber i φ x]
  apply integral_compact_derivative_zero
  · have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
        (φ : EuclideanSpace ℝ (Fin n) → ℝ) (coordinateInsert i (x, t))) :=
      φ.2.1.comp ((coordinateInsert i).contDiff.comp
        (contDiff_const.prodMk contDiff_id))
    exact hc.of_le (by simp)
  · exact compactSupport_coordinate_fiber i φ x

/-- Fubini gives zero on every cylinder in the actual Euclidean coordinates. -/
theorem integral_coordinate_cylinder_zero {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (φ : testFunctions Ω) (s : Set (OtherCoordinates i)) :
    (∫ y in (fun y => (coordinateChart i y).1) ⁻¹' s,
      fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) y
        (EuclideanSpace.basisFun (Fin n) ℝ i)) = 0 := by
  let d : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) y (EuclideanSpace.basisFun (Fin n) ℝ i)
  have hd : Integrable d :=
    (HitAndRun.Sobolev.derivativeTest φ (EuclideanSpace.basisFun (Fin n) ℝ i)).2.1.continuous
      |>.integrable_of_hasCompactSupport
        (hasCompactSupport_fderiv_apply_of_mem φ.2 _)
  have hi := (coordinateChart_volume i).symm.integrable_comp_of_integrable hd
  have hm := setIntegral_map_equiv (μ := volume.prod volume) (coordinateChart i).symm d
    ((fun y => (coordinateChart i y).1) ⁻¹' s)
  rw [(coordinateChart_volume i).symm.map_eq] at hm
  change (∫ y in (fun y => (coordinateChart i y).1) ⁻¹' s, d y) = 0
  rw [hm]
  have he : (coordinateChart i).symm ⁻¹' ((fun y => (coordinateChart i y).1) ⁻¹' s) =
      s ×ˢ (univ : Set ℝ) := by
    ext z
    simp
  rw [he]
  change (∫ z in s ×ˢ (univ : Set ℝ), (d ∘ (coordinateChart i).symm) z ∂volume.prod volume) = 0
  rw [setIntegral_prod _ hi.integrableOn]
  change (∫ x in s, ∫ t : ℝ in univ,
    fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ)
      (coordinateInsert i (x, t)) (EuclideanSpace.basisFun (Fin n) ℝ i)) = 0
  simp only [setIntegral_univ, integral_coordinate_fiber_zero, integral_zero]

end HitAndRun.Markov
