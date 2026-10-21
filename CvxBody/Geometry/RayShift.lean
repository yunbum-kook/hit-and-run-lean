module
public import CvxBody.Geometry.RayHessian
public import CvxBody.Geometry.PositiveOperatorMatrix

@[expose] public section


/-!
# L8: shift maps along rays and the area formula

For a `1`-Lipschitz `u` on `Space n`, `ε > 0` and `|s| < ε`, let `Φ_s x = x + s • strainDir u x`
(`rayShift u s`) on `raySet u ε`.  This file proves (`docs/part1/P02-NEEDLE-BLUEPRINT.md`, L8, with the
correction of `P02-NEEDLE-REVIEW-M0.md`, Section 4):

* (a) `injOn_rayShift`: `Φ_s` is injective on `raySet u ε`;
* (b) `rayShift_spec`: `rayInv u (Φ_s x) = rayInv u x`, `u (Φ_s x) = u x + s`,
  `Φ_s x ∈ raySet u (ε - |s|)` and the direction is unchanged;
* (c) `lipschitzOnWith_rayShift`: `Φ_s` is `(1 + 3|s|/ε)`-Lipschitz on `raySet u ε`, so
  `volume_image_rayShift_eq_zero`: it maps null subsets of `raySet u ε` to null sets;
* (d) area formula, for a Hessian `H` away from `N` in the sense of `IsRayHessian u ε H N` (the output
  of L7, `exists_measurable_hessian_strainDir`) and a measurable `B ⊆ raySet u ε \ N`:
  `shiftJac_pos` (`det (1 + s H x) > 0`), `lintegral_image_rayShift`
  (`∫_{Φ_s B} g = ∫_B det(1 + s H) · g ∘ Φ_s`), `volume_image_rayShift`,
  `measure_image_rayShift_withDensity` (density `ρ`, ratio `ρ(Φ_s x) / ρ x`) and
  `measure_image_rayShift_densityMeasure` (the corrected version of the review: density
  `e^{-ψ} 1_D`, `B ⊆ D`, `e^{-∞} := 0`).
-/

namespace CvxBody.Geometry

open OAI.LeanBlast.KLS MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace InnerProductSpace ENNReal

variable {n : ℕ}

/-- The shift map `Φ_s x = x + s • strainDir u x` along the rays. -/
noncomputable def rayShift (u : Space n → ℝ) (s : ℝ) (x : Space n) : Space n :=
  x + s • strainDir u x

theorem rayShift_apply (u : Space n → ℝ) (s : ℝ) (x : Space n) :
    rayShift u s x = x + s • strainDir u x := rfl

/-- **L8(b).** The shift moves `x` along its ray: same invariant, `u` increases by `s`, and the
remaining half-length is `ε - |s|`. -/
theorem rayShift_spec {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε : ℝ} (hε : 0 < ε)
    {x : Space n} (hx : x ∈ raySet u ε) {s : ℝ} (hs : |s| < ε) :
    rayInv u (rayShift u s x) = rayInv u x ∧ u (rayShift u s x) = u x + s ∧
      rayShift u s x ∈ raySet u (ε - |s|) ∧ strainDir u (rayShift u s x) = strainDir u x := by
  obtain ⟨h1, h2, h3⟩ := add_smul_strainDir_mem_raySet hu hε hx hs
  exact ⟨rayInv_add_smul hu hε hx hs, h3, h1, h2⟩

/-- **L8(a).** The shift `Φ_s` is injective on `raySet u ε` for `|s| < ε`. -/
theorem injOn_rayShift {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε : ℝ} (hε : 0 < ε)
    {s : ℝ} (hs : |s| < ε) : InjOn (rayShift u s) (raySet u ε) := by
  intro x hx y hy hxy
  obtain ⟨-, -, -, hdx⟩ := rayShift_spec hu hε hx hs
  obtain ⟨-, -, -, hdy⟩ := rayShift_spec hu hε hy hs
  have hθ : strainDir u x = strainDir u y := by rw [← hdx, ← hdy, hxy]
  have h : x + s • strainDir u x = y + s • strainDir u y := hxy
  rw [← hθ] at h
  exact add_right_cancel h

/-- **L8(c).** `Φ_s` is `(1 + 3|s|/ε)`-Lipschitz on `raySet u ε` (for every `s`). -/
theorem lipschitzOnWith_rayShift {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε : ℝ}
    (hε : 0 < ε) (s : ℝ) :
    LipschitzOnWith (Real.toNNReal (1 + 3 * |s| / ε)) (rayShift u s) (raySet u ε) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have h := (lipschitzOnWith_strainDir hu hε).dist_le_mul x hx y hy
  rw [Real.coe_toNNReal _ (by positivity)] at h ⊢
  simp only [dist_eq_norm] at h ⊢
  have e : rayShift u s x - rayShift u s y = (x - y) + s • (strainDir u x - strainDir u y) := by
    simp only [rayShift_apply, smul_sub]; abel
  rw [e]
  calc ‖(x - y) + s • (strainDir u x - strainDir u y)‖
      ≤ ‖x - y‖ + ‖s • (strainDir u x - strainDir u y)‖ := norm_add_le _ _
    _ = ‖x - y‖ + |s| * ‖strainDir u x - strainDir u y‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖x - y‖ + |s| * (3 / ε * ‖x - y‖) := by gcongr
    _ = (1 + 3 * |s| / ε) * ‖x - y‖ := by ring

/-- **L8(c).** `Φ_s` maps null subsets of `raySet u ε` to null sets. -/
theorem volume_image_rayShift_eq_zero {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε : ℝ}
    (hε : 0 < ε) (s : ℝ) {B : Set (Space n)} (hB : B ⊆ raySet u ε) (h0 : volume B = 0) :
    volume (rayShift u s '' B) = 0 :=
  ((lipschitzOnWith_rayShift hu hε s).mono hB).addHaar_image_eq_zero volume volume le_rfl h0

private theorem operatorEuclideanMatrix_add (A B : Space n →L[ℝ] Space n) :
    operatorEuclideanMatrix (A + B) = operatorEuclideanMatrix A + operatorEuclideanMatrix B := by
  simp [operatorEuclideanMatrix]

private theorem operatorEuclideanMatrix_smul (c : ℝ) (A : Space n →L[ℝ] Space n) :
    operatorEuclideanMatrix (c • A) = c • operatorEuclideanMatrix A := by
  simp [operatorEuclideanMatrix]

private theorem operatorEuclideanMatrix_id :
    operatorEuclideanMatrix (ContinuousLinearMap.id ℝ (Space n)) = 1 := by
  simp [operatorEuclideanMatrix]

/-- `det (1 + s H) > 0` when `H` is symmetric with `-(1/ε) ≤ H ≤ 1/ε` and `|s| < ε`. -/
theorem det_id_add_smul_pos {ε : ℝ} (hε : 0 < ε) {H : Space n →L[ℝ] Space n}
    (hsymm : ∀ v w, ⟪H v, w⟫_ℝ = ⟪v, H w⟫_ℝ)
    (hb : ∀ v, -(1 / ε) * ‖v‖ ^ 2 ≤ ⟪H v, v⟫_ℝ ∧ ⟪H v, v⟫_ℝ ≤ (1 / ε) * ‖v‖ ^ 2)
    {s : ℝ} (hs : |s| < ε) :
    0 < (ContinuousLinearMap.id ℝ (Space n) + s • H).det := by
  set c : ℝ := |s| / ε with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c < 1 := by rw [hc, div_lt_one hε]; exact hs
  set R : Space n →L[ℝ] Space n := c • ContinuousLinearMap.id ℝ (Space n) + s • H with hR
  have hRpos : R.IsPositive := by
    refine ⟨?_, fun v => ?_⟩
    · intro v w
      change ⟪R v, w⟫_ℝ = ⟪v, R w⟫_ℝ
      simp only [hR, _root_.add_apply, _root_.smul_apply,
        ContinuousLinearMap.id_apply, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hsymm v w]
    · have : ⟪R v, v⟫_ℝ = c * ‖v‖ ^ 2 + s * ⟪H v, v⟫_ℝ := by
        simp only [hR, _root_.add_apply, _root_.smul_apply,
          ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left,
          real_inner_self_eq_norm_sq]
      change 0 ≤ ⟪R v, v⟫_ℝ
      rw [this]
      obtain ⟨h1, h2⟩ := hb v
      rcases le_total 0 s with h | h
      · rw [hc, abs_of_nonneg h]
        have : s * (-(1 / ε) * ‖v‖ ^ 2) ≤ s * ⟪H v, v⟫_ℝ := mul_le_mul_of_nonneg_left h1 h
        have e : s / ε * ‖v‖ ^ 2 = -(s * (-(1 / ε) * ‖v‖ ^ 2)) := by ring
        linarith
      · rw [hc, abs_of_nonpos h]
        have : s * ⟪H v, v⟫_ℝ ≥ s * ((1 / ε) * ‖v‖ ^ 2) := mul_le_mul_of_nonpos_left h2 h
        have e : -s / ε * ‖v‖ ^ 2 = -(s * ((1 / ε) * ‖v‖ ^ 2)) := by ring
        linarith
  have hT : ContinuousLinearMap.id ℝ (Space n) + s • H =
      (1 - c) • ContinuousLinearMap.id ℝ (Space n) + R := by
    dsimp only [R]
    module
  have hM : operatorEuclideanMatrix (ContinuousLinearMap.id ℝ (Space n) + s • H) =
      (1 - c) • (1 : Matrix (Fin n) (Fin n) ℝ) + operatorEuclideanMatrix R := by
    rw [hT, operatorEuclideanMatrix_add, operatorEuclideanMatrix_smul, operatorEuclideanMatrix_id]
  have hpd : (operatorEuclideanMatrix (ContinuousLinearMap.id ℝ (Space n) + s • H)).PosDef := by
    rw [hM]
    exact (Matrix.PosDef.one.smul (by linarith)).add_posSemidef
      (operatorEuclideanMatrix_posSemidef R hRpos)
  rw [← operatorEuclideanMatrix_det]
  exact hpd.det_pos


/-! ### L8(d): the area formula -/

/-- The Jacobian determinant of the shift `Φ_s` at `x`: `det (1 + s • H x)`. -/
noncomputable def shiftJac (H : Space n → (Space n →L[ℝ] Space n)) (s : ℝ) (x : Space n) : ℝ :=
  (ContinuousLinearMap.id ℝ (Space n) + s • H x).det

/-- `det (1 + s H x) > 0` for `x ∈ raySet u ε \ N` and `|s| < ε`. -/
theorem shiftJac_pos {u : Space n → ℝ} {ε : ℝ} (hε : 0 < ε)
    {H : Space n → (Space n →L[ℝ] Space n)} {N : Set (Space n)} (hH : IsRayHessian u ε H N)
    {s : ℝ} (hs : |s| < ε) {x : Space n} (hx : x ∈ raySet u ε \ N) : 0 < shiftJac H s x :=
  det_id_add_smul_pos hε (hH x hx).2.1 (hH x hx).2.2 hs

/-- The shift `Φ_s` has derivative `1 + s H x` within `raySet u ε` at `x ∈ raySet u ε \ N`. -/
theorem hasFDerivWithinAt_rayShift {u : Space n → ℝ} {ε : ℝ}
    {H : Space n → (Space n →L[ℝ] Space n)} {N : Set (Space n)} (hH : IsRayHessian u ε H N)
    (s : ℝ) {x : Space n} (hx : x ∈ raySet u ε \ N) :
    HasFDerivWithinAt (rayShift u s) (ContinuousLinearMap.id ℝ (Space n) + s • H x)
      (raySet u ε) x :=
  (hasFDerivWithinAt_id x (raySet u ε)).add ((hH x hx).1.const_smul s)

section Area

variable {u : Space n → ℝ} {ε : ℝ} {H : Space n → (Space n →L[ℝ] Space n)} {N : Set (Space n)}
  {s : ℝ} {B : Set (Space n)}

theorem hasFDerivWithinAt_rayShift_of_subset (hH : IsRayHessian u ε H N) (s : ℝ)
    (hBS : B ⊆ raySet u ε \ N) :
    ∀ x ∈ B, HasFDerivWithinAt (rayShift u s) (ContinuousLinearMap.id ℝ (Space n) + s • H x) B x :=
  fun _ hx => (hasFDerivWithinAt_rayShift hH s (hBS hx)).mono (hBS.trans sdiff_subset)

/-- The image of a measurable `B ⊆ raySet u ε \ N` under `Φ_s` is measurable. -/
theorem measurableSet_image_rayShift (hu : LipschitzWith 1 u) (hε : 0 < ε)
    (hH : IsRayHessian u ε H N) (hs : |s| < ε) (hB : MeasurableSet B)
    (hBS : B ⊆ raySet u ε \ N) : MeasurableSet (rayShift u s '' B) :=
  measurable_image_of_fderivWithin hB (hasFDerivWithinAt_rayShift_of_subset hH s hBS)
    ((injOn_rayShift hu hε hs).mono (hBS.trans sdiff_subset))

/-- **L8(d), area formula (clean version).** For measurable `B ⊆ raySet u ε \ N`, `|s| < ε`, and every
`g : Space n → ℝ≥0∞`,
`∫_{Φ_s '' B} g = ∫_B det(1 + s H x) · g (Φ_s x) dx`. -/
theorem lintegral_image_rayShift (hu : LipschitzWith 1 u) (hε : 0 < ε)
    (hH : IsRayHessian u ε H N) (hs : |s| < ε) (hB : MeasurableSet B)
    (hBS : B ⊆ raySet u ε \ N) (g : Space n → ℝ≥0∞) :
    ∫⁻ y in rayShift u s '' B, g y =
      ∫⁻ x in B, ENNReal.ofReal (shiftJac H s x) * g (rayShift u s x) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hB
    (hasFDerivWithinAt_rayShift_of_subset hH s hBS)
    ((injOn_rayShift hu hε hs).mono (hBS.trans sdiff_subset))]
  refine setLIntegral_congr_fun hB fun x hx => ?_
  have hpos := shiftJac_pos hε hH hs (hBS hx)
  simp only [shiftJac] at hpos ⊢
  rw [abs_of_pos hpos]

/-- **L8(d), volume.** `vol(Φ_s B) = ∫_B det(1 + s H x) dx` for measurable `B ⊆ raySet u ε \ N`. -/
theorem volume_image_rayShift (hu : LipschitzWith 1 u) (hε : 0 < ε)
    (hH : IsRayHessian u ε H N) (hs : |s| < ε) (hB : MeasurableSet B)
    (hBS : B ⊆ raySet u ε \ N) :
    volume (rayShift u s '' B) = ∫⁻ x in B, ENNReal.ofReal (shiftJac H s x) := by
  have := lintegral_image_rayShift hu hε hH hs hB hBS (fun _ => 1)
  simpa using this

/-- **L8(d), density version.** Let `ρ ≥ 0` be measurable, `μ = ρ dx`, and `B ⊆ raySet u ε \ N`
measurable with `ρ > 0` on `B`.  Then
`μ (Φ_s B) = ∫_B g_s dμ` with `g_s x = ρ(Φ_s x) / ρ x · det(1 + s H x)`. -/
theorem measure_image_rayShift_withDensity (hu : LipschitzWith 1 u) (hε : 0 < ε)
    (hH : IsRayHessian u ε H N) (hs : |s| < ε) (hB : MeasurableSet B)
    (hBS : B ⊆ raySet u ε \ N) {ρ : Space n → ℝ} (hρ : Measurable ρ)
    (hρB : ∀ x ∈ B, 0 < ρ x) :
    (volume.withDensity fun x => ENNReal.ofReal (ρ x)) (rayShift u s '' B) =
      ∫⁻ x in B, ENNReal.ofReal (ρ (rayShift u s x) / ρ x * shiftJac H s x)
        ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x)) := by
  have hmeas := measurableSet_image_rayShift hu hε hH hs hB hBS
  rw [withDensity_apply _ hmeas, lintegral_image_rayShift hu hε hH hs hB hBS,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable volume
      (hρ.ennreal_ofReal) _ hB (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine setLIntegral_congr_fun hB fun x hx => ?_
  have hJ := shiftJac_pos hε hH hs (hBS hx)
  have hx0 := hρB x hx
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul hx0.le]
  have e : ρ x * (ρ (rayShift u s x) / ρ x * shiftJac H s x) =
      shiftJac H s x * ρ (rayShift u s x) := by
    field_simp
  rw [e, ENNReal.ofReal_mul hJ.le]

/-- **L8(d), corrected density identity of the review (`μ = e^{-ψ} dx` on a domain `D`).**  For a
measurable `ψ`, a measurable set `D` (the interior of the domain of `ψ`), and a measurable
`B ⊆ raySet u ε \ N` with `B ⊆ D`:
`μ (Φ_s B) = ∫_B g_s dμ` where `μ = densityMeasure (e^{-ψ} 1_D)` and
`g_s x = e^{ψ x - ψ (Φ_s x)} det(1 + s H x)` if `Φ_s x ∈ D` and `0` otherwise
(that is `e^{-∞} := 0`; written with the indicator of `D`). -/
theorem measure_image_rayShift_densityMeasure (hu : LipschitzWith 1 u) (hε : 0 < ε)
    (hH : IsRayHessian u ε H N) (hs : |s| < ε) (hB : MeasurableSet B)
    (hBS : B ⊆ raySet u ε \ N) {ψ : Space n → ℝ} (hψ : Measurable ψ) {D : Set (Space n)}
    (hD : MeasurableSet D) (hBD : B ⊆ D) :
    densityMeasure (D.indicator fun x => Real.exp (-ψ x)) (rayShift u s '' B) =
      ∫⁻ x in B, ENNReal.ofReal (D.indicator (fun y => Real.exp (ψ x - ψ y)) (rayShift u s x) *
          shiftJac H s x) ∂(densityMeasure (D.indicator fun x => Real.exp (-ψ x))) := by
  have hρ : Measurable (D.indicator fun x => Real.exp (-ψ x)) :=
    (Real.measurable_exp.comp hψ.neg).indicator hD
  have h := measure_image_rayShift_withDensity hu hε hH hs hB hBS hρ (fun x hx => by
    simp [Set.indicator_of_mem (hBD hx), Real.exp_pos])
  unfold densityMeasure
  rw [h]
  refine setLIntegral_congr_fun hB fun x hx => ?_
  by_cases hΦ : rayShift u s x ∈ D
  · simp only [Set.indicator_of_mem hΦ, Set.indicator_of_mem (hBD hx)]
    congr 2
    rw [show ψ x - ψ (rayShift u s x) = -ψ (rayShift u s x) - -ψ x by ring, Real.exp_sub]
  · simp [hΦ]

end Area

end CvxBody.Geometry
