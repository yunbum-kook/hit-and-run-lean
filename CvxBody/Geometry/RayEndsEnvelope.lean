module
public import CvxBody.Geometry.RaysTouching
public import CvxBody.Geometry.ConvexHessianAdapter
public import CvxBody.Geometry.PositiveOperatorMatrix

@[expose] public section


/-!
# One-sided envelope for the end set (auxiliary file for L9)

This file contains the generic part of the proof that the top ends of the slope-one segments of a
`1`-Lipschitz function are null (`docs/part1/P02-NEEDLE-BLUEPRINT.md`, L9, and
`P02-NEEDLE-REVIEW-M0.md`, Section 5).  It is the one-sided analogue of `RayHessian.lean`:

* `UpperTouching u δ Z θ`: for `z ∈ Z` the paraboloid
  `endParaboloid u δ θ z w = u z + ⟪θ z, w - z⟫ + ‖w - z‖² / (2δ)` lies above `u` (this is the upper
  half of the touching bound L6 and needs only the backward half-segment);
* `endConvex u δ Z θ` is `‖·‖² / (2δ) - inf_{z ∈ Z} endParaboloid z`, written as a supremum of
  affine functions: it is finite and convex (`convexOn_endConvex`);
* if moreover `u` has gradient `θ z` at `z ∈ Z`, then `endConvex` has gradient
  `δ⁻¹ z - θ z` at `z` (`hasGradientAt_endConvex`);
* `le_det_smul_id_add_smul`: `c ^ n ≤ det (c • id + s • A)` for `c > 0`, `s ≥ 0`, `A` positive.
-/

namespace CvxBody.Geometry

open OAI.LeanBlast.KLS MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace InnerProductSpace

variable {n : ℕ}

/-! ### The one-sided upper paraboloid -/

/-- The paraboloid `w ↦ u z + ⟪θ z, w - z⟫ + ‖w - z‖² / (2δ)` through `(z, u z)`. -/
noncomputable def endParaboloid (u : Space n → ℝ) (δ : ℝ) (θ : Space n → Space n)
    (z w : Space n) : ℝ :=
  u z + ⟪θ z, w - z⟫ + ‖w - z‖ ^ 2 / (2 * δ)

/-- The slope `δ⁻¹ z - θ z` of the affine function `‖w‖² / (2δ) - endParaboloid u δ θ z w`. -/
noncomputable def endSlope (δ : ℝ) (θ : Space n → Space n) (z : Space n) : Space n :=
  δ⁻¹ • z - θ z

/-- `G = ‖·‖² / (2δ) - inf_{z ∈ Z} endParaboloid z`, written as a supremum of affine functions. -/
noncomputable def endConvex (u : Space n → ℝ) (δ : ℝ) (Z : Set (Space n))
    (θ : Space n → Space n) (w : Space n) : ℝ :=
  ⨆ z : Z, (‖w‖ ^ 2 / (2 * δ) - endParaboloid u δ θ z w)

/-- All the paraboloids with vertex in `Z` lie above `u`. -/
def UpperTouching (u : Space n → ℝ) (δ : ℝ) (Z : Set (Space n)) (θ : Space n → Space n) :
    Prop :=
  ∀ z ∈ Z, ∀ w : Space n, u w ≤ endParaboloid u δ θ z w

section Envelope

variable {u : Space n → ℝ} {δ : ℝ} {Z : Set (Space n)} {θ : Space n → Space n}

theorem endParaboloid_affine (hδ : 0 < δ) (z w : Space n) :
    ‖w‖ ^ 2 / (2 * δ) - endParaboloid u δ θ z w =
      ⟪endSlope δ θ z, w⟫ + (⟪θ z, z⟫ - u z - ‖z‖ ^ 2 / (2 * δ)) := by
  unfold endParaboloid endSlope
  rw [inner_sub_left, inner_sub_right, norm_sub_sq_real, inner_smul_left, real_inner_comm w z]
  simp only [RCLike.conj_to_real]
  field_simp
  ring

theorem endParaboloid_self (z : Space n) : endParaboloid u δ θ z z = u z := by
  simp [endParaboloid]

theorem bddAbove_endConvex (hT : UpperTouching u δ Z θ) (w : Space n) :
    BddAbove (range fun z : Z => ‖w‖ ^ 2 / (2 * δ) - endParaboloid u δ θ z w) := by
  refine ⟨‖w‖ ^ 2 / (2 * δ) - u w, ?_⟩
  rintro _ ⟨z, rfl⟩
  have := hT z z.2 w
  simp only
  linarith

theorem endConvex_ge (hT : UpperTouching u δ Z θ) {z : Space n} (hz : z ∈ Z) (w : Space n) :
    ‖w‖ ^ 2 / (2 * δ) - endParaboloid u δ θ z w ≤ endConvex u δ Z θ w :=
  le_ciSup (f := fun z : Z => ‖w‖ ^ 2 / (2 * δ) - endParaboloid u δ θ z w)
    (bddAbove_endConvex hT w) ⟨z, hz⟩

theorem endConvex_le (hT : UpperTouching u δ Z θ) {z : Space n} (hz : z ∈ Z) (w : Space n) :
    endConvex u δ Z θ w ≤ ‖w‖ ^ 2 / (2 * δ) - u w := by
  have : Nonempty Z := ⟨⟨z, hz⟩⟩
  refine ciSup_le fun z => ?_
  have := hT z z.2 w
  linarith

theorem convexOn_endConvex (hδ : 0 < δ) (hT : UpperTouching u δ Z θ) :
    ConvexOn ℝ univ (endConvex u δ Z θ) := by
  refine ⟨convex_univ, fun w1 _ w2 _ a b ha hb hab => ?_⟩
  rcases isEmpty_or_nonempty Z with h | h
  · simp [endConvex]
  · refine ciSup_le fun z' => ?_
    obtain ⟨z, hz⟩ := z'
    show ‖a • w1 + b • w2‖ ^ 2 / (2 * δ) - endParaboloid u δ θ z (a • w1 + b • w2) ≤ _
    have e : ∀ w, ‖w‖ ^ 2 / (2 * δ) - endParaboloid u δ θ z w =
        ⟪endSlope δ θ z, w⟫ + (⟪θ z, z⟫ - u z - ‖z‖ ^ 2 / (2 * δ)) :=
      endParaboloid_affine hδ z
    have h1 := endConvex_ge hT hz w1
    have h2 := endConvex_ge hT hz w2
    simp only [smul_eq_mul]
    rw [e, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    rw [e] at h1 h2
    have : a * (⟪endSlope δ θ z, w1⟫ + (⟪θ z, z⟫ - u z - ‖z‖ ^ 2 / (2 * δ))) +
      b * (⟪endSlope δ θ z, w2⟫ + (⟪θ z, z⟫ - u z - ‖z‖ ^ 2 / (2 * δ))) =
      a * ⟪endSlope δ θ z, w1⟫ + b * ⟪endSlope δ θ z, w2⟫ +
        (⟪θ z, z⟫ - u z - ‖z‖ ^ 2 / (2 * δ)) := by
      have : (a + b) * (⟪θ z, z⟫ - u z - ‖z‖ ^ 2 / (2 * δ)) =
        ⟪θ z, z⟫ - u z - ‖z‖ ^ 2 / (2 * δ) := by rw [hab, one_mul]
      linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

theorem endConvex_self (hT : UpperTouching u δ Z θ) {z : Space n} (hz : z ∈ Z) :
    endConvex u δ Z θ z = ‖z‖ ^ 2 / (2 * δ) - u z := by
  refine le_antisymm (endConvex_le hT hz z) ?_
  have := endConvex_ge hT hz z
  rwa [endParaboloid_self] at this

/-- Subgradient inequality for `endConvex` at a point of `Z`. -/
theorem endConvex_lower (hδ : 0 < δ) (hT : UpperTouching u δ Z θ) {z : Space n} (hz : z ∈ Z)
    (w : Space n) :
    endConvex u δ Z θ z + ⟪endSlope δ θ z, w - z⟫ ≤ endConvex u δ Z θ w := by
  have h1 := endConvex_ge hT hz w
  have h2 := endConvex_self hT hz
  rw [endParaboloid_affine hδ] at h1
  have h3 := endParaboloid_affine (u := u) (θ := θ) hδ z z
  rw [endParaboloid_self] at h3
  rw [inner_sub_right]
  linarith

/-- Quadratic upper estimate of `endConvex` at a point of `Z`, in terms of the remainder of `u`. -/
theorem endConvex_upper (hδ : 0 < δ) (hT : UpperTouching u δ Z θ) {z : Space n} (hz : z ∈ Z)
    (w : Space n) :
    endConvex u δ Z θ w ≤ endConvex u δ Z θ z + ⟪endSlope δ θ z, w - z⟫ +
      (‖w - z‖ ^ 2 / (2 * δ) - (u w - u z - ⟪θ z, w - z⟫)) := by
  have h1 := endConvex_le hT hz w
  have h2 := endConvex_self hT hz
  have hw : w = z + (w - z) := by abel
  have h4 : ‖w‖ ^ 2 = ‖z‖ ^ 2 + 2 * ⟪z, w - z⟫ + ‖w - z‖ ^ 2 := by
    conv_lhs => rw [hw]
    rw [norm_add_sq_real]
  unfold endSlope
  rw [inner_sub_left, inner_smul_left]
  simp only [RCLike.conj_to_real]
  have h5 : ‖w‖ ^ 2 / (2 * δ) = ‖z‖ ^ 2 / (2 * δ) + δ⁻¹ * ⟪z, w - z⟫ +
      ‖w - z‖ ^ 2 / (2 * δ) := by
    rw [h4]; field_simp
  linarith

/-- If `u` has gradient `θ z` at `z ∈ Z`, then `endConvex` has gradient `δ⁻¹ z - θ z` at `z`. -/
theorem hasGradientAt_endConvex (hδ : 0 < δ) (hT : UpperTouching u δ Z θ) {z : Space n}
    (hz : z ∈ Z) (hd : HasGradientAt u (θ z) z) :
    HasGradientAt (endConvex u δ Z θ) (endSlope δ θ z) z := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero]
  have hdual : (InnerProductSpace.toDual ℝ (Space n)) (endSlope δ θ z) =
      innerSL ℝ (endSlope δ θ z) := rfl
  rw [hdual]
  have hu0 := hd
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero] at hu0
  have hdual' : (InnerProductSpace.toDual ℝ (Space n)) (θ z) = innerSL ℝ (θ z) := rfl
  rw [hdual'] at hu0
  refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
  have h1 := hu0.def (half_pos hc)
  have hball : Metric.ball (0 : Space n) (δ * c) ∈ nhds (0 : Space n) :=
    Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [h1, hball] with v hv hvb
  have hv' : ‖v‖ < δ * c := by simpa using hvb
  have hlo := endConvex_lower hδ hT hz (z + v)
  have hup := endConvex_upper hδ hT hz (z + v)
  simp only [add_sub_cancel_left] at hlo hup
  simp only [Real.norm_eq_abs, innerSL_apply_apply] at hv ⊢
  have hr : |u (z + v) - u z - ⟪θ z, v⟫| ≤ c / 2 * ‖v‖ := hv
  have hq : ‖v‖ ^ 2 / (2 * δ) ≤ c / 2 * ‖v‖ := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  have hr' := abs_le.mp hr
  rw [abs_le]
  constructor <;> nlinarith [hr'.1, hr'.2]

end Envelope

/-! ### A determinant bound -/

private theorem operatorEuclideanMatrix_add' (A B : Space n →L[ℝ] Space n) :
    operatorEuclideanMatrix (A + B) = operatorEuclideanMatrix A + operatorEuclideanMatrix B := by
  simp [operatorEuclideanMatrix]

private theorem operatorEuclideanMatrix_smul' (c : ℝ) (A : Space n →L[ℝ] Space n) :
    operatorEuclideanMatrix (c • A) = c • operatorEuclideanMatrix A := by
  simp [operatorEuclideanMatrix]

private theorem operatorEuclideanMatrix_id' :
    operatorEuclideanMatrix (ContinuousLinearMap.id ℝ (Space n)) = 1 := by
  simp [operatorEuclideanMatrix]

/-- For a positive semidefinite matrix `B`, `1 ≤ det (1 + B)`. -/
private theorem one_le_det_one_add {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) :
    1 ≤ (1 + B).det := by
  have hspec := positiveMatrix_half_one_add_det_spectral B hB
  have h1 : ((1 / 2 : ℝ) • (1 + B)).det = (1 / 2 : ℝ) ^ n * (1 + B).det := by
    rw [Matrix.det_smul, Fintype.card_fin]
  have h2 : (1 / 2 : ℝ) ^ n ≤ ∏ i, (1 + hB.isHermitian.eigenvalues i) / 2 := by
    have : (1 / 2 : ℝ) ^ n = ∏ _i : Fin n, (1 / 2 : ℝ) := by simp
    rw [this]
    gcongr with i
    have := hB.eigenvalues_nonneg i
    linarith
  rw [← hspec, h1] at h2
  have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  by_contra hcon
  push Not at hcon
  have := mul_lt_mul_of_pos_left hcon hp
  linarith

/-- `c ^ n ≤ det (c • id + s • A)` for `c > 0`, `s ≥ 0` and a positive operator `A`. -/
theorem le_det_smul_id_add_smul {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s) {A : Space n →L[ℝ] Space n}
    (hA : A.IsPositive) :
    c ^ n ≤ (c • ContinuousLinearMap.id ℝ (Space n) + s • A).det := by
  have hM : operatorEuclideanMatrix (c • ContinuousLinearMap.id ℝ (Space n) + s • A) =
      c • (1 + (s / c) • operatorEuclideanMatrix A) := by
    rw [operatorEuclideanMatrix_add', operatorEuclideanMatrix_smul', operatorEuclideanMatrix_smul',
      operatorEuclideanMatrix_id', smul_add, smul_smul, mul_div_cancel₀ _ hc.ne']
  rw [← operatorEuclideanMatrix_det, hM, Matrix.det_smul, Fintype.card_fin]
  have hB : ((s / c) • operatorEuclideanMatrix A).PosSemidef :=
    (operatorEuclideanMatrix_posSemidef A hA).smul (by positivity)
  have := one_le_det_one_add hB
  calc c ^ n = c ^ n * 1 := (mul_one _).symm
    _ ≤ c ^ n * (1 + (s / c) • operatorEuclideanMatrix A).det :=
      mul_le_mul_of_nonneg_left this (by positivity)

end CvxBody.Geometry
