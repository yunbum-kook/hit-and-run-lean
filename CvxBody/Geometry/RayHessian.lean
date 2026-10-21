module
public import CvxBody.Geometry.Rays
public import CvxBody.Geometry.ConvexHessianAdapter

@[expose] public section


/-!
# L7: the Hessian of the ray direction field

Fix a `1`-Lipschitz `u` on `Space n` and `ε > 0`, and write `S = raySet u ε`.  Following
`docs/part1/P02-NEEDLE-BLUEPRINT.md` (L7) and its review `P02-NEEDLE-REVIEW-M0.md` (Section 3):

* `rayConvex u ε` is `G = ‖·‖² / (2ε) - inf_{y ∈ S} (upper paraboloid at y)`, written as the finite
  supremum `⨆ y : S, (‖w‖² / (2ε) - rayParaboloid u ε y w)` of affine functions, hence convex
  (`convexOn_rayConvex`); it is finite because the paraboloids lie above `u` (L6);
* at `y ∈ S`, `G` is differentiable with gradient `raySlope u ε y = ε⁻¹ y - strainDir u y`
  (`hasGradientAt_rayConvex`), with the two-sided estimate
  `0 ≤ G w - G y - ⟪raySlope y, w - y⟫ ≤ ‖w - y‖² / ε` (`rayConvex_lower`, `rayConvex_upper`);
* the adapter `ConvexOn.exists_measurable_hessian` for the ported Alexandrov theorem, applied with
  `t = S`, gives the within-set derivative of `gradient G` at almost every point of `S`, hence of
  `strainDir u = ε⁻¹ id - gradient G` on `S`;
* the upper bound `A ≤ 2/ε` of the Alexandrov Hessian `A` follows from the symmetric second differences
  of `G` and the quadratic upper bound, whence `-(1/ε) ≤ H = ε⁻¹ - A ≤ 1/ε`.

Main statement: `exists_measurable_hessian_strainDir`.
-/

namespace CvxBody.Geometry

open OAI.LeanBlast.KLS MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace InnerProductSpace

variable {n : ℕ}

section Envelope

variable (u : Space n → ℝ) (ε : ℝ)

/-- The upper paraboloid touching `u` at `y` (it lies above `u` when `y ∈ raySet u ε`). -/
noncomputable def rayParaboloid (y w : Space n) : ℝ :=
  u y + ⟪strainDir u y, w - y⟫ + ‖w - y‖ ^ 2 / (2 * ε)

/-- The slope of the affine function `‖w‖² / (2ε) - rayParaboloid u ε y w`. -/
noncomputable def raySlope (y : Space n) : Space n := ε⁻¹ • y - strainDir u y

/-- `G = ‖·‖² / (2ε) - inf_y paraboloid_y`, written as a supremum of affine functions. -/
noncomputable def rayConvex (w : Space n) : ℝ :=
  ⨆ y : raySet u ε, (‖w‖ ^ 2 / (2 * ε) - rayParaboloid u ε y w)

variable {u ε}

theorem rayParaboloid_affine (hε : 0 < ε) (y w : Space n) :
    ‖w‖ ^ 2 / (2 * ε) - rayParaboloid u ε y w =
      ⟪raySlope u ε y, w⟫ + (⟪strainDir u y, y⟫ - u y - ‖y‖ ^ 2 / (2 * ε)) := by
  unfold rayParaboloid raySlope
  rw [inner_sub_left, inner_sub_right, norm_sub_sq_real, inner_smul_left, real_inner_comm w y]
  simp only [RCLike.conj_to_real]
  field_simp
  ring

theorem rayParaboloid_ge (hu : LipschitzWith 1 u) (hε : 0 < ε) {y : Space n}
    (hy : y ∈ raySet u ε) (w : Space n) : u w ≤ rayParaboloid u ε y w := by
  have := abs_sub_inner_strainDir_le hu hε hy w
  have := (abs_le.mp this).2
  unfold rayParaboloid
  linarith

theorem rayParaboloid_le (hu : LipschitzWith 1 u) (hε : 0 < ε) {y : Space n}
    (hy : y ∈ raySet u ε) (w : Space n) :
    u y + ⟪strainDir u y, w - y⟫ - ‖w - y‖ ^ 2 / (2 * ε) ≤ u w := by
  have := abs_sub_inner_strainDir_le hu hε hy w
  have := (abs_le.mp this).1
  linarith

theorem rayParaboloid_self (y : Space n) : rayParaboloid u ε y y = u y := by
  simp [rayParaboloid]

theorem bddAbove_rayConvex (hu : LipschitzWith 1 u) (hε : 0 < ε) (w : Space n) :
    BddAbove (range fun y : raySet u ε => ‖w‖ ^ 2 / (2 * ε) - rayParaboloid u ε y w) := by
  refine ⟨‖w‖ ^ 2 / (2 * ε) - u w, ?_⟩
  rintro _ ⟨y, rfl⟩
  have := rayParaboloid_ge hu hε y.2 w
  simp only
  linarith

theorem rayConvex_ge (hu : LipschitzWith 1 u) (hε : 0 < ε) {y : Space n} (hy : y ∈ raySet u ε)
    (w : Space n) : ‖w‖ ^ 2 / (2 * ε) - rayParaboloid u ε y w ≤ rayConvex u ε w :=
  le_ciSup (f := fun y : raySet u ε => ‖w‖ ^ 2 / (2 * ε) - rayParaboloid u ε y w)
    (bddAbove_rayConvex hu hε w) ⟨y, hy⟩

theorem rayConvex_le (hu : LipschitzWith 1 u) (hε : 0 < ε) {y : Space n} (hy : y ∈ raySet u ε)
    (w : Space n) : rayConvex u ε w ≤ ‖w‖ ^ 2 / (2 * ε) - u w := by
  have : Nonempty (raySet u ε) := ⟨⟨y, hy⟩⟩
  refine ciSup_le fun z => ?_
  have := rayParaboloid_ge hu hε z.2 w
  linarith

theorem convexOn_rayConvex (hu : LipschitzWith 1 u) (hε : 0 < ε) :
    ConvexOn ℝ univ (rayConvex u ε) := by
  refine ⟨convex_univ, fun w1 _ w2 _ a b ha hb hab => ?_⟩
  rcases isEmpty_or_nonempty (raySet u ε) with h | h
  · simp [rayConvex]
  · refine ciSup_le fun y' => ?_
    obtain ⟨y, hy⟩ := y'
    show ‖a • w1 + b • w2‖ ^ 2 / (2 * ε) - rayParaboloid u ε y (a • w1 + b • w2) ≤ _
    have e : ∀ w, ‖w‖ ^ 2 / (2 * ε) - rayParaboloid u ε y w =
        ⟪raySlope u ε y, w⟫ + (⟪strainDir u y, y⟫ - u y - ‖y‖ ^ 2 / (2 * ε)) :=
      rayParaboloid_affine hε y
    have h1 := rayConvex_ge hu hε hy w1
    have h2 := rayConvex_ge hu hε hy w2
    simp only [smul_eq_mul]
    rw [e, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    rw [e] at h1 h2
    have : a * (⟪raySlope u ε y, w1⟫ + (⟪strainDir u y, y⟫ - u y - ‖y‖ ^ 2 / (2 * ε))) +
      b * (⟪raySlope u ε y, w2⟫ + (⟪strainDir u y, y⟫ - u y - ‖y‖ ^ 2 / (2 * ε))) =
      a * ⟪raySlope u ε y, w1⟫ + b * ⟪raySlope u ε y, w2⟫ +
        (⟪strainDir u y, y⟫ - u y - ‖y‖ ^ 2 / (2 * ε)) := by
      have : (a + b) * (⟪strainDir u y, y⟫ - u y - ‖y‖ ^ 2 / (2 * ε)) =
        ⟪strainDir u y, y⟫ - u y - ‖y‖ ^ 2 / (2 * ε) := by rw [hab, one_mul]
      linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]


theorem rayConvex_self (hu : LipschitzWith 1 u) (hε : 0 < ε) {y : Space n} (hy : y ∈ raySet u ε) :
    rayConvex u ε y = ‖y‖ ^ 2 / (2 * ε) - u y := by
  refine le_antisymm (rayConvex_le hu hε hy y) ?_
  have := rayConvex_ge hu hε hy y
  rwa [rayParaboloid_self] at this

/-- Subgradient inequality for `rayConvex` at a point of `raySet`. -/
theorem rayConvex_lower (hu : LipschitzWith 1 u) (hε : 0 < ε) {y : Space n}
    (hy : y ∈ raySet u ε) (w : Space n) :
    rayConvex u ε y + ⟪raySlope u ε y, w - y⟫ ≤ rayConvex u ε w := by
  have h1 := rayConvex_ge hu hε hy w
  have h2 := rayConvex_self hu hε hy
  rw [rayParaboloid_affine hε] at h1
  have h3 := rayParaboloid_affine (u := u) hε y y
  rw [rayParaboloid_self] at h3
  rw [inner_sub_right]
  linarith

/-- Quadratic upper bound for `rayConvex` at a point of `raySet`. -/
theorem rayConvex_upper (hu : LipschitzWith 1 u) (hε : 0 < ε) {y : Space n}
    (hy : y ∈ raySet u ε) (w : Space n) :
    rayConvex u ε w ≤ rayConvex u ε y + ⟪raySlope u ε y, w - y⟫ + ‖w - y‖ ^ 2 / ε := by
  have h1 := rayConvex_le hu hε hy w
  have h2 := rayConvex_self hu hε hy
  have h3 := rayParaboloid_le hu hε hy w
  have hw : w = y + (w - y) := by abel
  have h4 : ‖w‖ ^ 2 = ‖y‖ ^ 2 + 2 * ⟪y, w - y⟫ + ‖w - y‖ ^ 2 := by
    conv_lhs => rw [hw]
    rw [norm_add_sq_real]
  unfold raySlope
  rw [inner_sub_left, inner_smul_left]
  simp only [RCLike.conj_to_real]
  have h5 : ‖w‖ ^ 2 / (2 * ε) = ‖y‖ ^ 2 / (2 * ε) + ε⁻¹ * ⟪y, w - y⟫ + ‖w - y‖ ^ 2 / (2 * ε) := by
    rw [h4]; field_simp
  have h6 : ‖w - y‖ ^ 2 / ε = ‖w - y‖ ^ 2 / (2 * ε) + ‖w - y‖ ^ 2 / (2 * ε) := by
    field_simp; ring
  linarith

/-- `rayConvex` is differentiable at a point of `raySet`, with gradient `raySlope`. -/
theorem hasGradientAt_rayConvex (hu : LipschitzWith 1 u) (hε : 0 < ε) {y : Space n}
    (hy : y ∈ raySet u ε) : HasGradientAt (rayConvex u ε) (raySlope u ε y) y := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero]
  have hdual : (InnerProductSpace.toDual ℝ (Space n)) (raySlope u ε y) =
      innerSL ℝ (raySlope u ε y) := rfl
  rw [hdual]
  refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
  have hball : Metric.ball (0 : Space n) (ε * c) ∈ nhds (0 : Space n) :=
    Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [hball] with v hv
  have hv' : ‖v‖ < ε * c := by simpa using hv
  have hlo := rayConvex_lower hu hε hy (y + v)
  have hup := rayConvex_upper hu hε hy (y + v)
  simp only [add_sub_cancel_left] at hlo hup
  simp only [Real.norm_eq_abs, innerSL_apply_apply]
  have hab : |rayConvex u ε (y + v) - rayConvex u ε y - ⟪raySlope u ε y, v⟫| ≤ ‖v‖ ^ 2 / ε := by
    rw [abs_le]; constructor <;> linarith
  refine hab.trans ?_
  rw [div_le_iff₀ hε]
  nlinarith [norm_nonneg v]


theorem secondDiff_rayConvex_le (hu : LipschitzWith 1 u) (hε : 0 < ε) {x : Space n}
    (hx : x ∈ raySet u ε) (v : Space n) {k : ℕ} (hk : 1 ≤ k) :
    secondDiff (rayConvex u ε) k v x ≤ 2 * ‖v‖ ^ 2 / ε := by
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have h1 := rayConvex_upper hu hε hx (x + (k : ℝ)⁻¹ • v)
  have h2 := rayConvex_upper hu hε hx (x - (k : ℝ)⁻¹ • v)
  simp only [add_sub_cancel_left, sub_sub_cancel_left, norm_neg, inner_neg_right, norm_smul,
    Real.norm_eq_abs] at h1 h2
  simp only [secondDiff]
  have h3 : (k : ℝ) ^ 2 * ((|(k : ℝ)⁻¹| * ‖v‖) ^ 2 / ε) = ‖v‖ ^ 2 / ε := by
    rw [abs_inv, Nat.abs_cast]; field_simp
  have h4 : (k : ℝ) ^ 2 * (2 * ((|(k : ℝ)⁻¹| * ‖v‖) ^ 2 / ε)) = 2 * ‖v‖ ^ 2 / ε := by
    rw [abs_inv, Nat.abs_cast]; field_simp
  have h5 : rayConvex u ε (x + (k : ℝ)⁻¹ • v) + rayConvex u ε (x - (k : ℝ)⁻¹ • v) -
      2 * rayConvex u ε x ≤ 2 * ((|(k : ℝ)⁻¹| * ‖v‖) ^ 2 / ε) := by
    linarith
  calc (k : ℝ) ^ 2 * (rayConvex u ε (x + (k : ℝ)⁻¹ • v) + rayConvex u ε (x - (k : ℝ)⁻¹ • v) -
      2 * rayConvex u ε x) ≤ (k : ℝ) ^ 2 * (2 * ((|(k : ℝ)⁻¹| * ‖v‖) ^ 2 / ε)) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = _ := h4


end Envelope

/-- `H` is a Hessian of the ray direction field `strainDir u` on `raySet u ε` away from `N`: at every
`x ∈ raySet u ε \ N`, `strainDir u` has derivative `H x` within `raySet u ε`, `H x` is symmetric, and
`-(1/ε) I ≤ H x ≤ (1/ε) I` as quadratic forms. -/
def IsRayHessian (u : Space n → ℝ) (ε : ℝ) (H : Space n → (Space n →L[ℝ] Space n))
    (N : Set (Space n)) : Prop :=
  ∀ x ∈ raySet u ε \ N,
    HasFDerivWithinAt (strainDir u) (H x) (raySet u ε) x ∧
    (∀ v w, ⟪H x v, w⟫_ℝ = ⟪v, H x w⟫_ℝ) ∧
    ∀ v, -(1 / ε) * ‖v‖ ^ 2 ≤ ⟪H x v, v⟫_ℝ ∧ ⟪H x v, v⟫_ℝ ≤ (1 / ε) * ‖v‖ ^ 2

/-- **L7.** Hessian of the ray direction field on `raySet u ε`: there are a measurable operator-valued
function `H` and a measurable Lebesgue-null set `N` such that `IsRayHessian u ε H N`, that is, at every
`x ∈ raySet u ε \ N`, `strainDir u` has derivative `H x` within `raySet u ε`, `H x` is symmetric, and
`-(1/ε) I ≤ H x ≤ (1/ε) I`. -/
theorem exists_measurable_hessian_strainDir {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (H : Space n → (Space n →L[ℝ] Space n)) (N : Set (Space n)),
      Measurable H ∧ MeasurableSet N ∧ volume N = 0 ∧ IsRayHessian u ε H N := by
  obtain ⟨Hs, hHs, hae⟩ := (convexOn_rayConvex hu hε).exists_measurable_hessian
    (μ := (volume : Measure (Space n)))
  set P : Space n → Prop := fun x => (Hs x).IsPositive ∧
      (fun x' => rayConvex u ε x' - rayConvex u ε x - ⟪gradient (rayConvex u ε) x, x' - x⟫_ℝ
        - ⟪Hs x (x' - x), x' - x⟫_ℝ / 2) =o[𝓝 x] (fun x' => ‖x' - x‖ ^ 2) ∧
      ∀ t : Set (Space n), (∀ x' ∈ t, DifferentiableAt ℝ (rayConvex u ε) x') →
        HasFDerivWithinAt (gradient (rayConvex u ε)) (Hs x) t x with hP
  have hnull : volume {x | ¬ P x} = 0 := ae_iff.mp hae
  refine ⟨fun x => ε⁻¹ • ContinuousLinearMap.id ℝ (Space n) - Hs x,
    toMeasurable volume {x | ¬ P x}, measurable_const.sub hHs, measurableSet_toMeasurable _ _,
    by rw [measure_toMeasurable]; exact hnull, ?_⟩
  rintro x ⟨hx, hxN⟩
  have hPx : P x := by
    by_contra h
    exact hxN (subset_toMeasurable _ _ h)
  obtain ⟨hpos, hexp, hder⟩ := hPx
  have hdiff : ∀ x' ∈ raySet u ε, DifferentiableAt ℝ (rayConvex u ε) x' :=
    fun x' hx' => (hasGradientAt_rayConvex hu hε hx').differentiableAt
  have hS := hder _ hdiff
  have hgrad : ∀ x' ∈ raySet u ε, gradient (rayConvex u ε) x' = raySlope u ε x' :=
    fun x' hx' => (hasGradientAt_rayConvex hu hε hx').gradient
  refine ⟨?_, ?_, ?_⟩
  · have h1 : HasFDerivWithinAt (fun x' => ε⁻¹ • x' - gradient (rayConvex u ε) x')
        (ε⁻¹ • ContinuousLinearMap.id ℝ (Space n) - Hs x) (raySet u ε) x :=
      (((hasFDerivAt_id x).const_smul ε⁻¹).hasFDerivWithinAt).sub hS
    refine h1.congr (fun x' hx' => ?_) ?_
    · beta_reduce; rw [hgrad x' hx']; simp [raySlope]
    · beta_reduce; rw [hgrad x hx]; simp [raySlope]
  · intro v w
    have := hpos.isSymmetric v w
    change ⟪Hs x v, w⟫_ℝ = ⟪v, Hs x w⟫_ℝ at this
    simp only [_root_.sub_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, RCLike.conj_to_real, this]
  · intro v
    have hnn : 0 ≤ ⟪Hs x v, v⟫_ℝ := hpos.inner_nonneg_left v
    have hle : ⟪Hs x v, v⟫_ℝ ≤ 2 * ‖v‖ ^ 2 / ε := by
      refine le_of_tendsto (tendsto_secondDiff hexp v) ?_
      filter_upwards [eventually_ge_atTop 1] with k hk
      exact secondDiff_rayConvex_le hu hε hx v hk
    simp only [_root_.sub_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_left, inner_smul_left, RCLike.conj_to_real,
      real_inner_self_eq_norm_sq]
    have h2 : 2 * ‖v‖ ^ 2 / ε = 2 * (1 / ε * ‖v‖ ^ 2) := by field_simp
    constructor <;> nlinarith [h2, one_div ε]

end CvxBody.Geometry
