module
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import CvxBody.External.OAI.KLS.Model

@[expose] public section


/-!
# Slope-one segments of a 1-Lipschitz function and two-sided quadratic touching

For a function `u` on `E = Space n` we call a unit vector `θ` a *ray direction of half-length `ε`*
at `x` (`HasRaySlope u ε x θ`) if `u (x + t • θ) = u x + t` for `|t| ≤ ε`.  `raySet u ε` is the set
of points having such a direction.  This file proves the quadratic touching bound (L6 of
`docs/part1/P02-NEEDLE-BLUEPRINT.md`) and its consequences:

* uniqueness of the direction, differentiability of `u` with gradient `θ`;
* the direction map is `(3/ε)`-Lipschitz on `raySet u ε`.
-/

namespace CvxBody.Geometry

open OAI.LeanBlast.KLS
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- `θ` is a unit vector along which `u` has slope one on both sides of `x`, up to distance `ε`. -/
def HasRaySlope (u : Space n → ℝ) (ε : ℝ) (x θ : Space n) : Prop :=
  ‖θ‖ = 1 ∧ ∀ t : ℝ, |t| ≤ ε → u (x + t • θ) = u x + t

/-- Points through which `u` has a slope-one segment of half-length `ε` in some unit direction. -/
def raySet (u : Space n → ℝ) (ε : ℝ) : Set (Space n) :=
  {x | ∃ θ : Space n, ‖θ‖ = 1 ∧ ∀ t : ℝ, |t| ≤ ε → u (x + t • θ) = u x + t}

theorem mem_raySet {u : Space n → ℝ} {ε : ℝ} {x : Space n} :
    x ∈ raySet u ε ↔ ∃ θ, HasRaySlope u ε x θ := Iff.rfl

theorem HasRaySlope.mono {u : Space n → ℝ} {ε ε' : ℝ} {x θ : Space n}
    (h : HasRaySlope u ε x θ) (hε : ε' ≤ ε) : HasRaySlope u ε' x θ :=
  ⟨h.1, fun t ht => h.2 t (ht.trans hε)⟩

/-- Monotonicity: a longer segment contains a shorter one. -/
theorem raySet_mono {u : Space n → ℝ} {ε ε' : ℝ} (hε : ε' ≤ ε) :
    raySet u ε ⊆ raySet u ε' := fun _ ⟨θ, h⟩ => ⟨θ, HasRaySlope.mono ⟨h.1, h.2⟩ hε⟩

/-- Square-root estimate: `‖v + ε θ‖ ≤ ε + ⟪θ, v⟫ + ‖v‖² / (2ε)` for a unit vector `θ`. -/
theorem norm_add_smul_le {θ v : Space n} (hθ : ‖θ‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ‖v + ε • θ‖ ≤ ε + ⟪θ, v⟫ + ‖v‖ ^ 2 / (2 * ε) := by
  have hsq : ‖v + ε • θ‖ ^ 2 = ‖v‖ ^ 2 + 2 * ε * ⟪θ, v⟫ + ε ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, hθ, real_inner_comm]
    simp [Real.norm_eq_abs, sq_abs]; ring
  set a : ℝ := ⟪θ, v⟫ + ‖v‖ ^ 2 / (2 * ε) with ha
  have hcs : |⟪θ, v⟫| ≤ ‖v‖ := by
    simpa [hθ] using abs_real_inner_le_norm θ v
  have hb : 0 ≤ ε + a := by
    have h1 : -‖v‖ ≤ ⟪θ, v⟫ := (abs_le.mp hcs).1
    have h2 : 0 ≤ (ε - ‖v‖) ^ 2 / (2 * ε) := by positivity
    have h3 : (ε - ‖v‖) ^ 2 / (2 * ε) = ε / 2 - ‖v‖ + ‖v‖ ^ 2 / (2 * ε) := by
      field_simp; ring
    rw [ha]; linarith
  have h4 : ‖v + ε • θ‖ ^ 2 ≤ (ε + a) ^ 2 := by
    rw [hsq]
    have : (ε + a) ^ 2 = ε ^ 2 + 2 * ε * a + a ^ 2 := by ring
    have h5 : 2 * ε * a = 2 * ε * ⟪θ, v⟫ + ‖v‖ ^ 2 := by
      rw [ha]; field_simp
    nlinarith [sq_nonneg a]
  have := (pow_le_pow_iff_left₀ (norm_nonneg _) hb (two_ne_zero)).mp h4
  linarith

/-- **L6.** Two-sided quadratic touching at points with a slope-one segment of half-length `ε`. -/
theorem abs_sub_inner_le_of_hasRaySlope {u : Space n → ℝ} (hu : LipschitzWith 1 u)
    {ε : ℝ} (hε : 0 < ε) {x θ : Space n} (h : HasRaySlope u ε x θ) (w : Space n) :
    |u w - u x - ⟪θ, w - x⟫| ≤ ‖w - x‖ ^ 2 / (2 * ε) := by
  have hθ := h.1
  have hup : u w ≤ u x + ⟪θ, w - x⟫ + ‖w - x‖ ^ 2 / (2 * ε) := by
    have h1 := h.2 (-ε) (by simp [abs_of_pos hε])
    have h2 := hu.dist_le_mul w (x + (-ε) • θ)
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul] at h2
    have h3 : w - (x + (-ε) • θ) = (w - x) + ε • θ := by
      rw [neg_smul]; abel
    rw [h3] at h2
    have h4 := norm_add_smul_le (v := w - x) hθ hε
    have := (abs_le.mp h2).2
    linarith
  have hlow : u x + ⟪θ, w - x⟫ - ‖w - x‖ ^ 2 / (2 * ε) ≤ u w := by
    have h1 := h.2 ε (by simp [abs_of_pos hε])
    have h2 := hu.dist_le_mul w (x + ε • θ)
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul] at h2
    have h3 : w - (x + ε • θ) = (w - x) + ε • (-θ) := by
      rw [smul_neg]; abel
    rw [h3] at h2
    have h4 := norm_add_smul_le (v := w - x) (θ := -θ) (by simpa using hθ) hε
    rw [inner_neg_left] at h4
    have := (abs_le.mp h2).1
    linarith
  rw [abs_le]; constructor <;> linarith

/-- The direction of a slope-one segment of half-length `ε > 0` is unique. -/
theorem HasRaySlope.eq {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε ε' : ℝ}
    (hε : 0 < ε) (hε' : 0 < ε') {x θ θ' : Space n} (h : HasRaySlope u ε x θ)
    (h' : HasRaySlope u ε' x θ') : θ = θ' := by
  have hm := lt_min hε hε'
  have a := abs_sub_inner_le_of_hasRaySlope hu hm (h.mono (min_le_left _ _))
  have b := abs_sub_inner_le_of_hasRaySlope hu hm (h'.mono (min_le_right _ _))
  set δ : ℝ := min ε ε' with hδ
  set d : Space n := θ - θ' with hd
  -- evaluate at `w = x + (δ/2) • d`
  have key : ∀ w : Space n, |⟪d, w - x⟫| ≤ ‖w - x‖ ^ 2 / δ := by
    intro w
    have e : ⟪d, w - x⟫ = -(u w - u x - ⟪θ, w - x⟫) + (u w - u x - ⟪θ', w - x⟫) := by
      rw [hd, inner_sub_left]; ring
    have := abs_add_le (-(u w - u x - ⟪θ, w - x⟫)) (u w - u x - ⟪θ', w - x⟫)
    rw [← e, abs_neg] at this
    have t1 := a w
    have t2 := b w
    have : ‖w - x‖ ^ 2 / δ = ‖w - x‖ ^ 2 / (2 * δ) + ‖w - x‖ ^ 2 / (2 * δ) := by
      field_simp; ring
    linarith
  by_contra hne
  have hdne : d ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
  have hpos : 0 < ‖d‖ := norm_pos_iff.mpr hdne
  have := key (x + (δ / 2) • d)
  have e1 : x + (δ / 2) • d - x = (δ / 2) • d := by abel
  rw [e1, inner_smul_right, real_inner_self_eq_norm_sq, norm_smul] at this
  rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < δ / 2)] at this
  rw [abs_of_nonneg (by positivity)] at this
  have h7 : δ / 2 * ‖d‖ ^ 2 ≤ (δ / 2 * ‖d‖) ^ 2 / δ := this
  have h8 : (δ / 2 * ‖d‖) ^ 2 / δ = δ / 4 * ‖d‖ ^ 2 := by field_simp; ring
  rw [h8] at h7
  have : 0 < δ / 4 * ‖d‖ ^ 2 := by positivity
  nlinarith

/-- Differentiability at a point of `raySet u ε`, with gradient the ray direction. -/
theorem HasRaySlope.hasGradientAt {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε : ℝ}
    (hε : 0 < ε) {x θ : Space n} (h : HasRaySlope u ε x θ) : HasGradientAt u θ x := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero]
  have hdual : (InnerProductSpace.toDual ℝ (Space n)) θ = innerSL ℝ θ := rfl
  rw [hdual]
  refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
  have hball : Metric.ball (0 : Space n) (2 * ε * c) ∈ nhds (0 : Space n) :=
    Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [hball] with v hv
  have hv' : ‖v‖ < 2 * ε * c := by simpa using hv
  have := abs_sub_inner_le_of_hasRaySlope hu hε h (x + v)
  simp only [add_sub_cancel_left] at this
  simp only [Real.norm_eq_abs, innerSL_apply_apply]
  refine this.trans ?_
  rw [div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg v]

theorem HasRaySlope.hasFDerivAt {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε : ℝ}
    (hε : 0 < ε) {x θ : Space n} (h : HasRaySlope u ε x θ) :
    HasFDerivAt u (innerSL ℝ θ) x :=
  (h.hasGradientAt hu hε)

theorem HasRaySlope.gradient_eq {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε : ℝ}
    (hε : 0 < ε) {x θ : Space n} (h : HasRaySlope u ε x θ) : gradient u x = θ :=
  (h.hasGradientAt hu hε).gradient

/-- On `raySet u ε` the direction field is `(3/ε)`-Lipschitz (the constant proved is `3/ε`). -/
theorem HasRaySlope.dist_le {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε : ℝ}
    (hε : 0 < ε) {x y θx θy : Space n} (hx : HasRaySlope u ε x θx)
    (hy : HasRaySlope u ε y θy) : ‖θx - θy‖ ≤ 3 / ε * ‖x - y‖ := by
  set d : ℝ := ‖x - y‖ with hd
  set δ : Space n := θx - θy with hδ
  by_cases hδ0 : δ = 0
  · rw [hδ0, norm_zero]; positivity
  have hδpos : 0 < ‖δ‖ := norm_pos_iff.mpr hδ0
  -- D z = affine difference
  set D : Space n → ℝ := fun z => (u x + ⟪θx, z - x⟫) - (u y + ⟪θy, z - y⟫) with hD
  have hDb : ∀ z, |D z| ≤ (‖z - x‖ ^ 2 + ‖z - y‖ ^ 2) / (2 * ε) := by
    intro z
    have a := abs_sub_inner_le_of_hasRaySlope hu hε hx z
    have b := abs_sub_inner_le_of_hasRaySlope hu hε hy z
    have e : D z = -(u z - u x - ⟪θx, z - x⟫) + (u z - u y - ⟪θy, z - y⟫) := by
      simp only [hD]; ring
    have := abs_add_le (-(u z - u x - ⟪θx, z - x⟫)) (u z - u y - ⟪θy, z - y⟫)
    rw [← e, abs_neg] at this
    have : (‖z - x‖ ^ 2 + ‖z - y‖ ^ 2) / (2 * ε) =
        ‖z - x‖ ^ 2 / (2 * ε) + ‖z - y‖ ^ 2 / (2 * ε) := by ring
    linarith
  have hDy := hDb y
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero] at hDy
  have hyx : ‖y - x‖ = d := by rw [hd, norm_sub_rev]
  rw [hyx] at hDy
  -- z = y + (d/‖δ‖) • δ
  set s : ℝ := d / ‖δ‖ with hs
  have hs0 : 0 ≤ s := by positivity
  have hsδ : ‖s • δ‖ = d := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, hs]; field_simp
  have hDz : D (y + s • δ) = D y + s * ‖δ‖ ^ 2 := by
    simp only [hD]
    have e1 : y + s • δ - x = (y - x) + s • δ := by abel
    have e2 : y + s • δ - y = s • δ := by abel
    rw [e1, e2, inner_add_right, inner_smul_right, inner_smul_right, show y - y = 0 by simp,
      inner_zero_right]
    have : ⟪θx, δ⟫ - ⟪θy, δ⟫ = ‖δ‖ ^ 2 := by
      rw [← inner_sub_left, ← hδ, real_inner_self_eq_norm_sq]
    nlinarith [this]
  have hDz2 := hDb (y + s • δ)
  have n1 : ‖y + s • δ - x‖ ≤ 2 * d := by
    have : y + s • δ - x = (y - x) + s • δ := by abel
    rw [this]
    calc ‖(y - x) + s • δ‖ ≤ ‖y - x‖ + ‖s • δ‖ := norm_add_le _ _
      _ = 2 * d := by rw [hyx, hsδ]; ring
  have n2 : ‖y + s • δ - y‖ = d := by simpa using hsδ
  rw [n2] at hDz2
  have n3 : ‖y + s • δ - x‖ ^ 2 ≤ (2 * d) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) n1 2
  have hz : s * ‖δ‖ ^ 2 ≤ 3 * d ^ 2 / ε := by
    have h1 : s * ‖δ‖ ^ 2 = D (y + s • δ) - D y := by rw [hDz]; ring
    have h2 : D (y + s • δ) ≤ (‖y + s • δ - x‖ ^ 2 + d ^ 2) / (2 * ε) :=
      (le_abs_self _).trans hDz2
    have h3 : -D y ≤ d ^ 2 / (2 * ε) := (neg_le_abs _).trans hDy
    have h4 : (‖y + s • δ - x‖ ^ 2 + d ^ 2) / (2 * ε) ≤ ((2 * d) ^ 2 + d ^ 2) / (2 * ε) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h5 : ((2 * d) ^ 2 + d ^ 2) / (2 * ε) + d ^ 2 / (2 * ε) = 3 * d ^ 2 / ε := by
      field_simp; ring
    linarith
  have : s * ‖δ‖ ^ 2 = d * ‖δ‖ := by rw [hs]; field_simp
  rw [this] at hz
  -- conclude: d‖δ‖ ≤ 3 d²/ε
  by_cases hd0 : d = 0
  · -- then x = y and θx = θy by uniqueness
    have hxy : x = y := by
      rw [hd] at hd0; exact sub_eq_zero.mp (norm_eq_zero.mp hd0)
    subst hxy
    exact absurd (HasRaySlope.eq hu hε hε hx hy) (fun h => hδ0 (by rw [hδ, h, sub_self]))
  · have hdpos : 0 < d := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd0)
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]
    have : d * ‖δ‖ * ε ≤ 3 * d ^ 2 := by
      have := mul_le_mul_of_nonneg_right hz hε.le
      rw [div_mul_cancel₀ _ hε.ne'] at this; exact this
    nlinarith

end CvxBody.Geometry
