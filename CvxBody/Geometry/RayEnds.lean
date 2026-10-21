module
public import CvxBody.Geometry.RayEndsEnvelope
public import CvxBody.Geometry.Rays
public import Mathlib.Analysis.Calculus.Rademacher

@[expose] public section


/-!
# L9: the set of ray endpoints is Lebesgue null

For a `1`-Lipschitz `u : Space n → ℝ` the *ends* of the slope-one segments are the endpoints of the
maximal segments `{y + (τ - u y) • strainDir u y}` through points `y` of `Strain u` which are not
themselves in `Strain u`.  This file proves `volume (RayEnds u) = 0`, following
`docs/part1/P02-NEEDLE-BLUEPRINT.md` (L9) with the corrections of `P02-NEEDLE-REVIEW-M0.md`,
Section 5.

* `RayEnds u` is the definition requested by the work package (the mass-balance file's `Ends`, which
  is `x ∉ Strain u ∧ OnSlopeOneSegment u x`, has the same description in `mem_ends_iff`; the name
  `RayEnds` avoids a clash with it); `TopEnds`, `BottomEnds` are the two halves
  (`rayEnds_eq_union`).  `mem_rayEnds_iff` and `volume_ends_eq_zero` state the result in the form of
  `mem_ends_iff`, without the redundant condition `u x = τ`.
* `extSet u a b` is the (closed) set of points with a unit vector `θ` such that `u (z + a θ) = u z + b`.
  A top end with backward extension `≥ δ` lies in `extSet u (-δ) (-δ)` and has no forward extension
  (`fwdExt u`).
* `volume_extSet_diff_fwdExt`: for `δ > 0`, `volume (extSet u (-δ) (-δ) \ fwdExt u) = 0`.  Proof: on
  the measurable set `Z` of such points where `u` is differentiable, `θ_z = gradient u z` is the backward
  direction, the upper paraboloids `endParaboloid` touch `u` from above, and the convex function
  `G = endConvex` has gradient `δ⁻¹ z - θ_z` at `z ∈ Z` (`RayEndsEnvelope.lean`).  By Alexandrov's
  theorem, `Φ_{-s} z = z - s θ_z = (1 - s/δ) z + s ∇G z` has derivative `(1 - s/δ) I + s A ≥ (1 - s/δ) I`
  within `Z`, so the area formula gives `volume (Φ_{-s} B) ≥ 2^{-n} volume B` for `s ≤ δ/2`;
  the sets `Φ_{-s} B` for different `s` are pairwise disjoint (`eq_of_sub_smul_eq`) and bounded, which
  forces `volume B = 0`.
* Bottom ends follow by applying the top-end result to `-u`.
-/

namespace CvxBody.Geometry

open OAI.LeanBlast.KLS MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace InnerProductSpace ENNReal

variable {n : ℕ}

/-! ### Extension sets -/

/-- Points `z` admitting a unit vector `θ` with `u (z + a θ) = u z + b`. -/
def extSet (u : Space n → ℝ) (a b : ℝ) : Set (Space n) :=
  {z | ∃ θ : Space n, ‖θ‖ = 1 ∧ u (z + a • θ) = u z + b}

theorem isClosed_extSet {u : Space n → ℝ} (hu : LipschitzWith 1 u) (a b : ℝ) :
    IsClosed (extSet u a b) := by
  set C : Set (Space n × Metric.sphere (0 : Space n) 1) :=
    {p | u (p.1 + a • (p.2 : Space n)) = u p.1 + b} with hC
  have hcont := hu.continuous
  have hCc : IsClosed C := by
    refine isClosed_eq ?_ ?_
    · exact hcont.comp (continuous_fst.add
        ((continuous_subtype_val.comp continuous_snd).const_smul a))
    · exact (hcont.comp continuous_fst).add continuous_const
  have himg : extSet u a b = Prod.fst '' C := by
    ext x
    constructor
    · rintro ⟨θ, hθ, h⟩
      exact ⟨(x, ⟨θ, by simpa using hθ⟩), h, rfl⟩
    · rintro ⟨⟨y, θ⟩, hp, rfl⟩
      exact ⟨θ, by simp, hp⟩
  rw [himg]
  exact isClosedMap_fst_of_compactSpace _ hCc

/-- Reversing the direction. -/
theorem extSet_neg_left (u : Space n → ℝ) (a b : ℝ) : extSet u (-a) b = extSet u a b := by
  ext z
  constructor
  · rintro ⟨θ, hθ, h⟩
    exact ⟨-θ, by simpa using hθ, by simpa using h⟩
  · rintro ⟨θ, hθ, h⟩
    exact ⟨-θ, by simpa using hθ, by simpa using h⟩

/-- Replacing `u` by `-u`. -/
theorem extSet_neg_fun (u : Space n → ℝ) (a b : ℝ) :
    extSet (fun x => -u x) a b = extSet u a (-b) := by
  ext z
  constructor
  · rintro ⟨θ, hθ, h⟩
    exact ⟨θ, hθ, by simp only at h; linarith⟩
  · rintro ⟨θ, hθ, h⟩
    exact ⟨θ, hθ, by simp only; linarith⟩

/-- Points with a forward slope-one extension of some positive length `1/(m+1)`. -/
def fwdExt (u : Space n → ℝ) : Set (Space n) :=
  ⋃ m : ℕ, extSet u (1 / ((m : ℝ) + 1)) (1 / ((m : ℝ) + 1))

/-- Points with a backward slope-one extension of some positive length `1/(m+1)`. -/
def bwdExt (u : Space n → ℝ) : Set (Space n) :=
  ⋃ m : ℕ, extSet u (-(1 / ((m : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))

theorem measurableSet_fwdExt {u : Space n → ℝ} (hu : LipschitzWith 1 u) :
    MeasurableSet (fwdExt u) :=
  MeasurableSet.iUnion fun _ => (isClosed_extSet hu _ _).measurableSet

theorem fwdExt_neg_fun (u : Space n → ℝ) : fwdExt (fun x => -u x) = bwdExt u := by
  unfold fwdExt bwdExt
  refine iUnion_congr fun m => ?_
  rw [extSet_neg_fun, ← extSet_neg_left]

/-! ### Slope-one segments of a Lipschitz function -/

/-- If `u (x + a θ) = u x + a` then `u` has slope one along the whole segment `[x, x + a θ]`. -/
theorem seg_of_ext {u : Space n → ℝ} (hu : LipschitzWith 1 u) {x θ : Space n} (hθ : ‖θ‖ = 1)
    {a : ℝ} (h : u (x + a • θ) = u x + a) {t : ℝ} (ht0 : 0 ≤ t) (hta : t ≤ a) :
    u (x + t • θ) = u x + t := by
  have d1 : dist (x + t • θ) x = t := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hθ, Real.norm_eq_abs, abs_of_nonneg ht0,
      mul_one]
  have d2 : dist (x + t • θ) (x + a • θ) = a - t := by
    rw [dist_eq_norm, show x + t • θ - (x + a • θ) = (t - a) • θ by rw [sub_smul]; abel,
      norm_smul, hθ, Real.norm_eq_abs, abs_of_nonpos (by linarith), mul_one]
    ring
  have a1 := hu.dist_le_mul (x + t • θ) x
  have a2 := hu.dist_le_mul (x + t • θ) (x + a • θ)
  rw [Real.dist_eq, NNReal.coe_one, one_mul, d1] at a1
  rw [Real.dist_eq, NNReal.coe_one, one_mul, d2] at a2
  have := (abs_le.mp a1).2
  have := (abs_le.mp a2).1
  linarith

/-- A forward extension of length `ε` yields one of any shorter length. -/
theorem mem_fwdExt_of_extSet {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε : ℝ} (hε : 0 < ε)
    {z : Space n} (hz : z ∈ extSet u ε ε) : z ∈ fwdExt u := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨θ, hθ, h⟩ := hz
  exact mem_iUnion.mpr ⟨m, θ, hθ, seg_of_ext hu hθ h (by positivity) hm.le⟩

/-- The top-end situation: a forward extension of length `a` in direction `θ` and a backward
extension of length `b` in direction `θ'` force `x` to be a strain point. -/
theorem mem_strain_of_ext {u : Space n → ℝ} (hu : LipschitzWith 1 u) {x θ θ' : Space n}
    (hθ : ‖θ‖ = 1) (hθ' : ‖θ'‖ = 1) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hf : u (x + a • θ) = u x + a) (hbk : u (x - b • θ') = u x - b) : x ∈ Strain u := by
  -- the two directions agree
  have hdist := hu.dist_le_mul (x + a • θ) (x - b • θ')
  rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm, hf, hbk] at hdist
  have e : x + a • θ - (x - b • θ') = a • θ + b • θ' := by abel
  rw [e] at hdist
  have h1 : a + b ≤ ‖a • θ + b • θ'‖ := by
    have := (abs_le.mp hdist).2
    linarith [abs_le.mp hdist |>.1]
  have h2 : ‖a • θ + b • θ'‖ ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b * ⟪θ, θ'⟫ := by
    rw [norm_add_sq_real, inner_smul_left, inner_smul_right, norm_smul, norm_smul, hθ, hθ']
    simp only [Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb, RCLike.conj_to_real]
    ring
  have h3 : (a + b) ^ 2 ≤ ‖a • θ + b • θ'‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have hin1 : 1 ≤ ⟪θ, θ'⟫ := by
    have : 2 * a * b * 1 ≤ 2 * a * b * ⟪θ, θ'⟫ := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hin2 : ⟪θ, θ'⟫ ≤ 1 := by
    have := real_inner_le_norm θ θ'
    rwa [hθ, hθ', mul_one] at this
  have hθθ : θ = θ' := eq_of_inner_eq_one hθ hθ' (le_antisymm hin2 hin1)
  subst hθθ
  -- slope one on both sides
  refine raySet_subset_strain (ε := min a b) (lt_min ha hb) ⟨θ, hθ, fun t ht => ?_⟩
  have hta : |t| ≤ a := ht.trans (min_le_left _ _)
  have htb : |t| ≤ b := ht.trans (min_le_right _ _)
  rcases le_total 0 t with h0 | h0
  · exact seg_of_ext hu hθ hf h0 ((le_abs_self t).trans hta)
  · have hbk' : u ((x - b • θ) + b • θ) = u (x - b • θ) + b := by
      rw [sub_add_cancel, hbk]; ring
    have := seg_of_ext hu hθ hbk' (t := b + t) (by linarith [neg_abs_le t]) (by linarith [le_abs_self t])
    have e2 : x - b • θ + (b + t) • θ = x + t • θ := by
      rw [add_smul]; abel
    rw [e2, hbk] at this
    linarith

/-! ### Upper touching and the gradient at a point with a backward extension -/

/-- Upper half of the touching bound L6: only the backward half-segment is needed. -/
theorem le_endParaboloid_of_back {u : Space n → ℝ} (hu : LipschitzWith 1 u) {δ : ℝ} (hδ : 0 < δ)
    {z θ : Space n} (hθ : ‖θ‖ = 1) (h : u (z - δ • θ) = u z - δ) (w : Space n) :
    u w ≤ u z + ⟪θ, w - z⟫ + ‖w - z‖ ^ 2 / (2 * δ) := by
  have h2 := hu.dist_le_mul w (z - δ • θ)
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul] at h2
  have h3 : w - (z - δ • θ) = (w - z) + δ • θ := by abel
  rw [h3] at h2
  have h4 := norm_add_smul_le (v := w - z) hθ hδ
  have := (abs_le.mp h2).2
  linarith

/-- At a point where `u` is differentiable and which has a backward extension in direction `θ`,
`gradient u z = θ`. -/
theorem gradient_eq_of_back {u : Space n → ℝ} (hu : LipschitzWith 1 u) {δ : ℝ} (hδ : 0 < δ)
    {z θ : Space n} (hθ : ‖θ‖ = 1) (h : u (z - δ • θ) = u z - δ)
    (hd : DifferentiableAt ℝ u z) : gradient u z = θ := by
  set g : Space n := gradient u z with hg
  have hgrad : HasGradientAt u g z := hd.hasGradientAt
  have hF : HasFDerivAt u (innerSL ℝ g) z := hgrad
  -- the directional derivative along `-θ` is `-1`
  have hγ : HasDerivAt (fun t : ℝ => z + t • (-θ)) (-θ) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (-θ)).const_add z
    simpa using this
  have hcomp : HasDerivAt (u ∘ fun t : ℝ => z + t • (-θ)) (innerSL ℝ g (-θ)) 0 :=
    hF.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  have h1 := hcomp.hasDerivWithinAt (s := Set.Ici 0)
  have h2 : HasDerivWithinAt (fun t : ℝ => u z - t) (-1) (Set.Ici 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_sub (u z)).hasDerivWithinAt (s := Set.Ici 0)
  have h3 : HasDerivWithinAt (u ∘ fun t : ℝ => z + t • (-θ)) (-1) (Set.Ici 0) 0 := by
    refine h2.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [Icc_mem_nhdsGE hδ] with t ht
      have hh : u (z - δ • θ + δ • θ) = u (z - δ • θ) + δ := by
        rw [sub_add_cancel, h]; ring
      have hseg := seg_of_ext hu hθ hh (t := δ - t) (by linarith [ht.2]) (by linarith [ht.1])
      have e : z - δ • θ + (δ - t) • θ = z + t • (-θ) := by
        rw [sub_smul, smul_neg]; abel
      rw [e, h] at hseg
      simp only [Function.comp_apply]
      linarith
    · simp
  have h4 := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ h1 h3
  have h5 : ⟪g, θ⟫ = 1 := by
    simp only [innerSL_apply_apply, inner_neg_right] at h4
    linarith
  have hgn : ‖g‖ ≤ 1 := by
    have := norm_fderiv_le_of_lipschitz ℝ hu (x₀ := z)
    rw [hF.fderiv, innerSL_apply_norm] at this
    simpa using this
  have : ‖g - θ‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real, h5, hθ]
    nlinarith [norm_nonneg g]
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [sq_nonneg ‖g - θ‖, norm_nonneg (g - θ)]))

/-! ### The points `z - s θ_z` -/

/-- Along a backward extension of length `δ`, `u` has slope one: the value at `z - δθ + rθ`. -/
theorem seg_back {u : Space n → ℝ} (hu : LipschitzWith 1 u) {δ : ℝ} {z θ : Space n}
    (hθ : ‖θ‖ = 1) (h : u (z - δ • θ) = u z - δ) {r : ℝ} (hr0 : 0 ≤ r) (hrδ : r ≤ δ) :
    u (z - δ • θ + r • θ) = u z - δ + r := by
  have hh : u (z - δ • θ + δ • θ) = u (z - δ • θ) + δ := by
    rw [sub_add_cancel, h]; ring
  rw [seg_of_ext hu hθ hh hr0 hrδ, h]

theorem u_sub_smul_of_back {u : Space n → ℝ} (hu : LipschitzWith 1 u) {δ : ℝ} {z θ : Space n}
    (hθ : ‖θ‖ = 1) (h : u (z - δ • θ) = u z - δ) {s : ℝ} (hs0 : 0 ≤ s) (hsδ : s ≤ δ) :
    u (z - s • θ) = u z - s := by
  have := seg_back hu hθ h (r := δ - s) (by linarith) (by linarith)
  have e : z - δ • θ + (δ - s) • θ = z - s • θ := by rw [sub_smul]; abel
  rw [e] at this
  linarith

/-- The interior point `z - s θ` of a backward segment has a slope-one segment on both sides. -/
theorem hasRaySlope_sub_smul {u : Space n → ℝ} (hu : LipschitzWith 1 u) {δ : ℝ} {z θ : Space n}
    (hθ : ‖θ‖ = 1) (h : u (z - δ • θ) = u z - δ) {s : ℝ} (hs0 : 0 < s) (hsδ : s < δ) :
    HasRaySlope u (min s (δ - s)) (z - s • θ) θ := by
  refine ⟨hθ, fun t ht => ?_⟩
  have h1 : t ≤ s := (le_abs_self t).trans (ht.trans (min_le_left _ _))
  have h2 : -(δ - s) ≤ t := by
    have := (neg_abs_le t)
    have := ht.trans (min_le_right s (δ - s))
    linarith
  have a := seg_back hu hθ h (r := δ - s + t) (by linarith) (by linarith)
  have b := seg_back hu hθ h (r := δ - s) (by linarith) (by linarith)
  have e1 : z - δ • θ + (δ - s + t) • θ = z - s • θ + t • θ := by
    rw [add_smul, sub_smul]; abel
  have e2 : z - δ • θ + (δ - s) • θ = z - s • θ := by rw [sub_smul]; abel
  rw [e1] at a
  rw [e2] at b
  linarith

section Core

variable {u : Space n → ℝ} {δ : ℝ} {Z : Set (Space n)}

/-- The hypotheses on the set `Z` of the core argument. -/
def IsEndCandidates (u : Space n → ℝ) (δ : ℝ) (Z : Set (Space n)) : Prop :=
  ∀ z ∈ Z, z ∈ extSet u (-δ) (-δ) ∧ z ∉ fwdExt u ∧ DifferentiableAt ℝ u z

theorem IsEndCandidates.back (hu : LipschitzWith 1 u) (hδ : 0 < δ) (hZ : IsEndCandidates u δ Z)
    {z : Space n} (hz : z ∈ Z) :
    ‖gradient u z‖ = 1 ∧ u (z - δ • gradient u z) = u z - δ := by
  obtain ⟨⟨θ, hθ, h⟩, -, hd⟩ := hZ z hz
  have h' : u (z - δ • θ) = u z - δ := by
    have e : z - δ • θ = z + (-δ) • θ := by rw [neg_smul, sub_eq_add_neg]
    rw [e, h]; ring
  have := gradient_eq_of_back hu hδ hθ h' hd
  rw [this]
  exact ⟨hθ, h'⟩

/-- Two points `z - s θ_z = z' - s' θ_{z'}` of the shifted sets coincide with `s = s'` and `z = z'`. -/
theorem eq_of_sub_smul_eq (hu : LipschitzWith 1 u) (hδ : 0 < δ) (hZ : IsEndCandidates u δ Z)
    {z z' : Space n} (hz : z ∈ Z) (hz' : z' ∈ Z) {s s' : ℝ} (hs : 0 < s) (hsδ : s < δ)
    (hs' : 0 < s') (hs'δ : s' < δ)
    (h : z - s • gradient u z = z' - s' • gradient u z') : s = s' ∧ z = z' := by
  obtain ⟨hθ, hb⟩ := hZ.back hu hδ hz
  obtain ⟨hθ', hb'⟩ := hZ.back hu hδ hz'
  have hy := (hasRaySlope_sub_smul hu hθ hb hs hsδ).gradient_eq hu
    (lt_min hs (by linarith))
  have hy' := (hasRaySlope_sub_smul hu hθ' hb' hs' hs'δ).gradient_eq hu
    (lt_min hs' (by linarith))
  rw [← h] at hy'
  have hθeq : gradient u z = gradient u z' := hy.symm.trans hy'
  have hu1 := u_sub_smul_of_back hu hθ hb hs.le hsδ.le
  have hu2 := u_sub_smul_of_back hu hθ' hb' hs'.le hs'δ.le
  rw [← h] at hu2
  -- the key one-sided claim
  have key : ∀ {w w' : Space n} {t t' : ℝ}, w ∈ Z → 0 < t → t < t' →
      u w' = u w + (t' - t) → w' = w + (t' - t) • gradient u w → False := by
    intro w w' t t' hw ht htt' hu' hw'
    obtain ⟨hθw, -⟩ := hZ.back hu hδ hw
    have hfw : w ∈ extSet u (t' - t) (t' - t) :=
      ⟨gradient u w, hθw, by rw [← hw', hu']⟩
    exact (hZ w hw).2.1 (mem_fwdExt_of_extSet hu (by linarith) hfw)
  have hz'eq : z' = z + (s' - s) • gradient u z := by
    have : z' = z - s • gradient u z + s' • gradient u z' := by
      rw [h]; abel
    rw [this, ← hθeq, sub_smul]; abel
  have hzeq : z = z' + (s - s') • gradient u z' := by
    have : z = z' - s' • gradient u z' + s • gradient u z := by
      rw [← h]; abel
    rw [this, hθeq, sub_smul]; abel
  rcases lt_trichotomy s s' with hlt | heq | hgt
  · exact (key hz hs hlt (by linarith) hz'eq).elim
  · subst heq
    refine ⟨rfl, ?_⟩
    rw [hθeq] at h
    exact sub_left_injective h
  · exact (key hz' hs' hgt (by linarith) hzeq).elim

/-- **Core of L9.** A measurable set `Z` of points with a backward extension of length `δ`, no forward
extension, and at which `u` is differentiable, is Lebesgue null. -/
theorem volume_eq_zero_of_isEndCandidates (hu : LipschitzWith 1 u) (hδ : 0 < δ)
    (hZm : MeasurableSet Z) (hZ : IsEndCandidates u δ Z) : volume Z = 0 := by
  set θ : Space n → Space n := gradient u with hθdef
  have hT : UpperTouching u δ Z θ := fun z hz w => by
    obtain ⟨hθ, hb⟩ := hZ.back hu hδ hz
    exact le_endParaboloid_of_back hu hδ hθ hb w
  have hconv := convexOn_endConvex hδ hT
  set G := endConvex u δ Z θ with hG
  have hGgrad : ∀ z ∈ Z, HasGradientAt G (endSlope δ θ z) z := fun z hz =>
    hasGradientAt_endConvex hδ hT hz (hZ z hz).2.2.hasGradientAt
  obtain ⟨Hs, -, hae⟩ := hconv.exists_measurable_hessian (μ := (volume : Measure (Space n)))
  set Q : Space n → Prop := fun x => (Hs x).IsPositive ∧
      HasFDerivWithinAt (gradient G) (Hs x) Z x with hQ
  have hae' : ∀ᵐ x ∂(volume : Measure (Space n)), Q x := by
    filter_upwards [hae] with x hx
    obtain ⟨hpos, -, hder⟩ := hx
    exact ⟨hpos, hder _ fun x' hx' => (hGgrad x' hx').differentiableAt⟩
  have hnull : volume {x | ¬ Q x} = 0 := ae_iff.mp hae'
  set N : Set (Space n) := toMeasurable volume {x | ¬ Q x} with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by rw [hN, measure_toMeasurable]; exact hnull
  have hQN : ∀ x, x ∉ N → Q x := fun x hx => by
    by_contra h
    exact hx (subset_toMeasurable _ _ h)
  -- it suffices to show that `Z \ N` is null
  have hZN : volume (Z \ N) = 0 := by
    have hcover : Z \ N = ⋃ R : ℕ, (Z \ N) ∩ Metric.ball (0 : Space n) R := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, Metric.mem_ball, dist_zero_right]
      constructor
      · intro hx
        obtain ⟨R, hR⟩ := exists_nat_gt ‖x‖
        exact ⟨R, hx, hR⟩
      · rintro ⟨R, hx, -⟩
        exact hx
    rw [hcover]
    refine measure_iUnion_null fun R => ?_
    set B : Set (Space n) := (Z \ N) ∩ Metric.ball (0 : Space n) R with hB
    have hBm : MeasurableSet B := (hZm.diff hNm).inter Metric.isOpen_ball.measurableSet
    have hBZ : B ⊆ Z := fun x hx => hx.1.1
    have hBQ : ∀ x ∈ B, Q x := fun x hx => hQN x hx.1.2
    by_contra hne
    -- the shifted maps
    set Ψ : ℝ → Space n → Space n := fun s z => (1 - s / δ) • z + s • gradient G z with hΨ
    have hΨeq : ∀ s, ∀ z ∈ Z, Ψ s z = z - s • gradient u z := by
      intro s z hz
      have hg : gradient G z = δ⁻¹ • z - gradient u z := (hGgrad z hz).gradient
      simp only [hΨ, hg]
      rw [smul_sub, smul_smul, sub_smul, one_smul, div_eq_mul_inv, mul_comm s δ⁻¹]
      abel
    have hderiv : ∀ s, ∀ x ∈ B, HasFDerivWithinAt (Ψ s)
        ((1 - s / δ) • ContinuousLinearMap.id ℝ (Space n) + s • Hs x) B x := by
      intro s x hx
      have h1 := hBQ x hx
      have h2 : HasFDerivWithinAt (gradient G) (Hs x) B x := h1.2.mono hBZ
      exact ((hasFDerivWithinAt_id x B).const_smul (1 - s / δ)).add (h2.const_smul s)
    have hinj : ∀ s ∈ Ioo 0 δ, InjOn (Ψ s) B := by
      intro s hs z hz z' hz' hzz
      rw [hΨeq s z (hBZ hz), hΨeq s z' (hBZ hz')] at hzz
      exact (eq_of_sub_smul_eq hu hδ hZ (hBZ hz) (hBZ hz') hs.1 hs.2 hs.1 hs.2 hzz).2
    have hmeas : ∀ s ∈ Ioo 0 δ, MeasurableSet (Ψ s '' B) := fun s hs =>
      measurable_image_of_fderivWithin hBm (hderiv s) (hinj s hs)
    have hdisj : ∀ s ∈ Ioo 0 δ, ∀ s' ∈ Ioo 0 δ, s ≠ s' → Disjoint (Ψ s '' B) (Ψ s' '' B) := by
      intro s hs s' hs' hss'
      rw [Set.disjoint_left]
      rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', hzz⟩
      rw [hΨeq s z (hBZ hz), hΨeq s' z' (hBZ hz')] at hzz
      exact hss' (eq_of_sub_smul_eq hu hδ hZ (hBZ hz') (hBZ hz) hs'.1 hs'.2 hs.1 hs.2 hzz).1.symm
    have hsub : ∀ s ∈ Ioo 0 δ, Ψ s '' B ⊆ Metric.ball (0 : Space n) (R + δ) := by
      rintro s hs _ ⟨z, hz, rfl⟩
      rw [hΨeq s z (hBZ hz), mem_ball_zero_iff]
      have h1 : ‖z‖ < R := by simpa using hz.2
      have h2 := (hZ.back hu hδ (hBZ hz)).1
      calc ‖z - s • gradient u z‖ ≤ ‖z‖ + ‖s • gradient u z‖ := norm_sub_le _ _
        _ = ‖z‖ + s := by rw [norm_smul, h2, Real.norm_eq_abs, abs_of_pos hs.1, mul_one]
        _ < R + δ := by linarith [hs.2]
    have hlow : ∀ s ∈ Ioc 0 (δ / 2), ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * volume B ≤
        volume (Ψ s '' B) := by
      intro s hs
      have hsδ : s ∈ Ioo 0 δ := ⟨hs.1, by linarith [hs.2]⟩
      rw [← lintegral_abs_det_fderiv_eq_addHaar_image (μ := volume) hBm (hderiv s) (hinj s hsδ),
        ← setLIntegral_const]
      refine setLIntegral_mono' hBm fun x hx => ENNReal.ofReal_le_ofReal ?_
      have hhalf : (1 / 2 : ℝ) ≤ 1 - s / δ := by
        have : s / δ ≤ 1 / 2 := by
          rw [div_le_iff₀ hδ]; linarith [hs.2]
        linarith
      have hdet := le_det_smul_id_add_smul (n := n) (c := 1 - s / δ) (s := s)
        (by linarith) hs.1.le (hBQ x hx).1
      calc (1 / 2 : ℝ) ^ n ≤ (1 - s / δ) ^ n := pow_le_pow_left₀ (by norm_num) hhalf n
        _ ≤ _ := hdet
        _ ≤ _ := le_abs_self _
    -- infinitely many disjoint images of definite measure in a ball
    set sq : ℕ → ℝ := fun k => δ / ((k : ℝ) + 3) with hsq
    have hsq_pos : ∀ k, 0 < sq k := fun k => by positivity
    have hsq_le : ∀ k, sq k ≤ δ / 2 := fun k => by
      rw [hsq]
      refine div_le_div_of_nonneg_left hδ.le (by norm_num) (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
    have hsq_mem : ∀ k, sq k ∈ Ioo 0 δ := fun k => ⟨hsq_pos k, by linarith [hsq_le k]⟩
    have hsq_inj : Function.Injective sq := by
      intro k l hkl
      simp only [hsq] at hkl
      have h1 := div_eq_div_iff (by positivity) (by positivity) |>.mp hkl
      have h2 : ((k : ℝ) + 3) = (l : ℝ) + 3 := by
        have := mul_left_cancel₀ hδ.ne' (by linarith : δ * ((l : ℝ) + 3) = δ * ((k : ℝ) + 3))
        linarith
      exact_mod_cast (by linarith : (k : ℝ) = l)
    have hdisj' : Pairwise (Function.onFun Disjoint fun k => Ψ (sq k) '' B) := by
      intro k l hkl
      exact hdisj _ (hsq_mem k) _ (hsq_mem l) (fun h => hkl (hsq_inj h))
    have htot : volume (⋃ k, Ψ (sq k) '' B) = ∑' k, volume (Ψ (sq k) '' B) :=
      measure_iUnion hdisj' fun k => hmeas _ (hsq_mem k)
    have hfin : volume (⋃ k, Ψ (sq k) '' B) < ∞ :=
      (measure_mono (iUnion_subset fun k => hsub _ (hsq_mem k))).trans_lt measure_ball_lt_top
    have hc : ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * volume B ≠ 0 :=
      mul_ne_zero (by simp) hne
    have hge : ∑' _k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * volume B ≤
        ∑' k, volume (Ψ (sq k) '' B) :=
      ENNReal.tsum_le_tsum fun k => hlow _ ⟨hsq_pos k, hsq_le k⟩
    rw [ENNReal.tsum_const_eq_top_of_ne_zero hc, ← htot] at hge
    exact (not_le.mpr hfin) hge
  exact measure_mono_null (by
    intro x hx
    by_cases hxN : x ∈ N
    · exact Or.inr hxN
    · exact Or.inl ⟨hx, hxN⟩) (measure_union_null hZN hN0)

end Core

/-! ### Null sets of points with a backward (forward) extension and no forward (backward) one -/

/-- For `δ > 0`, the points with a backward extension of length `δ` and no forward extension form
a Lebesgue null set. -/
theorem volume_extSet_diff_fwdExt {u : Space n → ℝ} (hu : LipschitzWith 1 u) {δ : ℝ} (hδ : 0 < δ) :
    volume (extSet u (-δ) (-δ) \ fwdExt u) = 0 := by
  set D : Set (Space n) := {x | ¬ DifferentiableAt ℝ u x} with hD
  have hD0 : volume D = 0 := ae_iff.mp (hu.ae_differentiableAt (μ := volume))
  set N0 : Set (Space n) := toMeasurable volume D with hN0
  have hN0m : MeasurableSet N0 := measurableSet_toMeasurable _ _
  have hN00 : volume N0 = 0 := by rw [hN0, measure_toMeasurable]; exact hD0
  set Z : Set (Space n) := (extSet u (-δ) (-δ) \ fwdExt u) \ N0 with hZdef
  have hZm : MeasurableSet Z :=
    ((isClosed_extSet hu _ _).measurableSet.diff (measurableSet_fwdExt hu)).diff hN0m
  have hZ : IsEndCandidates u δ Z := fun z hz =>
    ⟨hz.1.1, hz.1.2, by
      by_contra h
      exact hz.2 (subset_toMeasurable _ _ h)⟩
  have h1 := volume_eq_zero_of_isEndCandidates hu hδ hZm hZ
  refine measure_mono_null (fun x hx => ?_) (measure_union_null h1 hN00)
  by_cases hxN : x ∈ N0
  · exact Or.inr hxN
  · exact Or.inl ⟨hx, hxN⟩

/-- For `δ > 0`, the points with a forward extension of length `δ` and no backward extension form
a Lebesgue null set (apply the top-end result to `-u`). -/
theorem volume_extSet_diff_bwdExt {u : Space n → ℝ} (hu : LipschitzWith 1 u) {δ : ℝ} (hδ : 0 < δ) :
    volume (extSet u δ δ \ bwdExt u) = 0 := by
  have h := volume_extSet_diff_fwdExt (u := fun x => -u x) hu.neg hδ
  rwa [extSet_neg_fun, neg_neg, extSet_neg_left, fwdExt_neg_fun] at h

/-! ### The end set -/

/-- The set `Ends u` of endpoints of the maximal slope-one segments through strain points, which
are not themselves strain points: `x` is the point of the line through `y ∈ Strain u` with
`u`-coordinate `τ`, where `τ` is the lower or upper endpoint `rayLo u y`, `rayHi u y` of the
maximal slope-one segment (the endpoints are `EReal`-valued, so `τ : ℝ` is required to equal one of
them, i.e. to be finite), and `u x = τ`. -/
def RayEnds (u : Space n → ℝ) : Set (Space n) :=
  {x | x ∉ Strain u ∧ ∃ y ∈ Strain u, ∃ τ : ℝ, ((τ : EReal) = rayLo u y ∨ (τ : EReal) = rayHi u y) ∧
    x = y + (τ - u y) • strainDir u y ∧ u x = τ}

/-- The top ends: endpoints at the upper endpoint `rayHi`. -/
def TopEnds (u : Space n → ℝ) : Set (Space n) :=
  {x | x ∉ Strain u ∧ ∃ y ∈ Strain u, ∃ τ : ℝ, (τ : EReal) = rayHi u y ∧
    x = y + (τ - u y) • strainDir u y ∧ u x = τ}

/-- The bottom ends: endpoints at the lower endpoint `rayLo`. -/
def BottomEnds (u : Space n → ℝ) : Set (Space n) :=
  {x | x ∉ Strain u ∧ ∃ y ∈ Strain u, ∃ τ : ℝ, (τ : EReal) = rayLo u y ∧
    x = y + (τ - u y) • strainDir u y ∧ u x = τ}

theorem rayEnds_eq_union (u : Space n → ℝ) : RayEnds u = TopEnds u ∪ BottomEnds u := by
  ext x
  simp only [RayEnds, TopEnds, BottomEnds, mem_ofPred_eq, mem_union]
  constructor
  · rintro ⟨hx, y, hy, τ, h | h, hxy, hux⟩
    · exact Or.inr ⟨hx, y, hy, τ, h, hxy, hux⟩
    · exact Or.inl ⟨hx, y, hy, τ, h, hxy, hux⟩
  · rintro (⟨hx, y, hy, τ, h, hxy, hux⟩ | ⟨hx, y, hy, τ, h, hxy, hux⟩)
    · exact ⟨hx, y, hy, τ, Or.inr h, hxy, hux⟩
    · exact ⟨hx, y, hy, τ, Or.inl h, hxy, hux⟩

/-- A top end lies in `extSet u (-δ) (-δ) \ fwdExt u` for some `δ = 1/(m+1)`. -/
theorem TopEnds_subset {u : Space n → ℝ} (hu : LipschitzWith 1 u) :
    TopEnds u ⊆ ⋃ m : ℕ, (extSet u (-(1 / ((m : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))) \ fwdExt u) := by
  rintro x ⟨hx, y, hy, τ, hτ, hxy, hux⟩
  set θ := strainDir u y with hθdef
  have hθ : ‖θ‖ = 1 := norm_strainDir hy
  have hlt := lt_rayHi hu hy
  rw [← hτ] at hlt
  have hd : 0 < τ - u y := by have := EReal.coe_lt_coe_iff.mp hlt; linarith
  set d := τ - u y with hddef
  have hxd : x - d • θ = y := by rw [hxy]; abel
  have hext : u (y + d • θ) = u y + d := by
    have : y + d • θ = x := hxy.symm
    rw [this, hux]; ring
  have hback : u (x - d • θ) = u x - d := by
    rw [hxd, hux]; ring
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hd
  refine mem_iUnion.mpr ⟨m, ⟨θ, hθ, ?_⟩, fun hf => ?_⟩
  · have h1 := seg_of_ext hu hθ hext (t := d - 1 / ((m : ℝ) + 1)) (by linarith) (by
      have : 0 < 1 / ((m : ℝ) + 1) := by positivity
      linarith)
    have e : y + (d - 1 / ((m : ℝ) + 1)) • θ = x + (-(1 / ((m : ℝ) + 1))) • θ := by
      rw [hxy, sub_smul, neg_smul]; abel
    rw [e] at h1
    linarith
  · obtain ⟨m', θ', hθ', h'⟩ := mem_iUnion.mp hf
    exact hx (mem_strain_of_ext hu hθ' hθ (by positivity) hd h' hback)

/-- A bottom end lies in `extSet u δ δ \ bwdExt u` for some `δ = 1/(m+1)`. -/
theorem BottomEnds_subset {u : Space n → ℝ} (hu : LipschitzWith 1 u) :
    BottomEnds u ⊆ ⋃ m : ℕ, (extSet u (1 / ((m : ℝ) + 1)) (1 / ((m : ℝ) + 1)) \ bwdExt u) := by
  rintro x ⟨hx, y, hy, τ, hτ, hxy, hux⟩
  set θ := strainDir u y with hθdef
  have hθ : ‖θ‖ = 1 := norm_strainDir hy
  have hlt := rayLo_lt hu hy
  rw [← hτ] at hlt
  have hd : 0 < u y - τ := by have := EReal.coe_lt_coe_iff.mp hlt; linarith
  set d := u y - τ with hddef
  have hfwd : u (x + d • θ) = u x + d := by
    have : x + d • θ = y := by
      rw [hxy, add_assoc, ← add_smul]
      have : τ - u y + d = 0 := by rw [hddef]; ring
      rw [this, zero_smul, add_zero]
    rw [this, hux]; ring
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hd
  refine mem_iUnion.mpr ⟨m, ⟨θ, hθ, ?_⟩, fun hf => ?_⟩
  · exact seg_of_ext hu hθ hfwd (by positivity) hm.le
  · obtain ⟨m', θ', hθ', h'⟩ := mem_iUnion.mp hf
    have h'' : u (x - (1 / ((m' : ℝ) + 1)) • θ') = u x - 1 / ((m' : ℝ) + 1) := by
      have e : x - (1 / ((m' : ℝ) + 1)) • θ' = x + (-(1 / ((m' : ℝ) + 1))) • θ' := by
        rw [neg_smul, sub_eq_add_neg]
      rw [e]
      linarith
    exact hx (mem_strain_of_ext hu hθ hθ' hd (by positivity) hfwd h'')

theorem volume_topEnds_eq_zero {u : Space n → ℝ} (hu : LipschitzWith 1 u) :
    volume (TopEnds u) = 0 :=
  measure_mono_null (TopEnds_subset hu) (measure_iUnion_null fun m =>
    volume_extSet_diff_fwdExt hu (by positivity))

theorem volume_bottomEnds_eq_zero {u : Space n → ℝ} (hu : LipschitzWith 1 u) :
    volume (BottomEnds u) = 0 :=
  measure_mono_null (BottomEnds_subset hu) (measure_iUnion_null fun m =>
    volume_extSet_diff_bwdExt hu (by positivity))

/-- **L9.** For a `1`-Lipschitz function `u` on `Space n` the set of ends of its maximal slope-one
segments is Lebesgue null. -/
theorem volume_rayEnds_eq_zero {u : Space n → ℝ} (hu : LipschitzWith 1 u) :
    volume (RayEnds u) = 0 := by
  rw [rayEnds_eq_union]
  exact measure_union_null (volume_topEnds_eq_zero hu) (volume_bottomEnds_eq_zero hu)

/-! ### The endpoint value is attained; comparison with the formulation without `u x = τ` -/

theorem isClosed_raySlopeTimes {u : Space n → ℝ} (hu : LipschitzWith 1 u) (q : Space n × Space n) :
    IsClosed (raySlopeTimes u q) := by
  have hc : Continuous fun τ : ℝ => u (q.2 + τ • q.1) - τ :=
    (hu.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).sub
      continuous_id
  have : raySlopeTimes u q = (fun τ : ℝ => u (q.2 + τ • q.1) - τ) ⁻¹' {0} := by
    ext τ
    simp [raySlopeTimes, sub_eq_zero]
  rw [this]
  exact isClosed_singleton.preimage hc

/-- The upper endpoint `rayHi`, when finite, is attained: `u` has slope one up to it. -/
theorem u_eq_of_rayHi_eq {u : Space n → ℝ} (hu : LipschitzWith 1 u) {y : Space n}
    (hy : y ∈ Strain u) {τ : ℝ} (hτ : (τ : EReal) = rayHi u y) :
    u (y + (τ - u y) • strainDir u y) = τ := by
  have hlt : u y < τ := by
    have := lt_rayHi hu hy
    rw [← hτ] at this
    exact EReal.coe_lt_coe_iff.mp this
  have hsub : Ioo (u y) τ ⊆ raySlopeTimes u (rayInv u y) := fun τ' h =>
    mem_raySlopeTimes_of_lt_of_lt hu hy ((rayLo_lt hu hy).trans (EReal.coe_lt_coe_iff.mpr h.1))
      (by rw [← hτ]; exact EReal.coe_lt_coe_iff.mpr h.2)
  have : τ ∈ closure (Ioo (u y) τ) := by rw [closure_Ioo hlt.ne]; exact ⟨hlt.le, le_rfl⟩
  exact mem_raySlopeTimes_rayInv.mp
    (((isClosed_raySlopeTimes hu _).closure_subset_iff.mpr hsub) this)

/-- The lower endpoint `rayLo`, when finite, is attained. -/
theorem u_eq_of_rayLo_eq {u : Space n → ℝ} (hu : LipschitzWith 1 u) {y : Space n}
    (hy : y ∈ Strain u) {τ : ℝ} (hτ : (τ : EReal) = rayLo u y) :
    u (y + (τ - u y) • strainDir u y) = τ := by
  have hlt : τ < u y := by
    have := rayLo_lt hu hy
    rw [← hτ] at this
    exact EReal.coe_lt_coe_iff.mp this
  have hsub : Ioo τ (u y) ⊆ raySlopeTimes u (rayInv u y) := fun τ' h =>
    mem_raySlopeTimes_of_lt_of_lt hu hy (by rw [← hτ]; exact EReal.coe_lt_coe_iff.mpr h.1)
      ((EReal.coe_lt_coe_iff.mpr h.2).trans (lt_rayHi hu hy))
  have : τ ∈ closure (Ioo τ (u y)) := by rw [closure_Ioo hlt.ne]; exact ⟨le_rfl, hlt.le⟩
  exact mem_raySlopeTimes_rayInv.mp
    (((isClosed_raySlopeTimes hu _).closure_subset_iff.mpr hsub) this)

/-- `RayEnds u` without the redundant condition `u x = τ` (it holds because the finite endpoints
`rayLo`, `rayHi` are attained), in the form of the mass-balance file (`mem_ends_iff`). -/
theorem mem_rayEnds_iff {u : Space n → ℝ} (hu : LipschitzWith 1 u) (x : Space n) :
    x ∈ RayEnds u ↔ x ∉ Strain u ∧ ∃ z ∈ Strain u, ∃ τ : ℝ,
      (rayLo u z = τ ∨ rayHi u z = τ) ∧ x = z + (τ - u z) • strainDir u z := by
  constructor
  · rintro ⟨hx, z, hz, τ, h, hxz, -⟩
    exact ⟨hx, z, hz, τ, h.imp Eq.symm Eq.symm, hxz⟩
  · rintro ⟨hx, z, hz, τ, h, hxz⟩
    refine ⟨hx, z, hz, τ, h.imp Eq.symm Eq.symm, hxz, ?_⟩
    rw [hxz]
    rcases h with h | h
    · exact u_eq_of_rayLo_eq hu hz h.symm
    · exact u_eq_of_rayHi_eq hu hz h.symm

/-- **L9**, in the form of the mass-balance file: the set of `x ∉ Strain u` of the form
`z + (τ - u z) • strainDir u z`, `z ∈ Strain u`, `τ ∈ {rayLo u z, rayHi u z}` is Lebesgue null. -/
theorem volume_ends_eq_zero {u : Space n → ℝ} (hu : LipschitzWith 1 u) :
    volume {x | x ∉ Strain u ∧ ∃ z ∈ Strain u, ∃ τ : ℝ, (rayLo u z = τ ∨ rayHi u z = τ) ∧
      x = z + (τ - u z) • strainDir u z} = 0 := by
  have : {x | x ∉ Strain u ∧ ∃ z ∈ Strain u, ∃ τ : ℝ, (rayLo u z = τ ∨ rayHi u z = τ) ∧
      x = z + (τ - u z) • strainDir u z} = RayEnds u := by
    ext x; exact (mem_rayEnds_iff hu x).symm
  rw [this]
  exact volume_rayEnds_eq_zero hu

end CvxBody.Geometry
