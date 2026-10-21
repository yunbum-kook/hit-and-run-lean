module
public import CvxBody.Geometry.RaysTouching
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

@[expose] public section


/-!
# Ray structure of a 1-Lipschitz function (L5 of `docs/part1/P02-NEEDLE-BLUEPRINT.md`)

For a 1-Lipschitz `u : Space n → ℝ`:

* `raySet u ε` is closed (`isClosed_raySet`); `Strain u = ⋃ m, raySet u (1/(m+1))` is `F_σ`.
* At a point of `Strain u` the ray direction `strainDir u x` is unique, `u` is differentiable and
  `gradient u x = strainDir u x`.
* The ray invariant `rayInv u x = (θ, x - u x • θ)` is constant along rays and separates them;
  `rayLo`, `rayHi` are the endpoints of the maximal slope-one segment, in the `u`-coordinate.
* `strainDir`, `rayInv`, `rayLo`, `rayHi` are Borel measurable.
-/

namespace CvxBody.Geometry

open OAI.LeanBlast.KLS MeasureTheory Set
open scoped RealInnerProductSpace

variable {n : ℕ}

/-! ### Closedness of `raySet` -/

theorem isClosed_raySet {u : Space n → ℝ} (hu : LipschitzWith 1 u) (ε : ℝ) :
    IsClosed (raySet u ε) := by
  set C : Set (Space n × Metric.sphere (0 : Space n) 1) :=
    {p | ∀ t : ℝ, |t| ≤ ε → u (p.1 + t • (p.2 : Space n)) = u p.1 + t} with hC
  have hcont := hu.continuous
  have hCc : IsClosed C := by
    have : C = ⋂ t : ℝ, ⋂ (_ : |t| ≤ ε),
        {p : Space n × Metric.sphere (0 : Space n) 1 |
          u (p.1 + t • (p.2 : Space n)) = u p.1 + t} := by
      ext p; simp [hC]
    rw [this]
    refine isClosed_iInter fun t => isClosed_iInter fun _ => isClosed_eq ?_ ?_
    · exact hcont.comp (continuous_fst.add
        ((continuous_subtype_val.comp continuous_snd).const_smul t))
    · exact (hcont.comp continuous_fst).add continuous_const
  have himg : raySet u ε = Prod.fst '' C := by
    ext x
    constructor
    · rintro ⟨θ, hθ, h⟩
      exact ⟨(x, ⟨θ, by simpa using hθ⟩), fun t ht => h t ht, rfl⟩
    · rintro ⟨⟨y, θ⟩, hp, rfl⟩
      exact ⟨θ, by simp, hp⟩
  rw [himg]
  exact isClosedMap_fst_of_compactSpace _ hCc

/-! ### `Strain`, the ray direction, differentiability -/

/-- Points with slope-one segments of some positive half-length `1/(m+1)` on both sides. -/
def Strain (u : Space n → ℝ) : Set (Space n) := ⋃ m : ℕ, raySet u (1 / ((m : ℝ) + 1))

theorem mem_strain_iff {u : Space n → ℝ} {x : Space n} :
    x ∈ Strain u ↔ ∃ ε : ℝ, 0 < ε ∧ x ∈ raySet u ε := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := mem_iUnion.mp h
    exact ⟨_, by positivity, hm⟩
  · rintro ⟨ε, hε, hx⟩
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    exact mem_iUnion.mpr ⟨m, raySet_mono hm.le hx⟩

theorem raySet_subset_strain {u : Space n → ℝ} {ε : ℝ} (hε : 0 < ε) :
    raySet u ε ⊆ Strain u := fun _ hx => mem_strain_iff.mpr ⟨ε, hε, hx⟩

/-- `Strain u` is `F_σ`, hence Borel. -/
theorem measurableSet_strain {u : Space n → ℝ} (hu : LipschitzWith 1 u) :
    MeasurableSet (Strain u) :=
  MeasurableSet.iUnion fun _ => (isClosed_raySet hu _).measurableSet

open Classical in
/-- The (unique, by `HasRaySlope.strainDir_eq`) ray direction at a point of `Strain u`;
`0` off `Strain u`. -/
noncomputable def strainDir (u : Space n → ℝ) (x : Space n) : Space n :=
  if h : ∃ θ : Space n, ∃ m : ℕ, HasRaySlope u (1 / ((m : ℝ) + 1)) x θ then h.choose else 0

theorem strainDir_of_not_mem {u : Space n → ℝ} {x : Space n} (hx : x ∉ Strain u) :
    strainDir u x = 0 := by
  have : ¬ ∃ θ : Space n, ∃ m : ℕ, HasRaySlope u (1 / ((m : ℝ) + 1)) x θ := by
    rintro ⟨θ, m, h⟩
    exact hx (mem_iUnion.mpr ⟨m, θ, h⟩)
  classical
  rw [strainDir]
  exact dite_eq_right_iff.mpr fun h => absurd h this

/-- Specification of `strainDir`: it is a ray direction of some half-length `1/(m+1)`. -/
theorem strainDir_spec {u : Space n → ℝ} {x : Space n} (hx : x ∈ Strain u) :
    ∃ m : ℕ, HasRaySlope u (1 / ((m : ℝ) + 1)) x (strainDir u x) := by
  obtain ⟨m, θ, h⟩ : ∃ (m : ℕ) (θ : Space n), HasRaySlope u (1 / ((m : ℝ) + 1)) x θ := by
    obtain ⟨m, θ, hθ⟩ := mem_iUnion.mp hx
    exact ⟨m, θ, hθ⟩
  have hex : ∃ θ : Space n, ∃ m : ℕ, HasRaySlope u (1 / ((m : ℝ) + 1)) x θ := ⟨θ, m, h⟩
  simp only [strainDir, hex, dite_true]
  exact hex.choose_spec

theorem norm_strainDir {u : Space n → ℝ} {x : Space n} (hx : x ∈ Strain u) :
    ‖strainDir u x‖ = 1 := by
  obtain ⟨m, h⟩ := strainDir_spec hx
  exact h.1

/-- Uniqueness of the direction: any ray direction of positive half-length is `strainDir`. -/
theorem HasRaySlope.strainDir_eq {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε : ℝ}
    (hε : 0 < ε) {x θ : Space n} (h : HasRaySlope u ε x θ) : strainDir u x = θ := by
  have hx : x ∈ Strain u := mem_strain_iff.mpr ⟨ε, hε, θ, h⟩
  obtain ⟨m, hm⟩ := strainDir_spec hx
  exact HasRaySlope.eq hu (by positivity) hε hm h

theorem hasRaySlope_strainDir {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε : ℝ}
    (hε : 0 < ε) {x : Space n} (hx : x ∈ raySet u ε) : HasRaySlope u ε x (strainDir u x) := by
  obtain ⟨θ, h⟩ := mem_raySet.mp hx
  rwa [h.strainDir_eq hu hε]

/-- **L5(a).** At a point of `Strain u`, `u` has gradient `strainDir u x`. -/
theorem hasGradientAt_strainDir {u : Space n → ℝ} (hu : LipschitzWith 1 u) {x : Space n}
    (hx : x ∈ Strain u) : HasGradientAt u (strainDir u x) x := by
  obtain ⟨ε, hε, hxε⟩ := mem_strain_iff.mp hx
  exact (hasRaySlope_strainDir hu hε hxε).hasGradientAt hu hε

theorem hasFDerivAt_strainDir {u : Space n → ℝ} (hu : LipschitzWith 1 u) {x : Space n}
    (hx : x ∈ Strain u) : HasFDerivAt u (innerSL ℝ (strainDir u x)) x :=
  hasGradientAt_strainDir hu hx

theorem differentiableAt_of_mem_strain {u : Space n → ℝ} (hu : LipschitzWith 1 u) {x : Space n}
    (hx : x ∈ Strain u) : DifferentiableAt ℝ u x :=
  (hasFDerivAt_strainDir hu hx).differentiableAt

theorem fderiv_eq_of_mem_strain {u : Space n → ℝ} (hu : LipschitzWith 1 u) {x : Space n}
    (hx : x ∈ Strain u) : fderiv ℝ u x = innerSL ℝ (strainDir u x) :=
  (hasFDerivAt_strainDir hu hx).fderiv

theorem gradient_eq_strainDir {u : Space n → ℝ} (hu : LipschitzWith 1 u) {x : Space n}
    (hx : x ∈ Strain u) : gradient u x = strainDir u x :=
  (hasGradientAt_strainDir hu hx).gradient

/-- **L6** for `strainDir`: two-sided quadratic touching on `raySet u ε`. -/
theorem abs_sub_inner_strainDir_le {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε : ℝ}
    (hε : 0 < ε) {x : Space n} (hx : x ∈ raySet u ε) (w : Space n) :
    |u w - u x - ⟪strainDir u x, w - x⟫| ≤ ‖w - x‖ ^ 2 / (2 * ε) :=
  abs_sub_inner_le_of_hasRaySlope hu hε (hasRaySlope_strainDir hu hε hx) w

/-- **L6 (consequence).** `strainDir u` is `(3/ε)`-Lipschitz on `raySet u ε`. -/
theorem lipschitzOnWith_strainDir {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε : ℝ}
    (hε : 0 < ε) : LipschitzOnWith (Real.toNNReal (3 / ε)) (strainDir u) (raySet u ε) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
  exact HasRaySlope.dist_le hu hε (hasRaySlope_strainDir hu hε hx) (hasRaySlope_strainDir hu hε hy)

/-! ### L5(b): moving along a ray -/

/-- **L5(b)**, in terms of `HasRaySlope`: the shifted point has the same direction and the
remaining half-length. -/
theorem HasRaySlope.add_smul {u : Space n → ℝ} {ε : ℝ} {x θ : Space n}
    (h : HasRaySlope u ε x θ) {s : ℝ} (hs : |s| ≤ ε) :
    HasRaySlope u (ε - |s|) (x + s • θ) θ := by
  refine ⟨h.1, fun t ht => ?_⟩
  have h1 : |s + t| ≤ ε := by
    calc |s + t| ≤ |s| + |t| := abs_add_le _ _
      _ ≤ ε := by linarith
  rw [add_assoc, ← _root_.add_smul, h.2 _ h1, h.2 _ hs]
  ring

/-- **L5(b)**: `x ∈ raySet u ε`, `|s| < ε` gives `x + s θ ∈ raySet u (ε - |s|)` with the same
direction `strainDir`, and `u (x + s θ) = u x + s`. -/
theorem add_smul_strainDir_mem_raySet {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε : ℝ}
    (hε : 0 < ε) {x : Space n} (hx : x ∈ raySet u ε) {s : ℝ} (hs : |s| < ε) :
    x + s • strainDir u x ∈ raySet u (ε - |s|) ∧
      strainDir u (x + s • strainDir u x) = strainDir u x ∧
      u (x + s • strainDir u x) = u x + s := by
  have h := hasRaySlope_strainDir hu hε hx
  have h' := h.add_smul hs.le
  have hpos : 0 < ε - |s| := by linarith
  exact ⟨⟨_, h'⟩, h'.strainDir_eq hu hpos, h.2 s hs.le⟩

/-! ### L5(c): the ray invariant -/

/-- The ray invariant: the direction `θ` and the point `x - u x • θ` of the line at `u`-coordinate
`0`. For strain points it determines the line `{x + (t - u x) • θ}` and is constant on rays. -/
noncomputable def rayInv (u : Space n → ℝ) (x : Space n) : Space n × Space n :=
  (strainDir u x, x - u x • strainDir u x)

/-- The invariant is constant along rays. -/
theorem rayInv_add_smul {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε : ℝ} (hε : 0 < ε)
    {x : Space n} (hx : x ∈ raySet u ε) {s : ℝ} (hs : |s| < ε) :
    rayInv u (x + s • strainDir u x) = rayInv u x := by
  obtain ⟨-, hdir, hval⟩ := add_smul_strainDir_mem_raySet hu hε hx hs
  unfold rayInv
  rw [hdir, hval]
  ext
  · rfl
  · simp only [add_smul]; abel_nf

/-- Converse: equal invariants put the points on the same line, at `u`-coordinate difference. -/
theorem eq_add_sub_smul_of_rayInv_eq {u : Space n → ℝ} {x y : Space n}
    (h : rayInv u x = rayInv u y) : y = x + (u y - u x) • strainDir u x := by
  have h1 : strainDir u x = strainDir u y := congrArg Prod.fst h
  have h2 : x - u x • strainDir u x = y - u y • strainDir u y := congrArg Prod.snd h
  rw [← h1] at h2
  rw [sub_smul]
  calc y = (y - u y • strainDir u x) + u y • strainDir u x := by abel
    _ = (x - u x • strainDir u x) + u y • strainDir u x := by rw [h2]
    _ = _ := by abel

/-- If `u` has slope `c` along a segment from `x` in the unit direction `e`, then the ray
direction `θ` at `x` satisfies `⟪θ, e⟫ = c`. -/
theorem inner_eq_of_segment {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε : ℝ} (hε : 0 < ε)
    {x θ e : Space n} (h : HasRaySlope u ε x θ) (he : ‖e‖ = 1) {s c : ℝ} (hs : 0 < s)
    (hseg : ∀ t : ℝ, 0 ≤ t → t ≤ s → u (x + t • e) = u x + c * t) : ⟪θ, e⟫ = c := by
  by_contra hne
  set a : ℝ := |c - ⟪θ, e⟫| with ha
  have hapos : 0 < a := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  set t : ℝ := min s (ε * a) with ht
  have htpos : 0 < t := lt_min hs (by positivity)
  have hts : t ≤ s := min_le_left _ _
  have hte : t ≤ ε * a := min_le_right _ _
  have := abs_sub_inner_le_of_hasRaySlope hu hε h (x + t • e)
  rw [hseg t htpos.le hts] at this
  simp only [add_sub_cancel_left, inner_smul_right, norm_smul, he, Real.norm_eq_abs,
    abs_of_pos htpos] at this
  have e1 : c * t - t * ⟪θ, e⟫ = t * (c - ⟪θ, e⟫) := by ring
  rw [e1, abs_mul, abs_of_pos htpos, mul_one] at this
  have h2 : t * a ≤ t ^ 2 / (2 * ε) := this
  rw [le_div_iff₀ (by positivity)] at h2
  have h3 : t * a * (2 * ε) = t * (2 * ε * a) := by ring
  nlinarith

/-- A unit vector `θ` with `⟪θ, e⟫ = 1` for a unit vector `e` equals `e`. -/
theorem eq_of_inner_eq_one {θ e : Space n} (hθ : ‖θ‖ = 1) (he : ‖e‖ = 1) (h : ⟪θ, e⟫ = 1) :
    θ = e := by
  have : ‖θ - e‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hθ, he, h]; norm_num
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp this))

/-- Two strain points joined by a slope-one segment (`u y - u x = ‖y - x‖`) have the same ray
invariant. -/
theorem rayInv_eq_of_sub_eq_norm {u : Space n → ℝ} (hu : LipschitzWith 1 u) {x y : Space n}
    (hx : x ∈ Strain u) (hy : y ∈ Strain u) (h : u y - u x = ‖y - x‖) :
    rayInv u x = rayInv u y := by
  by_cases hxy : x = y
  · rw [hxy]
  have hs : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))
  set s : ℝ := ‖y - x‖ with hsdef
  set e : Space n := s⁻¹ • (y - x) with hedef
  have he : ‖e‖ = 1 := by
    rw [hedef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hs]
    exact inv_mul_cancel₀ hs.ne'
  have hye : y = x + s • e := by
    rw [hedef, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]; abel
  -- slope one on the segment
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ s → u (x + t • e) = u x + t := by
    intro t ht0 hts
    have d1 : dist (x + t • e) x = t := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he, Real.norm_eq_abs, abs_of_nonneg ht0,
        mul_one]
    have d2 : dist (x + t • e) y = s - t := by
      rw [dist_eq_norm, hye, show x + t • e - (x + s • e) = (t - s) • e by
        rw [sub_smul]; abel, norm_smul, he, Real.norm_eq_abs, abs_of_nonpos (by linarith),
        mul_one]
      ring
    have a1 := hu.dist_le_mul (x + t • e) x
    have a2 := hu.dist_le_mul (x + t • e) y
    rw [Real.dist_eq, NNReal.coe_one, one_mul, d1] at a1
    rw [Real.dist_eq, NNReal.coe_one, one_mul, d2] at a2
    have := (abs_le.mp a1).2
    have := (abs_le.mp a2).1
    linarith
  obtain ⟨εx, hεx, hxε⟩ := mem_strain_iff.mp hx
  obtain ⟨εy, hεy, hyε⟩ := mem_strain_iff.mp hy
  have hθx := hasRaySlope_strainDir hu hεx hxε
  have hθy := hasRaySlope_strainDir hu hεy hyε
  have c1 : ⟪strainDir u x, e⟫ = 1 :=
    inner_eq_of_segment hu hεx hθx he hs (c := 1) (by simpa using hseg)
  have c2 : ⟪strainDir u y, -e⟫ = -1 := by
    refine inner_eq_of_segment hu hεy hθy (by simpa using he) hs (c := -1) ?_
    intro t ht0 hts
    have : y + t • -e = x + (s - t) • e := by
      rw [hye, smul_neg, sub_smul]; abel
    have h' : u y = u x + s := by linarith
    rw [this, hseg (s - t) (by linarith) (by linarith), h']
    ring
  rw [inner_neg_right, neg_inj] at c2
  have d1 : strainDir u x = e := eq_of_inner_eq_one (norm_strainDir hx) he c1
  have d2 : strainDir u y = e := eq_of_inner_eq_one (norm_strainDir hy) he c2
  unfold rayInv
  rw [d1, d2]
  refine Prod.ext rfl ?_
  have h' : u y = u x + s := by linarith
  show x - u x • e = y - u y • e
  rw [h', hye, add_smul]; abel

/-- Strain points with `|u y - u x| = ‖y - x‖` (joined by a slope-one segment) lie on a common
ray. -/
theorem rayInv_eq_of_abs_sub_eq_dist {u : Space n → ℝ} (hu : LipschitzWith 1 u) {x y : Space n}
    (hx : x ∈ Strain u) (hy : y ∈ Strain u) (h : |u y - u x| = ‖y - x‖) :
    rayInv u x = rayInv u y := by
  rcases abs_cases (u y - u x) with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact rayInv_eq_of_sub_eq_norm hu hx hy (h1 ▸ h)
  · refine (rayInv_eq_of_sub_eq_norm hu hy hx ?_).symm
    rw [norm_sub_rev]; linarith

/-! ### L5(d): Borel measurability of the direction and of the ray invariant -/

/-- **L5(d).** `strainDir u` (zero off `Strain u`) is Borel measurable on `Space n`. -/
theorem measurable_strainDir {u : Space n → ℝ} (hu : LipschitzWith 1 u) :
    Measurable (strainDir u) := by
  refine measurable_of_isOpen fun V hV => ?_
  have hpre : strainDir u ⁻¹' V =
      (⋃ m : ℕ, (raySet u (1 / ((m : ℝ) + 1)) ∩ strainDir u ⁻¹' V)) ∪
        ((Strain u)ᶜ ∩ {_x | (0 : Space n) ∈ V}) := by
    ext x
    by_cases hx : x ∈ Strain u
    · obtain ⟨m, hm⟩ := mem_iUnion.mp hx
      simp only [mem_preimage, mem_union, mem_iUnion, mem_inter_iff, mem_compl_iff, mem_ofPred_eq]
      constructor
      · intro h; exact Or.inl ⟨m, hm, h⟩
      · rintro (⟨_, _, h⟩ | ⟨h, _⟩)
        · exact h
        · exact absurd hx h
    · simp only [mem_preimage, mem_union, mem_iUnion, mem_inter_iff, mem_compl_iff, mem_ofPred_eq,
        strainDir_of_not_mem hx]
      constructor
      · intro h; exact Or.inr ⟨hx, h⟩
      · rintro (⟨m, hm, _⟩ | ⟨_, h⟩)
        · exact absurd (mem_iUnion.mpr ⟨m, hm⟩) hx
        · exact h
  rw [hpre]
  refine MeasurableSet.union (MeasurableSet.iUnion fun m => ?_)
    ((measurableSet_strain hu).compl.inter (MeasurableSet.const _))
  have hcont := (lipschitzOnWith_strainDir hu (u := u)
    (ε := 1 / ((m : ℝ) + 1)) (by positivity)).continuousOn
  obtain ⟨W, hW, hWeq⟩ := continuousOn_iff'.mp hcont V hV
  rw [inter_comm, hWeq]
  exact hW.measurableSet.inter (isClosed_raySet hu _).measurableSet

/-- The ray invariant is Borel measurable on `Space n`. -/
theorem measurable_rayInv {u : Space n → ℝ} (hu : LipschitzWith 1 u) : Measurable (rayInv u) :=
  (measurable_strainDir hu).prodMk
    (measurable_id.sub (hu.continuous.measurable.smul (measurable_strainDir hu)))

/-! ### L5(c), continued: maximal slope-one segments and their endpoints -/

/-- The `u`-coordinates `τ` at which the line `{q.2 + τ • q.1}` has `u = τ`. -/
def raySlopeTimes (u : Space n → ℝ) (q : Space n × Space n) : Set ℝ :=
  {τ | u (q.2 + τ • q.1) = τ}

/-- Lower endpoint (in the `u`-coordinate) of the maximal slope-one segment through `x`. -/
noncomputable def rayLo (u : Space n → ℝ) (x : Space n) : EReal :=
  sInf (((↑) : ℝ → EReal) '' raySlopeTimes u (rayInv u x))

/-- Upper endpoint (in the `u`-coordinate) of the maximal slope-one segment through `x`. -/
noncomputable def rayHi (u : Space n → ℝ) (x : Space n) : EReal :=
  sSup (((↑) : ℝ → EReal) '' raySlopeTimes u (rayInv u x))

theorem mem_raySlopeTimes_rayInv {u : Space n → ℝ} {x : Space n} {τ : ℝ} :
    τ ∈ raySlopeTimes u (rayInv u x) ↔ u (x + (τ - u x) • strainDir u x) = τ := by
  have : (rayInv u x).2 + τ • (rayInv u x).1 = x + (τ - u x) • strainDir u x := by
    simp only [rayInv]; module
  simp only [raySlopeTimes, mem_ofPred_eq, this]

theorem self_mem_raySlopeTimes {u : Space n → ℝ} {x : Space n} :
    u x ∈ raySlopeTimes u (rayInv u x) := by
  simp [mem_raySlopeTimes_rayInv]

theorem rayLo_eq_of_rayInv_eq {u : Space n → ℝ} {x y : Space n} (h : rayInv u x = rayInv u y) :
    rayLo u x = rayLo u y := by
  unfold rayLo; rw [h]

theorem rayHi_eq_of_rayInv_eq {u : Space n → ℝ} {x y : Space n} (h : rayInv u x = rayInv u y) :
    rayHi u x = rayHi u y := by
  unfold rayHi; rw [h]

/-- The set of slope-one parameters of a line is an interval. -/
theorem ordConnected_raySlopeTimes {u : Space n → ℝ} (hu : LipschitzWith 1 u)
    {q : Space n × Space n} (hq : ‖q.1‖ = 1) : (raySlopeTimes u q).OrdConnected := by
  refine ⟨fun a ha b hb τ hτ => ?_⟩
  have hd : ∀ σ σ' : ℝ, dist (q.2 + σ • q.1) (q.2 + σ' • q.1) = |σ - σ'| := by
    intro σ σ'
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hq, mul_one,
      Real.norm_eq_abs]
  have h1 := hu.dist_le_mul (q.2 + τ • q.1) (q.2 + a • q.1)
  have h2 := hu.dist_le_mul (q.2 + τ • q.1) (q.2 + b • q.1)
  rw [Real.dist_eq, NNReal.coe_one, one_mul, hd] at h1 h2
  have ha' : u (q.2 + a • q.1) = a := ha
  have hb' : u (q.2 + b • q.1) = b := hb
  have e1 : |τ - a| = τ - a := abs_of_nonneg (by linarith [hτ.1])
  have e2 : |τ - b| = b - τ := by
    rw [abs_sub_comm]; exact abs_of_nonneg (by linarith [hτ.2])
  rw [ha', e1] at h1
  rw [hb', e2] at h2
  have := (abs_le.mp h1).2
  have := (abs_le.mp h2).1
  show u (q.2 + τ • q.1) = τ
  linarith

/-- On `raySet u ε` the slope-one parameters contain the `u`-interval of radius `ε`. -/
theorem Icc_subset_raySlopeTimes {u : Space n → ℝ} (hu : LipschitzWith 1 u) {ε : ℝ}
    (hε : 0 < ε) {x : Space n} (hx : x ∈ raySet u ε) :
    Icc (u x - ε) (u x + ε) ⊆ raySlopeTimes u (rayInv u x) := by
  intro τ hτ
  rw [mem_raySlopeTimes_rayInv, (hasRaySlope_strainDir hu hε hx).2 (τ - u x)
    (abs_le.mpr ⟨by linarith [hτ.1], by linarith [hτ.2]⟩)]
  ring

theorem rayLo_le {u : Space n → ℝ} (x : Space n) : rayLo u x ≤ (u x : ℝ) :=
  sInf_le (mem_image_of_mem _ self_mem_raySlopeTimes)

theorem le_rayHi {u : Space n → ℝ} (x : Space n) : ((u x : ℝ) : EReal) ≤ rayHi u x :=
  le_sSup (mem_image_of_mem _ self_mem_raySlopeTimes)

theorem rayLo_lt {u : Space n → ℝ} (hu : LipschitzWith 1 u) {x : Space n} (hx : x ∈ Strain u) :
    rayLo u x < (u x : ℝ) := by
  obtain ⟨ε, hε, hxε⟩ := mem_strain_iff.mp hx
  have h1 : rayLo u x ≤ ((u x - ε : ℝ) : EReal) :=
    sInf_le (mem_image_of_mem _ (Icc_subset_raySlopeTimes hu hε hxε ⟨le_rfl, by linarith⟩))
  exact h1.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))

theorem lt_rayHi {u : Space n → ℝ} (hu : LipschitzWith 1 u) {x : Space n} (hx : x ∈ Strain u) :
    ((u x : ℝ) : EReal) < rayHi u x := by
  obtain ⟨ε, hε, hxε⟩ := mem_strain_iff.mp hx
  have h1 : ((u x + ε : ℝ) : EReal) ≤ rayHi u x :=
    le_sSup (mem_image_of_mem _ (Icc_subset_raySlopeTimes hu hε hxε ⟨by linarith, le_rfl⟩))
  exact (EReal.coe_lt_coe_iff.mpr (by linarith)).trans_le h1

/-- Slope-one parameters lie in `[rayLo, rayHi]`; conversely (`mem_raySlopeTimes_of_lt_of_lt`)
at a strain point every parameter in `(rayLo, rayHi)` is a slope-one parameter. -/
theorem raySlopeTimes_subset_Icc {u : Space n → ℝ} {x : Space n} {τ : ℝ}
    (h : τ ∈ raySlopeTimes u (rayInv u x)) : rayLo u x ≤ τ ∧ (τ : EReal) ≤ rayHi u x :=
  ⟨sInf_le (mem_image_of_mem _ h), le_sSup (mem_image_of_mem _ h)⟩

theorem mem_raySlopeTimes_of_lt_of_lt {u : Space n → ℝ} (hu : LipschitzWith 1 u) {x : Space n}
    (hx : x ∈ Strain u) {τ : ℝ} (h1 : rayLo u x < τ) (h2 : (τ : EReal) < rayHi u x) :
    τ ∈ raySlopeTimes u (rayInv u x) := by
  have hq : ‖(rayInv u x).1‖ = 1 := norm_strainDir hx
  obtain ⟨_, ⟨a, ha, rfl⟩, ha'⟩ := sInf_lt_iff.mp h1
  obtain ⟨_, ⟨b, hb, rfl⟩, hb'⟩ := lt_sSup_iff.mp h2
  have hab := EReal.coe_lt_coe_iff.mp ha'
  have hbb := EReal.coe_lt_coe_iff.mp hb'
  exact (ordConnected_raySlopeTimes hu hq).out ha hb ⟨hab.le, hbb.le⟩

/-- Off `Strain u` the endpoints are the trivial ones. -/
theorem rayLo_of_not_mem {u : Space n → ℝ} {x : Space n} (hx : x ∉ Strain u) :
    rayLo u x = (u x : ℝ) := by
  have : raySlopeTimes u (rayInv u x) = {u x} := by
    ext τ
    simp [mem_raySlopeTimes_rayInv, strainDir_of_not_mem hx, eq_comm]
  simp [rayLo, this]

theorem rayHi_of_not_mem {u : Space n → ℝ} {x : Space n} (hx : x ∉ Strain u) :
    rayHi u x = (u x : ℝ) := by
  have : raySlopeTimes u (rayInv u x) = {u x} := by
    ext τ
    simp [mem_raySlopeTimes_rayInv, strainDir_of_not_mem hx, eq_comm]
  simp [rayHi, this]

/-- Rational-witness description of `rayLo < a` at a strain point. -/
theorem rayLo_lt_iff {u : Space n → ℝ} (hu : LipschitzWith 1 u) {x : Space n}
    (hx : x ∈ Strain u) (a : EReal) :
    rayLo u x < a ↔ ∃ r : ℚ, (((r : ℚ) : ℝ) : EReal) < a ∧
      u (x + (((r : ℚ) : ℝ) - u x) • strainDir u x) = ((r : ℚ) : ℝ) := by
  have hq : ‖(rayInv u x).1‖ = 1 := norm_strainDir hx
  obtain ⟨ε, hε, hxε⟩ := mem_strain_iff.mp hx
  have hI := Icc_subset_raySlopeTimes hu hε hxε
  have hoc := ordConnected_raySlopeTimes hu hq
  constructor
  · intro h
    obtain ⟨_, ⟨τ0, hτ0, rfl⟩, hlt⟩ := sInf_lt_iff.mp h
    by_cases hc : τ0 < u x
    · obtain ⟨a', ha1, ha2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
      have ha1' := EReal.coe_lt_coe_iff.mp ha1
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (lt_min ha1' hc)
      have hr3 : (r : ℝ) < a' := hr2.trans_le (min_le_left _ _)
      have hr4 : (r : ℝ) < u x := hr2.trans_le (min_le_right _ _)
      refine ⟨r, (EReal.coe_lt_coe_iff.mpr hr3).trans ha2, ?_⟩
      have := hoc.out hτ0 self_mem_raySlopeTimes ⟨hr1.le, hr4.le⟩
      exact mem_raySlopeTimes_rayInv.mp this
    · replace hc := not_lt.mp hc
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show u x - ε < u x by linarith)
      refine ⟨r, (EReal.coe_lt_coe_iff.mpr (hr2.trans_le hc)).trans hlt, ?_⟩
      exact mem_raySlopeTimes_rayInv.mp (hI ⟨hr1.le, by linarith⟩)
  · rintro ⟨r, hr, hu'⟩
    have hm : ((r : ℚ) : ℝ) ∈ raySlopeTimes u (rayInv u x) := mem_raySlopeTimes_rayInv.mpr hu'
    exact (sInf_le (mem_image_of_mem _ hm)).trans_lt hr

/-- Rational-witness description of `a < rayHi` at a strain point. -/
theorem lt_rayHi_iff {u : Space n → ℝ} (hu : LipschitzWith 1 u) {x : Space n}
    (hx : x ∈ Strain u) (a : EReal) :
    a < rayHi u x ↔ ∃ r : ℚ, a < (((r : ℚ) : ℝ) : EReal) ∧
      u (x + (((r : ℚ) : ℝ) - u x) • strainDir u x) = ((r : ℚ) : ℝ) := by
  have hq : ‖(rayInv u x).1‖ = 1 := norm_strainDir hx
  obtain ⟨ε, hε, hxε⟩ := mem_strain_iff.mp hx
  have hI := Icc_subset_raySlopeTimes hu hε hxε
  have hoc := ordConnected_raySlopeTimes hu hq
  constructor
  · intro h
    obtain ⟨_, ⟨τ0, hτ0, rfl⟩, hlt⟩ := lt_sSup_iff.mp h
    by_cases hc : u x < τ0
    · obtain ⟨a', ha1, ha2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
      have ha2' := EReal.coe_lt_coe_iff.mp ha2
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (max_lt ha2' hc)
      have hr3 : a' < (r : ℝ) := (le_max_left _ _).trans_lt hr1
      have hr4 : u x < (r : ℝ) := (le_max_right _ _).trans_lt hr1
      refine ⟨r, ha1.trans (EReal.coe_lt_coe_iff.mpr hr3), ?_⟩
      have := hoc.out self_mem_raySlopeTimes hτ0 ⟨hr4.le, hr2.le⟩
      exact mem_raySlopeTimes_rayInv.mp this
    · replace hc := not_lt.mp hc
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show u x < u x + ε by linarith)
      refine ⟨r, hlt.trans_le ((EReal.coe_le_coe_iff.mpr hc).trans
        (EReal.coe_lt_coe_iff.mpr hr1).le), ?_⟩
      exact mem_raySlopeTimes_rayInv.mp (hI ⟨by linarith, hr2.le⟩)
  · rintro ⟨r, hr, hu'⟩
    have hm : ((r : ℚ) : ℝ) ∈ raySlopeTimes u (rayInv u x) := mem_raySlopeTimes_rayInv.mpr hu'
    exact hr.trans_le (le_sSup (mem_image_of_mem _ hm))

/-- **L5(c)**: `rayLo` is Borel measurable on `Space n` (it equals `u` off `Strain u`). -/
theorem measurable_rayLo {u : Space n → ℝ} (hu : LipschitzWith 1 u) : Measurable (rayLo u) := by
  refine measurable_of_Iio fun a => ?_
  have hmeas : ∀ r : ℚ, Measurable fun x => u (x + (((r : ℚ) : ℝ) - u x) • strainDir u x) :=
    fun r => hu.continuous.measurable.comp (measurable_id.add
      ((measurable_const.sub hu.continuous.measurable).smul (measurable_strainDir hu)))
  have hpre : rayLo u ⁻¹' Iio a =
      (Strain u ∩ ⋃ r : ℚ, ({_x | (((r : ℚ) : ℝ) : EReal) < a} ∩
        {x | u (x + (((r : ℚ) : ℝ) - u x) • strainDir u x) = ((r : ℚ) : ℝ)})) ∪
      ((Strain u)ᶜ ∩ {x | ((u x : ℝ) : EReal) < a}) := by
    ext x
    by_cases hx : x ∈ Strain u
    · simp only [mem_preimage, mem_Iio, mem_union, mem_inter_iff, mem_iUnion, mem_ofPred_eq,
        mem_compl_iff, hx, true_and, not_true_eq_false, false_and, or_false]
      exact rayLo_lt_iff hu hx a
    · simp only [mem_preimage, mem_Iio, mem_union, mem_inter_iff, mem_iUnion, mem_ofPred_eq,
        mem_compl_iff, hx, false_and, false_or, not_false_eq_true, true_and,
        rayLo_of_not_mem hx]
  rw [hpre]
  refine ((measurableSet_strain hu).inter (MeasurableSet.iUnion fun r => ?_)).union
    ((measurableSet_strain hu).compl.inter ?_)
  · exact (MeasurableSet.const _).inter
      (measurableSet_eq_fun (hmeas r) measurable_const)
  · exact measurableSet_lt (measurable_coe_real_ereal.comp hu.continuous.measurable)
      measurable_const

/-- **L5(c)**: `rayHi` is Borel measurable on `Space n` (it equals `u` off `Strain u`). -/
theorem measurable_rayHi {u : Space n → ℝ} (hu : LipschitzWith 1 u) : Measurable (rayHi u) := by
  refine measurable_of_Ioi fun a => ?_
  have hmeas : ∀ r : ℚ, Measurable fun x => u (x + (((r : ℚ) : ℝ) - u x) • strainDir u x) :=
    fun r => hu.continuous.measurable.comp (measurable_id.add
      ((measurable_const.sub hu.continuous.measurable).smul (measurable_strainDir hu)))
  have hpre : rayHi u ⁻¹' Ioi a =
      (Strain u ∩ ⋃ r : ℚ, ({_x | a < (((r : ℚ) : ℝ) : EReal)} ∩
        {x | u (x + (((r : ℚ) : ℝ) - u x) • strainDir u x) = ((r : ℚ) : ℝ)})) ∪
      ((Strain u)ᶜ ∩ {x | a < ((u x : ℝ) : EReal)}) := by
    ext x
    by_cases hx : x ∈ Strain u
    · simp only [mem_preimage, mem_Ioi, mem_union, mem_inter_iff, mem_iUnion, mem_ofPred_eq,
        mem_compl_iff, hx, true_and, not_true_eq_false, false_and, or_false]
      exact lt_rayHi_iff hu hx a
    · simp only [mem_preimage, mem_Ioi, mem_union, mem_inter_iff, mem_iUnion, mem_ofPred_eq,
        mem_compl_iff, hx, false_and, false_or, not_false_eq_true, true_and,
        rayHi_of_not_mem hx]
  rw [hpre]
  refine ((measurableSet_strain hu).inter (MeasurableSet.iUnion fun r => ?_)).union
    ((measurableSet_strain hu).compl.inter ?_)
  · exact (MeasurableSet.const _).inter
      (measurableSet_eq_fun (hmeas r) measurable_const)
  · exact measurableSet_lt measurable_const
      (measurable_coe_real_ereal.comp hu.continuous.measurable)

/-- Borel measurability of `rayLo`, `rayHi`, `rayInv` as functions on the Borel subset
`Strain u` (subtype). -/
theorem measurable_rayLo_strain {u : Space n → ℝ} (hu : LipschitzWith 1 u) :
    Measurable fun x : Strain u => rayLo u x :=
  (measurable_rayLo hu).comp measurable_subtype_coe

theorem measurable_rayHi_strain {u : Space n → ℝ} (hu : LipschitzWith 1 u) :
    Measurable fun x : Strain u => rayHi u x :=
  (measurable_rayHi hu).comp measurable_subtype_coe

theorem measurable_rayInv_strain {u : Space n → ℝ} (hu : LipschitzWith 1 u) :
    Measurable fun x : Strain u => rayInv u x :=
  (measurable_rayInv hu).comp measurable_subtype_coe

end CvxBody.Geometry
