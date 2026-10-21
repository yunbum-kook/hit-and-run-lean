module
public import CvxBody.Analysis.NeedleLogConcaveDisint

@[expose] public section


/-!
# Deterministic ray geometry for the needle log-concavity argument (WP-H)

Elementary facts about a ray `t ↦ rayPt ω t = ω.2 + t • ω.1` of a `1`-Lipschitz function `u`
(`‖ω.1‖ = 1`):

* `WindowSet u ε α β`: the set of ray invariants `ω` such that for every `τ ∈ [α, β]` the point
  `rayPt ω τ` lies in `raySet u ε` and `u (rayPt ω τ) = τ`; it is closed;
* on such a window the ray direction at `rayPt ω τ` is `ω.1` (`strainDir_rayPt_of_window`), so
  `rayInv u (rayPt ω τ) = ω`;
* `rayJ u D₀ ω`: the open interval of parameters `t` in the interior of the slope-one set of the
  ray whose point lies in the open convex set `D₀`;
* the Jacobian `det (1 + s H)` of a symmetric operator `H` factors as `∏_j (1 + s λ_j)` with real
  eigenvalues `λ_j` (`exists_eigen_det`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open OAI.LeanBlast.KLS CvxBody.Geometry
open scoped ENNReal RealInnerProductSpace InnerProductSpace

namespace CvxBody.NeedleLC

variable {n : ℕ} {u : Space n → ℝ}

theorem rayPt_add_smul (ω : Space n × Space n) (t s : ℝ) :
    rayPt ω t + s • ω.1 = rayPt ω (t + s) := by
  simp only [rayPt, add_smul]; abel

theorem continuous_rayPt_left (τ : ℝ) : Continuous fun ω : Space n × Space n => rayPt ω τ :=
  continuous_snd.add ((continuous_const : Continuous fun _ : Space n × Space n => τ).smul
    continuous_fst)

theorem continuous_rayPt_right (ω : Space n × Space n) : Continuous fun t : ℝ => rayPt ω t :=
  continuous_const.add (continuous_id.smul continuous_const)

/-! ### Windows -/

/-- The ray invariants `ω` such that for every `τ ∈ [α, β]`, `rayPt ω τ ∈ raySet u ε` and
`u (rayPt ω τ) = τ`. -/
def WindowSet (u : Space n → ℝ) (ε α β : ℝ) : Set (Space n × Space n) :=
  {ω | ∀ τ ∈ Icc α β, rayPt ω τ ∈ raySet u ε ∧ u (rayPt ω τ) = τ}

theorem isClosed_windowSet (hu : LipschitzWith 1 u) (ε α β : ℝ) :
    IsClosed (WindowSet u ε α β) := by
  have : WindowSet u ε α β = ⋂ τ ∈ Icc α β,
      ((fun ω : Space n × Space n => rayPt ω τ) ⁻¹' raySet u ε ∩
        {ω | u (rayPt ω τ) = τ}) := by
    ext ω
    simp only [WindowSet, mem_ofPred_eq, mem_iInter, mem_inter_iff, mem_preimage]
  rw [this]
  refine isClosed_biInter fun τ _ => ?_
  exact ((isClosed_raySet hu ε).preimage (continuous_rayPt_left τ)).inter
    (isClosed_eq (hu.continuous.comp (continuous_rayPt_left τ)) continuous_const)

theorem measurableSet_windowSet (hu : LipschitzWith 1 u) (ε α β : ℝ) :
    MeasurableSet (WindowSet u ε α β) :=
  (isClosed_windowSet hu ε α β).measurableSet

/-- A unit vector `e` along which `u` has slope one from a point `y ∈ raySet u ε` is the ray
direction at `y`. -/
theorem strainDir_eq_of_segment (hu : LipschitzWith 1 u) {ε : ℝ} (hε : 0 < ε) {y e : Space n}
    (hy : y ∈ raySet u ε) (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s)
    (hseg : ∀ t : ℝ, 0 ≤ t → t ≤ s → u (y + t • e) = u y + 1 * t) : strainDir u y = e := by
  have h := inner_eq_of_segment hu hε (hasRaySlope_strainDir hu hε hy) he hs hseg
  exact eq_of_inner_eq_one (norm_strainDir (raySet_subset_strain hε hy)) he h

/-- If `u` has slope `-1` from `y ∈ raySet u ε` along a unit vector `e`, then the ray direction at
`y` is `-e`. -/
theorem strainDir_eq_neg_of_segment (hu : LipschitzWith 1 u) {ε : ℝ} (hε : 0 < ε) {y e : Space n}
    (hy : y ∈ raySet u ε) (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s)
    (hseg : ∀ t : ℝ, 0 ≤ t → t ≤ s → u (y + t • e) = u y + (-1) * t) : strainDir u y = -e := by
  have h := inner_eq_of_segment hu hε (hasRaySlope_strainDir hu hε hy) he hs hseg
  refine eq_of_inner_eq_one (norm_strainDir (raySet_subset_strain hε hy)) (by simpa using he) ?_
  rw [inner_neg_right, h]; norm_num

/-- On a window, the ray direction at `rayPt ω τ` is `ω.1`. -/
theorem strainDir_rayPt_of_window (hu : LipschitzWith 1 u) {ε α β : ℝ} (hε : 0 < ε)
    (hαβ : α < β) {ω : Space n × Space n} (hω1 : ‖ω.1‖ = 1) (hω : ω ∈ WindowSet u ε α β)
    {τ : ℝ} (hτ : τ ∈ Icc α β) : strainDir u (rayPt ω τ) = ω.1 := by
  obtain ⟨hy, hyu⟩ := hω τ hτ
  rcases lt_or_ge τ β with h | h
  · refine strainDir_eq_of_segment hu hε hy hω1 (s := β - τ) (by linarith) fun t ht0 hts => ?_
    rw [rayPt_add_smul, (hω (τ + t) ⟨by linarith [hτ.1], by linarith⟩).2, hyu, one_mul]
  · have hτβ : τ = β := le_antisymm hτ.2 h
    have hneg : ‖-ω.1‖ = 1 := by rw [norm_neg]; exact hω1
    have := strainDir_eq_neg_of_segment hu hε hy hneg (s := β - α) (by linarith) fun t ht0 hts => ?_
    · simpa using this
    · have e : rayPt ω τ + t • -ω.1 = rayPt ω (τ - t) := by
        rw [smul_neg, ← neg_smul, rayPt_add_smul]
        simp [sub_eq_add_neg]
      rw [e, (hω (τ - t) ⟨by linarith [hτ.1], by linarith⟩).2, hyu]
      ring

theorem rayInv_rayPt_of_window (hu : LipschitzWith 1 u) {ε α β : ℝ} (hε : 0 < ε) (hαβ : α < β)
    {ω : Space n × Space n} (hω1 : ‖ω.1‖ = 1) (hω : ω ∈ WindowSet u ε α β) {τ : ℝ}
    (hτ : τ ∈ Icc α β) : rayInv u (rayPt ω τ) = ω ∧ rayPt ω τ ∈ Strain u := by
  have hd := strainDir_rayPt_of_window hu hε hαβ hω1 hω hτ
  refine ⟨?_, raySet_subset_strain hε (hω τ hτ).1⟩
  refine Prod.ext hd ?_
  show rayPt ω τ - u (rayPt ω τ) • strainDir u (rayPt ω τ) = ω.2
  rw [hd, (hω τ hτ).2]
  simp [rayPt]

/-! ### The ray of a strain point -/

theorem eq_rayPt_of_rayInv {y : Space n} {ω : Space n × Space n} (h : rayInv u y = ω) :
    y = rayPt ω (u y) := by
  have h1 : strainDir u y = ω.1 := congrArg Prod.fst h
  have h2 : y - u y • strainDir u y = ω.2 := congrArg Prod.snd h
  show y = ω.2 + u y • ω.1
  rw [← h1, ← h2]
  simp

theorem u_eq_of_rayInv {ω : Space n × Space n} (hω1 : ‖ω.1‖ = 1) {y : Space n}
    (h : rayInv u y = ω) {t : ℝ} (hy : y = rayPt ω t) : u y = t := by
  have h1 : rayPt ω t = rayPt ω (u y) := hy.symm.trans (eq_rayPt_of_rayInv h)
  have hne : ω.1 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hω1; exact zero_ne_one hω1
  have : t • ω.1 = u y • ω.1 := by
    have h1' : ω.2 + t • ω.1 = ω.2 + u y • ω.1 := h1
    exact add_left_cancel h1'
  exact ((smul_left_injective ℝ hne this)).symm

/-- The set of slope-one parameters of the line `ω`. -/
theorem mem_raySlopeTimes_iff {ω : Space n × Space n} {τ : ℝ} :
    τ ∈ raySlopeTimes u ω ↔ u (rayPt ω τ) = τ := Iff.rfl

theorem mem_interior_raySlopeTimes_iff {ω : Space n × Space n} {t : ℝ} :
    t ∈ interior (raySlopeTimes u ω) ↔ ∃ δ > 0, ∀ τ : ℝ, |τ - t| ≤ δ → u (rayPt ω τ) = τ := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  constructor
  · rintro ⟨r, hr, hsub⟩
    refine ⟨r / 2, by positivity, fun τ hτ => hsub ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    linarith
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, fun τ hτ => h τ ?_⟩
    rw [Metric.mem_ball, Real.dist_eq] at hτ
    exact hτ.le

/-- The open interval of parameters `t` in the interior of the slope-one set of the line `ω` whose
point `rayPt ω t` lies in `D₀`. -/
def rayJ (u : Space n → ℝ) (D₀ : Set (Space n)) (ω : Space n × Space n) : Set ℝ :=
  interior (raySlopeTimes u ω) ∩ (fun t => rayPt ω t) ⁻¹' D₀

theorem isOpen_rayJ {D₀ : Set (Space n)} (hD₀ : IsOpen D₀) (ω : Space n × Space n) :
    IsOpen (rayJ u D₀ ω) :=
  isOpen_interior.inter (hD₀.preimage (continuous_rayPt_right ω))

theorem rayJ_subset (D₀ : Set (Space n)) (ω : Space n × Space n) :
    rayJ u D₀ ω ⊆ (fun t => rayPt ω t) ⁻¹' D₀ := inter_subset_right

theorem convex_preimage_rayPt {D₀ : Set (Space n)} (hD₀ : Convex ℝ D₀) (ω : Space n × Space n) :
    Convex ℝ ((fun t => rayPt ω t) ⁻¹' D₀) := by
  intro x hx y hy a b ha hb hab
  simp only [mem_preimage] at hx hy ⊢
  have : rayPt ω (a • x + b • y) = a • rayPt ω x + b • rayPt ω y := by
    simp only [rayPt, smul_eq_mul, smul_add, smul_smul, mul_comm a x, mul_comm b y]
    have h1 : ω.2 = a • ω.2 + b • ω.2 := by rw [← add_smul, hab, one_smul]
    conv_lhs => rw [h1]
    module
  rw [this]
  exact hD₀ hx hy ha hb hab

theorem convex_rayJ (hu : LipschitzWith 1 u) {D₀ : Set (Space n)} (hD₀ : Convex ℝ D₀)
    {ω : Space n × Space n} (hω1 : ‖ω.1‖ = 1) : Convex ℝ (rayJ u D₀ ω) :=
  ((ordConnected_raySlopeTimes hu (q := ω) hω1).convex.interior).inter
    (convex_preimage_rayPt hD₀ ω)

/-- If `rayPt ω t` is a strain point with invariant `ω` lying in `D₀`, then `t ∈ rayJ u D₀ ω`. -/
theorem mem_rayJ_of_rayInv (hu : LipschitzWith 1 u) {D₀ : Set (Space n)} {ω : Space n × Space n}
    {t : ℝ} (h1 : rayInv u (rayPt ω t) = ω) (h2 : rayPt ω t ∈ Strain u)
    (h3 : rayPt ω t ∈ D₀) : t ∈ rayJ u D₀ ω := by
  refine ⟨?_, h3⟩
  have hω1 : ‖ω.1‖ = 1 := by
    rw [← h1]; exact norm_strainDir h2
  obtain ⟨ε, hε, hxε⟩ := mem_strain_iff.mp h2
  have hslope := hasRaySlope_strainDir hu hε hxε
  have hθ : strainDir u (rayPt ω t) = ω.1 := congrArg Prod.fst h1
  have hut : u (rayPt ω t) = t := u_eq_of_rayInv hω1 h1 rfl
  rw [mem_interior_raySlopeTimes_iff]
  refine ⟨ε, hε, fun τ hτ => ?_⟩
  have := hslope.2 (τ - t) hτ
  rw [hθ, rayPt_add_smul, hut] at this
  simpa using this

/-- Every parameter in `rayJ` lies in some window of a ray with unit direction. -/
theorem exists_window_of_mem_rayJ {D₀ : Set (Space n)}
    {ω : Space n × Space n} (hω1 : ‖ω.1‖ = 1) {t : ℝ} (ht : t ∈ rayJ u D₀ ω) :
    ∃ (m : ℕ) (α β : ℚ), (α : ℝ) < β ∧ (α : ℝ) < t ∧ t < β ∧
      ω ∈ WindowSet u (1 / ((m : ℝ) + 1)) α β := by
  obtain ⟨δ, hδ, h⟩ := mem_interior_raySlopeTimes_iff.1 ht.1
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hδ)
  obtain ⟨α, hα1, hα2⟩ := exists_rat_btwn (show t - δ / 2 < t by linarith)
  obtain ⟨β, hβ1, hβ2⟩ := exists_rat_btwn (show t < t + δ / 2 by linarith)
  refine ⟨m, α, β, by linarith, hα2, hβ1, fun τ hτ => ?_⟩
  have hτt : |τ - t| < δ / 2 := abs_lt.2 ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hut : u (rayPt ω τ) = τ := h τ (by linarith)
  refine ⟨⟨ω.1, hω1, fun s hs => ?_⟩, hut⟩
  have hs' : |s| ≤ 1 / ((m : ℝ) + 1) := hs
  have h3 : |τ + s - t| ≤ δ := by
    calc |τ + s - t| = |(τ - t) + s| := by ring_nf
      _ ≤ |τ - t| + |s| := abs_add_le _ _
      _ ≤ δ := by linarith
  rw [rayPt_add_smul, h _ h3, hut]

/-! ### The Jacobian determinant of a symmetric operator -/

/-- For a symmetric operator `H` with `-(1/ε) ≤ H ≤ 1/ε`, `det (1 + s H) = ∏_j (1 + s λ_j)` with real
eigenvalues `λ_j`, `|λ_j| ≤ 1/ε`. -/
theorem exists_eigen_det {ε : ℝ} (H : Space n →L[ℝ] Space n)
    (hsymm : ∀ v w, ⟪H v, w⟫_ℝ = ⟪v, H w⟫_ℝ)
    (hb : ∀ v, -(1 / ε) * ‖v‖ ^ 2 ≤ ⟪H v, v⟫_ℝ ∧ ⟪H v, v⟫_ℝ ≤ (1 / ε) * ‖v‖ ^ 2) :
    ∃ lam : Fin n → ℝ, (∀ j, |lam j| ≤ 1 / ε) ∧ ∀ s : ℝ,
      (ContinuousLinearMap.id ℝ (Space n) + s • H).det = ∏ j, (1 + s * lam j) := by
  have hT : (H : Space n →ₗ[ℝ] Space n).IsSymmetric := fun x y => hsymm x y
  have hn : Module.finrank ℝ (Space n) = n := finrank_euclideanSpace_fin
  set b := hT.eigenvectorBasis hn with hbdef
  have hev : ∀ j, H (b j) = hT.eigenvalues hn j • b j := fun j => by
    have := hT.apply_eigenvectorBasis hn j
    exact this
  refine ⟨fun j => hT.eigenvalues hn j, fun j => ?_, fun s => ?_⟩
  · have h1 := hb (b j)
    rw [hev j, inner_smul_left, b.norm_eq_one j] at h1
    simp only [conj_trivial, real_inner_self_eq_norm_sq, b.norm_eq_one j] at h1
    rw [abs_le]
    constructor <;> nlinarith [h1.1, h1.2]
  · set T : Space n →ₗ[ℝ] Space n :=
      LinearMap.id + s • (H : Space n →ₗ[ℝ] Space n) with hTdef
    have hd : (ContinuousLinearMap.id ℝ (Space n) + s • H).det = LinearMap.det T := rfl
    rw [hd, ← LinearMap.det_toMatrix b.toBasis]
    have hM : LinearMap.toMatrix b.toBasis b.toBasis T =
        Matrix.diagonal (fun j => 1 + s * hT.eigenvalues hn j) := by
      ext i j
      rw [LinearMap.toMatrix_apply]
      have : T (b.toBasis j) = (1 + s * hT.eigenvalues hn j) • b.toBasis j := by
        have e1 : T (b.toBasis j) = b.toBasis j + s • H (b.toBasis j) := rfl
        rw [e1, OrthonormalBasis.coe_toBasis, hev, smul_smul, add_smul, one_smul]
      rw [this, map_smul, Module.Basis.repr_self]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    rw [hM, Matrix.det_diagonal]

end CvxBody.NeedleLC
