module
public import CvxBody.Geometry.Rays
public import CvxBody.Analysis.LipschitzMaximizer

@[expose] public section


/-!
# Mass balance along transport rays (L10(b)-(e) of `docs/part1/P02-NEEDLE-BLUEPRINT.md`)

Klartag, *Needle decompositions in Riemannian geometry*, Lemmas 4.3-4.6, in `E = Space n`.
Let `μ` be a probability measure with finite first moment, `f` measurable with `|f| ≤ 1` and
`∫ f dμ = 0`, and `u` a 1-Lipschitz maximizer of `v ↦ ∫ v f dμ` (`IsLipschitzMaximizer`).

* `Loose u`, `Ends u`, `Strain u` partition `E` (`strain_union_loose_union_ends`); `Loose u`
  and `Ends u` are Borel (`measurableSet_loose`, `measurableSet_ends`), and `Ends u` is exactly the
  set of endpoints of maximal slope-one segments (`mem_ends_iff`).
* `IsTransportSet u A`: `A` contains the interior `strainRay u x` of the maximal ray through every
  strain point `x ∈ A`.
* L10(b) `setIntegral_eq_zero_of_isTransportSet`: `∫_A f dμ = 0` for null-measurable transport sets
  `A`, **assuming `μ (Ends u) = 0`** (the content of L9, proved elsewhere; here an explicit
  hypothesis `hEnds`).  Proof: the closed set `D = {g = u}` of points reachable from a compact
  `K ⊆ A \ Ends` along slope-one segments (`g = inf_{y ∈ K} (u y + ‖· - y‖)`) satisfies
  `K ⊆ D ⊆ A ∪ Ends`, `u_κ = min (u, g - κ)` is 1-Lipschitz, and
  `(u - u_κ)/κ → 1_D` boundedly, so maximality gives `∫_D f ≥ 0`.  The complement of a transport
  set is a transport set, which gives equality.
* L10(c) `measure_loose_eq_zero`, `measure_strain_eq_one` (using `f ≠ 0` everywhere).
* L10(d)-(e) `setIntegral_strain_preimage_eq_zero`: `∫_{Strain u ∩ rayInv u ⁻¹' B} f dμ = 0` for
  Borel `B ⊆ E × E`; (d) and (e) coincide because the ray invariant `rayInv u` takes values in
  `E × E`.
* `mass_balance_of_maximizer`, `exists_maximizer_mass_balance`: the packaged statements for
  `f = 1_S - μ(S)`.
-/

open OAI.LeanBlast.KLS MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace CvxBody.Geometry

variable {n : ℕ}

/-! ### Definitions -/

/-- `x` lies on a slope-one segment of positive length of `u`: there is `y ≠ x` with
`|u y - u x| = ‖y - x‖` (for `u` 1-Lipschitz this says `u` is affine of slope `±1` on `[x,y]`,
see `onSlopeOneSegment_iff`). -/
def OnSlopeOneSegment (u : Space n → ℝ) (x : Space n) : Prop :=
  ∃ y : Space n, y ≠ x ∧ |u y - u x| = ‖y - x‖

/-- Klartag's `Loose[u]`: the points whose only transport ray is the singleton `{x}`. -/
def Loose (u : Space n → ℝ) : Set (Space n) := {x | ¬ OnSlopeOneSegment u x}

/-- Klartag's `Ends[u]`: points of a nondegenerate transport ray that are not interior points
of it (those form `Strain u`). -/
def Ends (u : Space n → ℝ) : Set (Space n) := {x | x ∉ Strain u ∧ OnSlopeOneSegment u x}

/-- The interior part of the maximal transport ray through `x`: the strain points with the
same ray invariant. -/
def strainRay (u : Space n → ℝ) (x : Space n) : Set (Space n) :=
  {y | y ∈ Strain u ∧ rayInv u y = rayInv u x}

/-- A transport set: whenever it meets `Strain u` at `x` it contains the whole interior of the
maximal ray through `x`.  (Klartag's definition (17) also requires the endpoints of the ray; those
lie in `Ends u`, which is null.) -/
def IsTransportSet (u : Space n → ℝ) (A : Set (Space n)) : Prop :=
  ∀ x ∈ A ∩ Strain u, strainRay u x ⊆ A

/-- `u` is a maximizer of `v ↦ ∫ v f dμ` over the 1-Lipschitz functions (normalized by `u 0 = 0`),
the conclusion of `exists_lipschitz_maximizer`. -/
def IsLipschitzMaximizer (μ : Measure (Space n)) (f u : Space n → ℝ) : Prop :=
  LipschitzWith 1 u ∧ u 0 = 0 ∧
    ∀ v : Space n → ℝ, LipschitzWith 1 v → ∫ x, v x * f x ∂μ ≤ ∫ x, u x * f x ∂μ

/-! ### The infimum over a compact set -/

/-- `x ↦ inf_{y ∈ K} (u y + ‖x - y‖)`. -/
noncomputable def reachInf (u : Space n → ℝ) (K : Set (Space n)) (x : Space n) : ℝ :=
  ⨅ y : K, (u y + ‖x - (y : Space n)‖)

section Reach

variable {u : Space n → ℝ} {K : Set (Space n)}

lemma bddBelow_reach (hu : LipschitzWith 1 u) (x : Space n) :
    BddBelow (range fun y : K => u y + ‖x - (y : Space n)‖) := by
  refine ⟨u x, ?_⟩
  rintro _ ⟨y, rfl⟩
  have := hu.dist_le_mul x y
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul] at this
  linarith [(abs_le.mp this).2]

lemma le_reachInf (hu : LipschitzWith 1 u) (hK : K.Nonempty) (x : Space n) :
    u x ≤ reachInf u K x := by
  have : Nonempty K := hK.to_subtype
  refine le_ciInf fun y => ?_
  have := hu.dist_le_mul x y
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul] at this
  linarith [(abs_le.mp this).2]

lemma reachInf_le (hu : LipschitzWith 1 u) {y x : Space n} (hy : y ∈ K) :
    reachInf u K x ≤ u y + ‖x - y‖ :=
  ciInf_le (bddBelow_reach hu x) (⟨y, hy⟩ : K)

lemma lipschitzWith_reachInf (hu : LipschitzWith 1 u) (hK : K.Nonempty) :
    LipschitzWith 1 (reachInf u K) := by
  have : Nonempty K := hK.to_subtype
  have key : ∀ x x' : Space n, reachInf u K x ≤ reachInf u K x' + ‖x - x'‖ := by
    intro x x'
    have : reachInf u K x - ‖x - x'‖ ≤ reachInf u K x' := by
      refine le_ciInf fun y => ?_
      have h1 : reachInf u K x ≤ u y + ‖x - y‖ := reachInf_le hu y.2
      have h2 : ‖x - (y : Space n)‖ ≤ ‖x' - y‖ + ‖x - x'‖ := by
        calc ‖x - (y : Space n)‖ = ‖(x' - y) + (x - x')‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      linarith
    linarith
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul, abs_le]
  have h1 := key x x'
  have h2 := key x' x
  rw [norm_sub_rev] at h2
  constructor <;> linarith

lemma exists_reachInf_eq (hu : LipschitzWith 1 u) (hK : IsCompact K) (hne : K.Nonempty)
    (x : Space n) : ∃ y ∈ K, reachInf u K x = u y + ‖x - y‖ := by
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hne
    ((hu.continuous.add (continuous_const.sub continuous_id).norm).continuousOn
      : ContinuousOn (fun y : Space n => u y + ‖x - y‖) K)
  refine ⟨y, hy, le_antisymm (reachInf_le hu hy) ?_⟩
  have : Nonempty K := hne.to_subtype
  exact le_ciInf fun z => hmin z.2

lemma reachInf_eq_self_of_mem (hu : LipschitzWith 1 u) (hK : K.Nonempty) {y : Space n}
    (hy : y ∈ K) : reachInf u K y = u y :=
  le_antisymm (by simpa using reachInf_le hu (x := y) hy) (le_reachInf hu hK y)

end Reach


/-! ### Klartag's Lemmas 4.3-4.4: the perturbation argument -/

section Key

variable {μ : Measure (Space n)} [IsProbabilityMeasure μ] {f u : Space n → ℝ}

/-- The perturbation `u_κ = min (u, g - κ)` of a 1-Lipschitz function, where
`g = inf_{y ∈ K} (u y + ‖· - y‖) ≥ u`.  This equals Klartag's
`inf_y (u y + ‖x - y‖ - κ 1_K y)`. -/
lemma lipschitzWith_perturb (hu : LipschitzWith 1 u) {g : Space n → ℝ} (hg : LipschitzWith 1 g)
    (κ : ℝ) : LipschitzWith 1 fun x => min (u x) (g x - κ) := by
  have h : LipschitzWith 1 fun x => g x - κ := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simpa [Real.dist_eq] using hg.dist_le_mul x y
  simpa using hu.min h

/-- Integral of the perturbation increment: this is the maximality inequality (Lemma 4.4, (21)). -/
lemma nonneg_integral_perturb (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hfm : Measurable f)
    (hfb : ∀ x, |f x| ≤ 1) (hmax : IsLipschitzMaximizer μ f u) {g : Space n → ℝ}
    (hg : LipschitzWith 1 g) (hgu : ∀ x, u x ≤ g x) {κ : ℝ} (hκ : 0 < κ) :
    0 ≤ ∫ x, ((u x - min (u x) (g x - κ)) / κ) * f x ∂μ := by
  obtain ⟨hu, hu0, hmax⟩ := hmax
  have hbd : ∀ x, 0 ≤ u x - min (u x) (g x - κ) ∧ u x - min (u x) (g x - κ) ≤ κ := by
    intro x
    refine ⟨by simp, ?_⟩
    have := hgu x
    have : u x - κ ≤ min (u x) (g x - κ) := le_min (by linarith) (by linarith)
    linarith
  have hψc : Continuous fun x => u x - min (u x) (g x - κ) :=
    hu.continuous.sub (hu.continuous.min (hg.continuous.sub continuous_const))
  have hfi : Integrable f μ :=
    (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hfb x)
  have hψi : Integrable (fun x => (u x - min (u x) (g x - κ)) * f x) μ := by
    refine hfi.bdd_mul (c := κ) hψc.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hbd x).1]
    exact (hbd x).2
  have hui : Integrable (fun x => u x * f x) μ := integrable_lipschitz_mul μ hμ hfm hfb hu hu0
  have hmx := hmax _ (lipschitzWith_perturb hu hg κ)
  have hsub : ∫ x, (u x - min (u x) (g x - κ)) * f x ∂μ =
      ∫ x, u x * f x ∂μ - ∫ x, min (u x) (g x - κ) * f x ∂μ := by
    have hmi : Integrable (fun x => min (u x) (g x - κ) * f x) μ := by
      have := hui.sub hψi
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only [Pi.sub_apply]; ring
    rw [← integral_sub hui hmi]
    congr 1; ext x; ring
  have hnn : 0 ≤ ∫ x, (u x - min (u x) (g x - κ)) * f x ∂μ := by
    rw [hsub]; linarith
  have : ∫ x, ((u x - min (u x) (g x - κ)) / κ) * f x ∂μ =
      κ⁻¹ * ∫ x, (u x - min (u x) (g x - κ)) * f x ∂μ := by
    rw [← integral_const_mul]
    congr 1; ext x; ring
  rw [this]
  positivity


/-- Passage to the limit `κ → 0+` (Lemma 4.4, (22)-(23)): `∫_D f ≥ 0` for the closed set
`D = {g = u}` of points reachable from `K` along slope-one segments. -/
lemma nonneg_setIntegral_reach (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hfm : Measurable f)
    (hfb : ∀ x, |f x| ≤ 1) (hmax : IsLipschitzMaximizer μ f u) {g : Space n → ℝ}
    (hg : LipschitzWith 1 g) (hgu : ∀ x, u x ≤ g x) :
    0 ≤ ∫ x in {x | g x = u x}, f x ∂μ := by
  have hu := hmax.1
  set D : Set (Space n) := {x | g x = u x} with hD
  have hDc : IsClosed D := isClosed_eq hg.continuous hu.continuous
  set κ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hκdef
  have hκ : ∀ k, 0 < κ k := fun k => by simp only [hκdef]; positivity
  have hbd : ∀ (c : ℝ) x, 0 ≤ u x - min (u x) (g x - c) ∧ u x - min (u x) (g x - c) ≤ max c 0 := by
    intro c x
    refine ⟨by simp, ?_⟩
    have := hgu x
    have : u x - max c 0 ≤ min (u x) (g x - c) :=
      le_min (by linarith [le_max_right c 0]) (by linarith [le_max_left c 0])
    linarith
  have hlim : Tendsto (fun k => ∫ x, ((u x - min (u x) (g x - κ k)) / κ k) * f x ∂μ) atTop
      (𝓝 (∫ x, D.indicator f x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun k => ?_)
      (integrable_const _) (fun k => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · exact ((((hu.continuous.sub (hu.continuous.min
        (hg.continuous.sub continuous_const))).div_const _).measurable).mul
          hfm).aestronglyMeasurable
    · have h1 := hbd (κ k) x
      rw [max_eq_left (hκ k).le] at h1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg h1.1 (hκ k).le)]
      calc _ ≤ 1 * 1 := mul_le_mul ((div_le_one (hκ k)).mpr h1.2) (hfb x) (abs_nonneg _)
            zero_le_one
        _ = 1 := one_mul 1
    · by_cases hx : x ∈ D
      · have hgx : g x = u x := hx
        have : ∀ k, (u x - min (u x) (g x - κ k)) / κ k * f x = f x := by
          intro k
          rw [hgx, min_eq_right (by linarith [hκ k]),
            show u x - (u x - κ k) = κ k by ring, div_self (hκ k).ne', one_mul]
        simp only [this, indicator_of_mem hx]
        exact tendsto_const_nhds
      · have hgx : u x < g x := lt_of_le_of_ne (hgu x) (fun h => hx h.symm)
        have hev : ∀ᶠ k in atTop, κ k ≤ g x - u x := by
          have : Tendsto κ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
          exact this.eventually (Iic_mem_nhds (by linarith))
        rw [indicator_of_notMem hx]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with k hk
        rw [min_eq_left (by linarith)]
        simp
  have h0 := ge_of_tendsto' hlim fun k =>
    nonneg_integral_perturb hμ hfm hfb hmax hg hgu (hκ k)
  rwa [integral_indicator hDc.measurableSet] at h0


end Key

/-! ### Points reachable from `K` along slope-one segments -/

/-- Lemma 4.3, support part: a point joined to a point `y ∈ A \ Ends` by a slope-one segment lies
in `A ∪ Ends` when `A` is a transport set. -/
lemma mem_union_ends_of_slope {u : Space n → ℝ} (hu : LipschitzWith 1 u) {A : Set (Space n)}
    (hA : IsTransportSet u A) {x y : Space n} (hyA : y ∈ A) (hyE : y ∉ Ends u)
    (h : |u x - u y| = ‖x - y‖) : x ∈ A ∪ Ends u := by
  by_cases hxy : x = y
  · left; rwa [hxy]
  have hy_on : OnSlopeOneSegment u y := ⟨x, hxy, h⟩
  have hyS : y ∈ Strain u := by
    by_contra hn; exact hyE ⟨hn, hy_on⟩
  by_cases hxS : x ∈ Strain u
  · left
    exact hA y ⟨hyA, hyS⟩ ⟨hxS, (rayInv_eq_of_abs_sub_eq_dist hu hyS hxS h).symm⟩
  · right
    refine ⟨hxS, y, Ne.symm hxy, ?_⟩
    rw [abs_sub_comm, norm_sub_rev]; exact h

section Key2

variable {μ : Measure (Space n)} [IsProbabilityMeasure μ] {f u : Space n → ℝ}

/-- Klartag, Lemma 4.4 (core): for compact `K ⊆ A \ Ends` in a transport set `A` there is a closed
set `D`, `K ⊆ D ⊆ A ∪ Ends`, with `∫_D f ≥ 0`. -/
theorem exists_closed_nonneg_integral (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ 1) (hmax : IsLipschitzMaximizer μ f u)
    {A K : Set (Space n)} (hK : IsCompact K) (hKA : K ⊆ A) (hKE : Disjoint K (Ends u))
    (hA : IsTransportSet u A) :
    ∃ D : Set (Space n), IsClosed D ∧ K ⊆ D ∧ D ⊆ A ∪ Ends u ∧ 0 ≤ ∫ x in D, f x ∂μ := by
  have hu := hmax.1
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, isClosed_empty, subset_rfl, empty_subset _, by simp⟩
  have hglip := lipschitzWith_reachInf hu hne
  have hgu : ∀ x, u x ≤ reachInf u K x := le_reachInf hu hne
  refine ⟨{x | reachInf u K x = u x}, isClosed_eq hglip.continuous hu.continuous, ?_, ?_,
    nonneg_setIntegral_reach hμ hfm hfb hmax hglip hgu⟩
  · intro y hy
    exact reachInf_eq_self_of_mem hu hne hy
  · intro x hx
    obtain ⟨y, hyK, hy⟩ := exists_reachInf_eq hu hK hne x
    have hx' : reachInf u K x = u x := hx
    have h1 : u x = u y + ‖x - y‖ := by rw [← hx', hy]
    refine mem_union_ends_of_slope hu hA (hKA hyK) (fun hE => ?_) ?_
    · exact Set.disjoint_left.mp hKE hyK hE
    · rw [abs_of_nonneg (by linarith [norm_nonneg (x - y)])]
      linarith


lemma abs_setIntegral_le (hfb : ∀ x, |f x| ≤ 1) (s : Set (Space n)) :
    |∫ x in s, f x ∂μ| ≤ μ.real s := by
  have := norm_setIntegral_le_of_norm_le_const (μ := μ) (f := f) (s := s) (C := 1)
    (measure_lt_top μ s) (fun x _ => by simpa [Real.norm_eq_abs] using hfb x)
  simpa [Real.norm_eq_abs] using this

/-- **Klartag, Lemma 4.4, one inequality.** If `μ (Ends u) = 0`, then `∫_A f dμ ≥ 0` for every
null-measurable transport set `A`. -/
theorem setIntegral_nonneg_of_isTransportSet (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ 1) (hmax : IsLipschitzMaximizer μ f u)
    (hEnds : μ (Ends u) = 0) {A : Set (Space n)} (hA : IsTransportSet u A)
    (hAm : NullMeasurableSet A μ) : 0 ≤ ∫ x in A, f x ∂μ := by
  have hfi : Integrable f μ :=
    (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hfb x)
  obtain ⟨B, hBA, hBm, hBae⟩ := hAm.exists_measurable_subset_ae_eq
  obtain ⟨N, hEN, hNm, hN0⟩ := exists_measurable_superset_of_null hEnds
  rw [← setIntegral_congr_set hBae]
  by_contra hneg
  push Not at hneg
  set ε : ℝ := -(∫ x in B, f x ∂μ) / 3 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨K, hKBN, hKc, hKlt⟩ := (hBm.diff hNm).exists_isCompact_lt_add (measure_ne_top μ _)
    (ENNReal.ofReal_pos.mpr hεpos).ne'
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hKB : K ⊆ B := fun x hx => (hKBN hx).1
  have hKE : Disjoint K (Ends u) := by
    refine Set.disjoint_left.mpr fun x hxK hxE => (hKBN hxK).2 (hEN hxE)
  -- the small measure of `B \ K`
  have hBK : μ.real (B \ K) ≤ ε := by
    have h1 : μ (B \ K) ≤ μ ((B \ N) \ K) + μ N := by
      refine (measure_mono ?_).trans (measure_union_le _ _)
      intro x hx
      by_cases hxN : x ∈ N
      · exact Or.inr hxN
      · exact Or.inl ⟨⟨hx.1, hxN⟩, hx.2⟩
    rw [hN0, add_zero, measure_sdiff hKBN hKm.nullMeasurableSet (measure_ne_top μ _)] at h1
    have h2 : μ (B \ N) - μ K ≤ ENNReal.ofReal ε := by
      rw [tsub_le_iff_left]; exact hKlt.le.trans (by rw [add_comm])
    exact ENNReal.toReal_le_of_le_ofReal hεpos.le (h1.trans h2)
  obtain ⟨D, hDc, hKD, hDA, hD0⟩ :=
    exists_closed_nonneg_integral hμ hfm hfb hmax hKc (hKB.trans hBA) hKE hA
  have hDm := hDc.measurableSet
  -- `D \ K` is also small
  have hAB : μ (A \ B) = 0 := (ae_eq_set.mp hBae).2
  have hDK : μ.real (D \ K) ≤ ε := by
    refine le_trans ?_ hBK
    have h1 : μ (D \ K) ≤ μ (B \ K) + (μ (A \ B) + μ (Ends u)) := by
      have hsub : D \ K ⊆ (B \ K) ∪ ((A \ B) ∪ Ends u) := by
        intro x hx
        rcases hDA hx.1 with hxA | hxE
        · by_cases hxB : x ∈ B
          · exact Or.inl ⟨hxB, hx.2⟩
          · exact Or.inr (Or.inl ⟨hxA, hxB⟩)
        · exact Or.inr (Or.inr hxE)
      exact (measure_mono hsub).trans ((measure_union_le _ _).trans
        (add_le_add_right (measure_union_le _ _) _) |>.trans_eq (by ring))
    rw [hAB, hEnds, add_zero, add_zero] at h1
    exact ENNReal.toReal_mono (measure_ne_top μ _) h1
  have hDint := hfi.integrableOn (s := D)
  have hBint := hfi.integrableOn (s := B)
  have e1 := setIntegral_sdiff hKm hDint hKD
  have e2 := setIntegral_sdiff hKm hBint hKB
  have a1 := abs_setIntegral_le (μ := μ) hfb (D \ K)
  have a2 := abs_setIntegral_le (μ := μ) hfb (B \ K)
  rw [abs_le] at a1 a2
  rw [hε] at hDK hBK
  linarith [a1.1, a1.2, a2.1, a2.2]


end Key2

theorem IsTransportSet.compl {u : Space n → ℝ} {A : Set (Space n)} (hA : IsTransportSet u A) :
    IsTransportSet u Aᶜ := by
  rintro x ⟨hxA, hxS⟩ y ⟨hyS, hy⟩
  by_contra hyA
  have hyA' : y ∈ A := by simpa using hyA
  exact hxA (hA y ⟨hyA', hyS⟩ ⟨hxS, hy.symm⟩)

section Main

variable {μ : Measure (Space n)} [IsProbabilityMeasure μ] {f u : Space n → ℝ}

/-- **Klartag, Lemmas 4.3-4.5 (mass balance on transport sets).**
Let `μ` be a probability measure with finite first moment, `f` measurable with `|f| ≤ 1` and
`∫ f dμ = 0`, and `u` a Lipschitz maximizer.  If `μ (Ends u) = 0` (the content of L9) then
`∫_A f dμ = 0` for every null-measurable transport set `A`. -/
theorem setIntegral_eq_zero_of_isTransportSet (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ 1) (hf0 : ∫ x, f x ∂μ = 0)
    (hmax : IsLipschitzMaximizer μ f u) (hEnds : μ (Ends u) = 0) {A : Set (Space n)}
    (hA : IsTransportSet u A) (hAm : NullMeasurableSet A μ) : ∫ x in A, f x ∂μ = 0 := by
  have hfi : Integrable f μ :=
    (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hfb x)
  have h1 := setIntegral_nonneg_of_isTransportSet hμ hfm hfb hmax hEnds hA hAm
  have h2 := setIntegral_nonneg_of_isTransportSet hμ hfm hfb hmax hEnds hA.compl hAm.compl
  have h3 := integral_add_compl₀ hAm hfi
  linarith


end Main

/-! ### The partition `Space n = Strain u ⊔ Loose u ⊔ Ends u`, and measurability -/

lemma disjoint_strain_ends (u : Space n → ℝ) : Disjoint (Strain u) (Ends u) :=
  Set.disjoint_left.mpr fun _ hS hE => hE.1 hS

lemma onSlopeOneSegment_of_mem_strain {u : Space n → ℝ} {x : Space n} (hx : x ∈ Strain u) :
    OnSlopeOneSegment u x := by
  obtain ⟨ε, hε, θ, hθ, h⟩ := mem_strain_iff.mp hx
  refine ⟨x + ε • θ, ?_, ?_⟩
  · intro hxe
    have h1 : ε • θ = 0 := by
      have := congrArg (fun z => z - x) hxe
      simpa using this
    have h2 : ‖ε • θ‖ = ε := by
      rw [norm_smul, hθ, Real.norm_eq_abs, abs_of_pos hε, mul_one]
    rw [h1, norm_zero] at h2
    linarith
  · rw [h ε (by rw [abs_of_pos hε]), show u x + ε - u x = ε by ring, add_sub_cancel_left,
      norm_smul, hθ, Real.norm_eq_abs, abs_of_pos hε]
    simp

theorem disjoint_strain_loose (u : Space n → ℝ) : Disjoint (Strain u) (Loose u) :=
  Set.disjoint_left.mpr fun _ hS hL => hL (onSlopeOneSegment_of_mem_strain hS)

theorem disjoint_loose_ends (u : Space n → ℝ) : Disjoint (Loose u) (Ends u) :=
  Set.disjoint_left.mpr fun _ hL hE => hL hE.2

/-- Every point is a strain point, a loose point, or an end point. -/
theorem strain_union_loose_union_ends (u : Space n → ℝ) :
    Strain u ∪ Loose u ∪ Ends u = univ := by
  ext x
  simp only [mem_union, mem_univ, iff_true, Loose, Ends, mem_ofPred_eq]
  by_cases h1 : x ∈ Strain u
  · exact Or.inl (Or.inl h1)
  · by_cases h2 : OnSlopeOneSegment u x
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl (Or.inr h2)

/-- Along a slope-one segment `[x, y]` the increments of `u` are proportional to the distance. -/
lemma abs_sub_segment {u : Space n → ℝ} (hu : LipschitzWith 1 u) {x y : Space n}
    (hxy : |u y - u x| = ‖y - x‖) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |u (x + t • (y - x)) - u x| = t * ‖y - x‖ := by
  set s : ℝ := ‖y - x‖ with hs
  set z : Space n := x + t • (y - x) with hz
  have d1 : ‖z - x‖ = t * s := by
    rw [hz, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  have d2 : ‖y - z‖ = (1 - t) * s := by
    have : y - z = (1 - t) • (y - x) := by rw [hz, sub_smul, one_smul]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have a1 := hu.dist_le_mul z x
  have a2 := hu.dist_le_mul y z
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul, d1] at a1
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul, d2] at a2
  have a3 : |u y - u x| ≤ |u y - u z| + |u z - u x| := by
    calc |u y - u x| = |(u y - u z) + (u z - u x)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  rw [hxy] at a3
  have hs0 : 0 ≤ s := norm_nonneg _
  have : t * s ≤ |u z - u x| := by nlinarith
  exact le_antisymm a1 this

/-- Restriction of a slope-one segment to a shorter initial piece. -/
lemma exists_slope_at_dist {u : Space n → ℝ} (hu : LipschitzWith 1 u) {x y : Space n}
    (hxy : |u y - u x| = ‖y - x‖) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ ‖y - x‖) :
    ∃ e : Space n, ‖e‖ = δ ∧ |u (x + e) - u x| = δ := by
  have hspos : 0 < ‖y - x‖ := lt_of_lt_of_le hδ0 hδ
  have ht0 : 0 < δ / ‖y - x‖ := div_pos hδ0 hspos
  have ht1 : δ / ‖y - x‖ ≤ 1 := (div_le_one hspos).mpr hδ
  have hts : δ / ‖y - x‖ * ‖y - x‖ = δ := div_mul_cancel₀ δ hspos.ne'
  refine ⟨(δ / ‖y - x‖) • (y - x), ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, hts]
  · rw [abs_sub_segment hu hxy ht0.le ht1, hts]

theorem isClosed_slopeAt {u : Space n → ℝ} (hu : LipschitzWith 1 u) (δ : ℝ) :
    IsClosed {x : Space n | ∃ e : Space n, ‖e‖ = δ ∧ |u (x + e) - u x| = δ} := by
  set C : Set (Space n × Metric.sphere (0 : Space n) δ) :=
    {p | |u (p.1 + (p.2 : Space n)) - u p.1| = δ} with hC
  have hcont := hu.continuous
  have hCc : IsClosed C := by
    refine isClosed_eq ?_ continuous_const
    exact ((hcont.comp (continuous_fst.add (continuous_subtype_val.comp continuous_snd))).sub
      (hcont.comp continuous_fst)).abs
  have himg : {x : Space n | ∃ e : Space n, ‖e‖ = δ ∧ |u (x + e) - u x| = δ} =
      Prod.fst '' C := by
    ext x
    constructor
    · rintro ⟨e, he, h⟩
      exact ⟨(x, ⟨e, by simpa using he⟩), h, rfl⟩
    · rintro ⟨⟨y, e⟩, hp, rfl⟩
      exact ⟨e, by simp, hp⟩
  rw [himg]
  exact isClosedMap_fst_of_compactSpace _ hCc

theorem onSlopeOneSegment_iff_exists {u : Space n → ℝ} (hu : LipschitzWith 1 u) (x : Space n) :
    OnSlopeOneSegment u x ↔ ∃ m : ℕ, ∃ e : Space n, ‖e‖ = 1 / ((m : ℝ) + 1) ∧
      |u (x + e) - u x| = 1 / ((m : ℝ) + 1) := by
  constructor
  · rintro ⟨y, hyx, h⟩
    have hs : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hs
    obtain ⟨e, he, h'⟩ := exists_slope_at_dist hu h (δ := 1 / ((m : ℝ) + 1)) (by positivity)
      hm.le
    exact ⟨m, e, he, h'⟩
  · rintro ⟨m, e, he, h⟩
    have hpos : 0 < 1 / ((m : ℝ) + 1) := by positivity
    refine ⟨x + e, ?_, ?_⟩
    · intro hxe
      have h1 : e = 0 := by simpa using congrArg (fun z => z - x) hxe
      rw [h1, norm_zero] at he
      linarith
    · rw [h, add_sub_cancel_left, he]

theorem measurableSet_onSlopeOneSegment {u : Space n → ℝ} (hu : LipschitzWith 1 u) :
    MeasurableSet {x | OnSlopeOneSegment u x} := by
  have : {x | OnSlopeOneSegment u x} = ⋃ m : ℕ, {x : Space n | ∃ e : Space n,
      ‖e‖ = 1 / ((m : ℝ) + 1) ∧ |u (x + e) - u x| = 1 / ((m : ℝ) + 1)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    exact onSlopeOneSegment_iff_exists hu x
  rw [this]
  exact MeasurableSet.iUnion fun m => (isClosed_slopeAt hu _).measurableSet

theorem measurableSet_loose {u : Space n → ℝ} (hu : LipschitzWith 1 u) :
    MeasurableSet (Loose u) :=
  (measurableSet_onSlopeOneSegment hu).compl

theorem measurableSet_ends {u : Space n → ℝ} (hu : LipschitzWith 1 u) :
    MeasurableSet (Ends u) :=
  (measurableSet_strain hu).compl.inter (measurableSet_onSlopeOneSegment hu)


/-! ### Consequences: (c) loose points, (d)-(e) saturated sets -/

section Consequences

variable {μ : Measure (Space n)} [IsProbabilityMeasure μ] {f u : Space n → ℝ}

omit [IsProbabilityMeasure μ] in
lemma measure_eq_zero_of_setIntegral_eq_zero {g : Space n → ℝ} (hgi : Integrable g μ)
    {T : Set (Space n)} (hT : MeasurableSet T) (hpos : ∀ x ∈ T, 0 < g x)
    (h0 : ∫ x in T, g x ∂μ = 0) : μ T = 0 := by
  have h1 : g =ᵐ[μ.restrict T] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae
      ((ae_restrict_iff' hT).mpr (ae_of_all _ fun x hx => (hpos x hx).le))
      hgi.integrableOn).mp h0
  have h2 := (ae_restrict_iff' hT).mp h1
  refine measure_eq_zero_iff_ae_notMem.mpr ?_
  filter_upwards [h2] with x hx hxT
  have := hx hxT
  have := hpos x hxT
  simp_all

/-- **Klartag, Section 4 (c): `μ (Loose u) = 0`.**  Here `f ≠ 0` everywhere replaces Klartag's
"`f = 0` a.e. off `Strain u`".  Every measurable subset of `Loose u` is a transport set
(vacuously, since `Loose u ∩ Strain u = ∅`). -/
theorem measure_loose_eq_zero (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hfm : Measurable f)
    (hfb : ∀ x, |f x| ≤ 1) (hf0 : ∫ x, f x ∂μ = 0) (hmax : IsLipschitzMaximizer μ f u)
    (hEnds : μ (Ends u) = 0) (hf : ∀ x, f x ≠ 0) : μ (Loose u) = 0 := by
  have hu := hmax.1
  have hfi : Integrable f μ :=
    (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hfb x)
  have hvac : ∀ T : Set (Space n), T ⊆ Loose u → IsTransportSet u T := by
    intro T hT x hx
    exact absurd (onSlopeOneSegment_of_mem_strain hx.2) (hT hx.1)
  have hL := measurableSet_loose hu
  have key : ∀ T : Set (Space n), MeasurableSet T → T ⊆ Loose u →
      ∫ x in T, f x ∂μ = 0 := fun T hT hTL =>
    setIntegral_eq_zero_of_isTransportSet hμ hfm hfb hf0 hmax hEnds (hvac T hTL)
      hT.nullMeasurableSet
  have hpos : μ (Loose u ∩ {x | 0 < f x}) = 0 :=
    measure_eq_zero_of_setIntegral_eq_zero hfi (hL.inter (measurableSet_lt measurable_const hfm))
      (fun x hx => hx.2) (key _ (hL.inter (measurableSet_lt measurable_const hfm))
        inter_subset_left)
  have hneg : μ (Loose u ∩ {x | f x < 0}) = 0 := by
    have hm : MeasurableSet (Loose u ∩ {x | f x < 0}) :=
      hL.inter (measurableSet_lt hfm measurable_const)
    refine measure_eq_zero_of_setIntegral_eq_zero (g := fun x => -f x) hfi.neg hm
      (fun x hx => by simpa using hx.2) ?_
    rw [integral_neg, key _ hm inter_subset_left, neg_zero]
  refine measure_mono_null (fun x hx => ?_) (measure_union_null hpos hneg)
  rcases lt_or_gt_of_ne (hf x) with h | h
  · exact Or.inr ⟨hx, h⟩
  · exact Or.inl ⟨hx, h⟩

/-- `μ (Strain u) = 1` once the loose points and the ends are null. -/
theorem measure_strain_eq_one (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hfm : Measurable f)
    (hfb : ∀ x, |f x| ≤ 1) (hf0 : ∫ x, f x ∂μ = 0) (hmax : IsLipschitzMaximizer μ f u)
    (hEnds : μ (Ends u) = 0) (hf : ∀ x, f x ≠ 0) : μ (Strain u) = 1 := by
  have hL := measure_loose_eq_zero hμ hfm hfb hf0 hmax hEnds hf
  have h1 : μ (Strain u ∪ Loose u ∪ Ends u) = 1 := by
    rw [strain_union_loose_union_ends, measure_univ]
  have h2 : μ (Strain u ∪ Loose u ∪ Ends u) ≤ μ (Strain u) + μ (Loose u) + μ (Ends u) :=
    (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
  rw [hL, hEnds, add_zero, add_zero, h1] at h2
  exact le_antisymm prob_le_one h2


/-- **Klartag, Lemma 4.6 / L10(d)-(e).** For every Borel set `B` of the ray-invariant space
`Space n × Space n`, the saturated set `{x ∈ Strain u | rayInv u x ∈ B}` is a transport set
and carries zero `f`-mass.  (No separate treatment of ray closures is needed: the endpoints of the
rays lie in `Ends u`, which is null.) -/
theorem setIntegral_strain_preimage_eq_zero (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ 1) (hf0 : ∫ x, f x ∂μ = 0)
    (hmax : IsLipschitzMaximizer μ f u) (hEnds : μ (Ends u) = 0)
    {B : Set (Space n × Space n)} (hB : MeasurableSet B) :
    ∫ x in Strain u ∩ rayInv u ⁻¹' B, f x ∂μ = 0 := by
  have hu := hmax.1
  refine setIntegral_eq_zero_of_isTransportSet hμ hfm hfb hf0 hmax hEnds ?_
    ((measurableSet_strain hu).inter ((measurable_rayInv hu) hB)).nullMeasurableSet
  rintro x ⟨⟨_, hxB⟩, _⟩ y ⟨hyS, hy⟩
  exact ⟨hyS, by simpa [mem_preimage, hy] using hxB⟩

/-- The saturated-set formulation of (d): a measurable `A` such that every strain point on the
ray of a point of `A` lies in `A` (for instance a saturated Borel subset of `Strain u`). -/
theorem setIntegral_eq_zero_of_saturated (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ 1) (hf0 : ∫ x, f x ∂μ = 0)
    (hmax : IsLipschitzMaximizer μ f u) (hEnds : μ (Ends u) = 0) {A : Set (Space n)}
    (hAm : MeasurableSet A)
    (hsat : ∀ x ∈ A, ∀ y ∈ Strain u, rayInv u y = rayInv u x → y ∈ A) :
    ∫ x in A, f x ∂μ = 0 :=
  setIntegral_eq_zero_of_isTransportSet hμ hfm hfb hf0 hmax hEnds
    (fun x hx _ hy => hsat x hx.1 _ hy.1 hy.2) hAm.nullMeasurableSet


end Consequences

/-! ### Sanity checks on the definitions -/

/-- `OnSlopeOneSegment` is the statement that `u` is affine of slope `±1` along a segment of
positive length with endpoint `x`. -/
theorem onSlopeOneSegment_iff_segment {u : Space n → ℝ} (hu : LipschitzWith 1 u) (x : Space n) :
    OnSlopeOneSegment u x ↔ ∃ e : Space n, ‖e‖ = 1 ∧ ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ ∃ s : ℝ,
      0 < s ∧ ∀ t : ℝ, 0 ≤ t → t ≤ s → u (x + t • e) = u x + c * t := by
  constructor
  · rintro ⟨y, hyx, h⟩
    have hs : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
    set s : ℝ := ‖y - x‖ with hsdef
    have hye : x + s • (s⁻¹ • (y - x)) = y := by
      rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]; abel
    have hsy : y - x = s • (s⁻¹ • (y - x)) := by
      rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    refine ⟨s⁻¹ • (y - x), ?_, ?_⟩
    · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hs]
      exact inv_mul_cancel₀ hs.ne'
    have hyx' : |u x - u y| = ‖x - y‖ := by rw [abs_sub_comm, norm_sub_rev]; exact h
    have key : ∀ t : ℝ, 0 ≤ t → t ≤ s →
        |u (x + t • (s⁻¹ • (y - x))) - u x| = t ∧
          |u (x + t • (s⁻¹ • (y - x))) - u y| = s - t := by
      intro t ht0 hts
      have hτ0 : 0 ≤ t / s := div_nonneg ht0 hs.le
      have hτ1 : t / s ≤ 1 := (div_le_one hs).mpr hts
      have e1 : x + t • (s⁻¹ • (y - x)) = x + (t / s) • (y - x) := by
        rw [smul_smul, div_eq_mul_inv]
      have e2 : x + t • (s⁻¹ • (y - x)) = y + (1 - t / s) • (x - y) := by
        rw [e1, sub_smul, one_smul, smul_sub, smul_sub]; abel
      refine ⟨?_, ?_⟩
      · rw [e1, abs_sub_segment hu h hτ0 hτ1, div_mul_cancel₀ _ hs.ne']
      · rw [e2, abs_sub_segment hu hyx' (by linarith) (by linarith), norm_sub_rev, ← hsdef]
        field_simp
    rcases abs_cases (u y - u x) with ⟨hc, _⟩ | ⟨hc, _⟩
    · refine ⟨1, Or.inl rfl, s, hs, fun t ht0 hts => ?_⟩
      have h1 : u y - u x = s := by rw [← h]; exact hc.symm
      obtain ⟨k1, k2⟩ := key t ht0 hts
      have := abs_le.mp k1.le
      have := abs_le.mp k2.le
      linarith [this.1, this.2]
    · refine ⟨-1, Or.inr rfl, s, hs, fun t ht0 hts => ?_⟩
      have h1 : u y - u x = -s := by linarith
      obtain ⟨k1, k2⟩ := key t ht0 hts
      have a1 := abs_le.mp k1.le
      have a2 := abs_le.mp k2.le
      linarith [a1.1, a1.2, a2.1, a2.2]
  · rintro ⟨e, he, c, hc, s, hs, h⟩
    refine ⟨x + s • e, ?_, ?_⟩
    · intro hxe
      have h1 : s • e = 0 := by simpa using congrArg (fun z => z - x) hxe
      rw [smul_eq_zero] at h1
      rcases h1 with h1 | h1
      · linarith
      · rw [h1, norm_zero] at he; exact zero_ne_one he
    · have hn : ‖x + s • e - x‖ = s := by
        rw [add_sub_cancel_left, norm_smul, he, Real.norm_eq_abs, abs_of_pos hs, mul_one]
      rw [h s hs.le le_rfl, hn, show u x + c * s - u x = c * s by ring, abs_mul]
      rcases hc with rfl | rfl <;> simp [abs_of_pos hs]

/-- Klartag's definition (17) of a transport set asks that `A` contain every transport ray meeting
`A \ Ends u`.  Any set closed under slope-one pairs started at non-end points is a transport set in
the sense of `IsTransportSet` (which is the weaker requirement). -/
theorem isTransportSet_of_forall_slope {u : Space n → ℝ} {A : Set (Space n)}
    (h : ∀ x ∈ A, x ∉ Ends u → ∀ y : Space n, |u y - u x| = ‖y - x‖ → y ∈ A) :
    IsTransportSet u A := by
  rintro x ⟨hxA, hxS⟩ y ⟨-, hy⟩
  refine h x hxA (fun hE => hE.1 hxS) y ?_
  have h1 := eq_add_sub_smul_of_rayInv_eq hy.symm
  have h2 : y - x = (u y - u x) • strainDir u x := sub_eq_of_eq_add' h1
  rw [h2, norm_smul, norm_strainDir hxS, mul_one, Real.norm_eq_abs]

/-! ### The function `f = 1_S - μ(S)` and the packaged mass-balance statement -/

/-- `f = 1_S - μ(S)`. -/
noncomputable def massBalanceFn (μ : Measure (Space n)) (S : Set (Space n)) : Space n → ℝ :=
  fun x => S.indicator (fun _ => (1 : ℝ)) x - μ.real S

section Package

variable {μ : Measure (Space n)} [IsProbabilityMeasure μ] {S : Set (Space n)}

lemma real_pos_lt_one (h0 : 0 < μ S) (h1 : μ S < 1) : 0 < μ.real S ∧ μ.real S < 1 := by
  refine ⟨ENNReal.toReal_pos h0.ne' (measure_ne_top μ S), ?_⟩
  have := ENNReal.toReal_strict_mono ENNReal.one_ne_top h1
  rwa [ENNReal.toReal_one] at this

omit [IsProbabilityMeasure μ] in
lemma measurable_massBalanceFn (hS : MeasurableSet S) : Measurable (massBalanceFn μ S) :=
  (measurable_const.indicator hS).sub measurable_const

lemma massBalanceFn_bound (h0 : 0 < μ S) (h1 : μ S < 1) (x : Space n) :
    |massBalanceFn μ S x| ≤ 1 := by
  obtain ⟨a0, a1⟩ := real_pos_lt_one h0 h1
  by_cases hx : x ∈ S
  · simp only [massBalanceFn, indicator_of_mem hx]
    rw [abs_le]; constructor <;> linarith
  · simp only [massBalanceFn, indicator_of_notMem hx]
    rw [abs_le]; constructor <;> linarith

lemma massBalanceFn_ne_zero (h0 : 0 < μ S) (h1 : μ S < 1) (x : Space n) :
    massBalanceFn μ S x ≠ 0 := by
  obtain ⟨a0, a1⟩ := real_pos_lt_one h0 h1
  by_cases hx : x ∈ S
  · simp only [massBalanceFn, indicator_of_mem hx]; intro h; linarith
  · simp only [massBalanceFn, indicator_of_notMem hx]; intro h; linarith

lemma integral_massBalanceFn (hS : MeasurableSet S) : ∫ x, massBalanceFn μ S x ∂μ = 0 := by
  have : ∫ x, S.indicator (fun _ => (1 : ℝ)) x ∂μ = μ.real S := integral_indicator_one hS
  unfold massBalanceFn
  rw [integral_sub ((integrable_const (1 : ℝ)).indicator hS) (integrable_const _), this]
  simp

/-- **L10(c)-(e) for `f = 1_S - μ(S)`.**  Let `μ` be a probability measure with finite first moment,
`S` measurable with `0 < μ S < 1`, and `u` a Lipschitz maximizer of `v ↦ ∫ v f dμ`.  If the ends of
the transport rays of `u` are `μ`-null (L9, here an explicit hypothesis), then the loose points are
null, `Strain u` has full measure, and every ray-invariant Borel set carries zero `f`-mass. -/
theorem mass_balance_of_maximizer (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hS : MeasurableSet S) (h0 : 0 < μ S) (h1 : μ S < 1) {u : Space n → ℝ}
    (hmax : IsLipschitzMaximizer μ (massBalanceFn μ S) u) (hEnds : μ (Ends u) = 0) :
    μ (Loose u) = 0 ∧ μ (Strain u) = 1 ∧ ∀ B : Set (Space n × Space n), MeasurableSet B →
      ∫ x in Strain u ∩ rayInv u ⁻¹' B, massBalanceFn μ S x ∂μ = 0 := by
  have hfm := measurable_massBalanceFn (μ := μ) hS
  have hfb := massBalanceFn_bound h0 h1
  have hf0 := integral_massBalanceFn (μ := μ) hS
  have hf := massBalanceFn_ne_zero h0 h1
  exact ⟨measure_loose_eq_zero hμ hfm hfb hf0 hmax hEnds hf,
    measure_strain_eq_one hμ hfm hfb hf0 hmax hEnds hf,
    fun B hB => setIntegral_strain_preimage_eq_zero hμ hfm hfb hf0 hmax hEnds hB⟩

/-- Existence of a maximizer (Klartag, Lemma 4.1) together with the mass balance, under the
hypothesis that the maximizer has null ends. -/
theorem exists_maximizer_mass_balance (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hS : MeasurableSet S) (h0 : 0 < μ S) (h1 : μ S < 1)
    (hEnds : ∀ u : Space n → ℝ, IsLipschitzMaximizer μ (massBalanceFn μ S) u →
      μ (Ends u) = 0) :
    ∃ u : Space n → ℝ, IsLipschitzMaximizer μ (massBalanceFn μ S) u ∧
      μ (Loose u) = 0 ∧ μ (Strain u) = 1 ∧ ∀ B : Set (Space n × Space n), MeasurableSet B →
        ∫ x in Strain u ∩ rayInv u ⁻¹' B, massBalanceFn μ S x ∂μ = 0 := by
  obtain ⟨u, hu, hu0, hmax⟩ := _root_.exists_lipschitz_maximizer μ hμ
    (measurable_massBalanceFn hS) (massBalanceFn_bound h0 h1) (integral_massBalanceFn hS)
  have hm : IsLipschitzMaximizer μ (massBalanceFn μ S) u := ⟨hu, hu0, hmax⟩
  exact ⟨u, hm, mass_balance_of_maximizer hμ hS h0 h1 hm (hEnds u hm)⟩

end Package

/-! ### `Ends u` is the set of endpoints of the maximal slope-one segments -/

theorem isClosed_raySlopeTimes {u : Space n → ℝ} (hu : LipschitzWith 1 u) (q : Space n × Space n) :
    IsClosed (raySlopeTimes u q) :=
  isClosed_eq (hu.continuous.comp (continuous_const.add (continuous_id.smul continuous_const)))
    continuous_id

/-- A finite value of `rayLo` or `rayHi` at a strain point is attained (the set of slope-one
parameters is closed). -/
theorem mem_raySlopeTimes_of_rayLo_eq {u : Space n → ℝ} (hu : LipschitzWith 1 u) {z : Space n}
    {τ : ℝ} (h : rayLo u z = τ) : τ ∈ raySlopeTimes u (rayInv u z) := by
  refine (isClosed_raySlopeTimes hu _).closure_subset_iff.mpr subset_rfl ?_
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hlt : rayLo u z < ((τ + ε : ℝ) : EReal) := by
    rw [h]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨_, ⟨a, ha, rfl⟩, hlt'⟩ := sInf_lt_iff.mp hlt
  have h1 : (τ : EReal) ≤ a := by
    rw [← h]; exact sInf_le (mem_image_of_mem _ ha)
  have h1' := EReal.coe_le_coe_iff.mp h1
  have h2 := EReal.coe_lt_coe_iff.mp hlt'
  exact ⟨a, ha, by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith⟩

theorem mem_raySlopeTimes_of_rayHi_eq {u : Space n → ℝ} (hu : LipschitzWith 1 u) {z : Space n}
    {τ : ℝ} (h : rayHi u z = τ) : τ ∈ raySlopeTimes u (rayInv u z) := by
  refine (isClosed_raySlopeTimes hu _).closure_subset_iff.mpr subset_rfl ?_
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hlt : ((τ - ε : ℝ) : EReal) < rayHi u z := by
    rw [h]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨_, ⟨a, ha, rfl⟩, hlt'⟩ := lt_sSup_iff.mp hlt
  have h1 : (a : EReal) ≤ τ := by
    rw [← h]; exact le_sSup (mem_image_of_mem _ ha)
  have h1' := EReal.coe_le_coe_iff.mp h1
  have h2 := EReal.coe_lt_coe_iff.mp hlt'
  exact ⟨a, ha, by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith⟩

/-- An interior parameter of the maximal ray through a strain point `z` is a strain point. -/
theorem mem_strain_of_lt_lt {u : Space n → ℝ} (hu : LipschitzWith 1 u) {z : Space n}
    (hz : z ∈ Strain u) {τ : ℝ} (h1 : rayLo u z < τ) (h2 : (τ : EReal) < rayHi u z) :
    z + (τ - u z) • strainDir u z ∈ Strain u := by
  obtain ⟨a, ha1, ha2⟩ := EReal.lt_iff_exists_real_btwn.mp h1
  obtain ⟨b, hb1, hb2⟩ := EReal.lt_iff_exists_real_btwn.mp h2
  have ha2' := EReal.coe_lt_coe_iff.mp ha2
  have hb1' := EReal.coe_lt_coe_iff.mp hb1
  refine mem_strain_iff.mpr ⟨min (τ - a) (b - τ), lt_min (by linarith) (by linarith),
    strainDir u z, norm_strainDir hz, fun t ht => ?_⟩
  have hτ : u (z + (τ - u z) • strainDir u z) = τ :=
    mem_raySlopeTimes_rayInv.mp (mem_raySlopeTimes_of_lt_of_lt hu hz h1 h2)
  have ht1 : t ≤ min (τ - a) (b - τ) := (le_abs_self t).trans ht
  have ht2 : -t ≤ min (τ - a) (b - τ) := (neg_le_abs t).trans ht
  have hm1 := min_le_left (τ - a) (b - τ)
  have hm2 := min_le_right (τ - a) (b - τ)
  have hσ : u (z + (τ + t - u z) • strainDir u z) = τ + t := by
    refine mem_raySlopeTimes_rayInv.mp (mem_raySlopeTimes_of_lt_of_lt hu hz ?_ ?_)
    · exact ha1.trans_le (EReal.coe_le_coe_iff.mpr (by linarith))
    · exact (EReal.coe_le_coe_iff.mpr (by linarith)).trans_lt hb2
  have : z + (τ - u z) • strainDir u z + t • strainDir u z = z + (τ + t - u z) • strainDir u z := by
    module
  rw [this, hσ, hτ]

/-- **`Ends u` is exactly the set of endpoints of the maximal slope-one segments through strain
points.**  A point `x ∉ Strain u` lies on a slope-one segment of positive length iff it is the point
of parameter `τ = rayLo u z` or `τ = rayHi u z` on the maximal ray through some strain point `z`. -/
theorem mem_ends_iff {u : Space n → ℝ} (hu : LipschitzWith 1 u) (x : Space n) :
    x ∈ Ends u ↔ x ∉ Strain u ∧ ∃ z ∈ Strain u, ∃ τ : ℝ, (rayLo u z = τ ∨ rayHi u z = τ) ∧
      x = z + (τ - u z) • strainDir u z := by
  constructor
  · rintro ⟨hxS, hx⟩
    refine ⟨hxS, ?_⟩
    obtain ⟨e, he, c, hc, s, hs, h⟩ := (onSlopeOneSegment_iff_segment hu x).mp hx
    have hc2 : c * c = 1 := by rcases hc with rfl | rfl <;> norm_num
    set z : Space n := x + (s / 2) • e with hzdef
    have huz : u z = u x + c * (s / 2) := h (s / 2) (by positivity) (by linarith)
    have hθ : HasRaySlope u (s / 2) z (c • e) := by
      refine ⟨?_, fun t ht => ?_⟩
      · rw [norm_smul, he, mul_one, Real.norm_eq_abs]
        rcases hc with rfl | rfl <;> simp
      · have hmem : 0 ≤ s / 2 + t * c ∧ s / 2 + t * c ≤ s := by
          have habs : |t * c| ≤ s / 2 := by
            rw [abs_mul]; rcases hc with rfl | rfl <;> simpa using ht
          constructor <;> linarith [(abs_le.mp habs).1, (abs_le.mp habs).2]
        have hz' : z + t • c • e = x + (s / 2 + t * c) • e := by
          rw [hzdef, smul_smul, add_smul, add_assoc]
        rw [hz', h _ hmem.1 hmem.2, huz]
        calc u x + c * (s / 2 + t * c) = u x + c * (s / 2) + t * (c * c) := by ring
          _ = _ := by rw [hc2]; ring
    have hzS : z ∈ Strain u := mem_strain_iff.mpr ⟨s / 2, by positivity, c • e, hθ⟩
    have hdir : strainDir u z = c • e := hθ.strainDir_eq hu (by positivity)
    have hxz : x = z + (u x - u z) • strainDir u z := by
      rw [hdir, huz, hzdef, smul_smul]
      have : (u x - (u x + c * (s / 2))) * c = -(s / 2) := by
        linear_combination (-(s / 2)) * hc2
      rw [this]; module
    have hmem : u x ∈ raySlopeTimes u (rayInv u z) := by
      rw [mem_raySlopeTimes_rayInv, ← hxz]
    refine ⟨z, hzS, u x, ?_, hxz⟩
    obtain ⟨hlo, hhi⟩ := raySlopeTimes_subset_Icc hmem
    by_contra hcon
    push Not at hcon
    exact hxS (hxz ▸ mem_strain_of_lt_lt hu hzS (lt_of_le_of_ne hlo hcon.1)
      (lt_of_le_of_ne hhi (Ne.symm hcon.2)))
  · rintro ⟨hxS, z, hzS, τ, hτ, hxz⟩
    refine ⟨hxS, ?_⟩
    have hmem : τ ∈ raySlopeTimes u (rayInv u z) := by
      rcases hτ with h | h
      · exact mem_raySlopeTimes_of_rayLo_eq hu h
      · exact mem_raySlopeTimes_of_rayHi_eq hu h
    have hux : u x = τ := by rw [hxz]; exact mem_raySlopeTimes_rayInv.mp hmem
    have hne : τ ≠ u z := by
      rintro rfl
      rcases hτ with h | h
      · exact (rayLo_lt hu hzS).ne h
      · exact (lt_rayHi hu hzS).ne' h
    refine ⟨z, ?_, ?_⟩
    · intro hzx
      apply hne
      have : (τ - u z) • strainDir u z = 0 := by
        have := congrArg (fun w => w - z) hzx.symm
        simpa [hxz] using this
      rcases smul_eq_zero.mp this with h | h
      · linarith
      · have := norm_strainDir hzS
        rw [h, norm_zero] at this
        exact absurd this zero_ne_one
    · have h1 : x - z = (τ - u z) • strainDir u z := by rw [hxz]; abel
      rw [hux, ← norm_neg (z - x), neg_sub, h1, norm_smul, norm_strainDir hzS, mul_one,
        Real.norm_eq_abs, abs_sub_comm]

/-- The form in which the L9 premise `volume (Ends u) = 0` is used: it suffices that `μ` is
absolutely continuous with respect to `volume` (e.g. `μ` has a density). -/
theorem measure_ends_eq_zero_of_volume {μ : Measure (Space n)} (hμ : μ ≪ volume)
    {u : Space n → ℝ} (hvol : volume (Ends u) = 0) : μ (Ends u) = 0 :=
  hμ hvol

end CvxBody.Geometry
