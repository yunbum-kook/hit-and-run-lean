module
public import Mathlib.MeasureTheory.Integral.Layercake
public import CvxBody.Analysis.FunctionalInequalities
public import CvxBody.Analysis.LSIApproximation
public import CvxBody.External.OAI.KLS.Model

@[expose] public section



/-!
# A Cheeger-type isoperimetric inequality implies the Poincaré inequality

Step towards the converse of `bg:concentration` (`docs/part1/P02-MILMAN-FEASIBILITY.md`): a
probability measure `ν ≪ volume` on `ℝⁿ` with the Cheeger-type inequality
`h · min(ν A, 1 - ν A) ≤ ν⁺(A)` (outer Minkowski content `minkowskiContent`) has the Poincaré bound
`4 / h²` in the repository's formulation `IsPoincareBound` (`isPoincareBound_of_cheeger`).

Proof (Maz'ya / Cheeger):

1. `coarea_inequality`: for a Lipschitz `f`, `∫_0^∞ ν⁺{f > t} dt ≤ ∫ ‖∇f‖ dν`. The shell
   `thickening ε {f > t} ∖ {f > t} = {f ≤ t < sup_{B(x,ε)} f}` (`diff_superlevel`) is integrated in
   `t` by Tonelli (`lintegral_shell_le`), then Fatou along `ε = 1/(k+1)` and reverse Fatou with
   the pointwise bound `(sup_{B(x,ε)} f - f x)/ε → ≤ ‖∇f x‖` at differentiability points
   (Rademacher, `ν ≪ volume`).
2. `cheeger_l1`: `h ∫ p dν ≤ ∫ ‖∇p‖ dν` for `p ≥ 0` Lipschitz with `ν{p > 0} ≤ 1/2`
   (layer cake).
3. `cheeger_l2`: apply 2 to `p²` and absorb with `2ab ≤ (h/2) a² + (2/h) b²`, giving
   `∫ p² ≤ (4/h²) ∫ ‖∇p‖²`.
4. `cheeger_variance_bounded`: for bounded Lipschitz `g` with median `m` (`exists_median`), split
   `g - m` into the positive and negative parts, which are supported in sets of measure `≤ 1/2`
   and have gradients with disjoint supports (`fderiv_posPart_norm`, `fderiv_negPart_norm`).
5. `isPoincareBound_of_bounded_lipschitz`: from bounded Lipschitz to all locally Lipschitz
   `f ∈ L²(ν)` by smooth cutoffs and lower semicontinuity of the variance
   (`evariance_le_liminf`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Metric
open OAI.LeanBlast.KLS
open scoped ENNReal NNReal

namespace CvxBody

variable {n : ℕ}

/-- Outer Minkowski content `ν⁺(A) = liminf_{ε→0+} (ν(thickening ε A) - ν A)/ε`. -/
noncomputable def minkowskiContent (ν : Measure (Space n)) (A : Set (Space n)) : ℝ≥0∞ :=
  liminf (fun ε : ℝ => (ν (thickening ε A) - ν A) / ENNReal.ofReal ε) (𝓝[>] 0)

section BallSup

variable {f : Space n → ℝ} {K : ℝ≥0}

/-- Supremum of `f` over the open ball `B(x, ε)`. -/
noncomputable def ballSup (f : Space n → ℝ) (ε : ℝ) (x : Space n) : ℝ := sSup (f '' ball x ε)

theorem bddAbove_image_ball (hf : LipschitzWith K f) (ε : ℝ) (x : Space n) :
    BddAbove (f '' ball x ε) := by
  refine ⟨f x + K * ε, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h := hf.dist_le_mul y x
  rw [Real.dist_eq] at h
  have h1 : f y - f x ≤ |f y - f x| := le_abs_self _
  have h2 : dist y x < ε := hy
  have : (K : ℝ) * dist y x ≤ K * ε := by gcongr
  linarith

theorem le_ballSup (hf : LipschitzWith K f) {ε : ℝ} {x y : Space n} (hy : y ∈ ball x ε) :
    f y ≤ ballSup f ε x :=
  le_csSup (bddAbove_image_ball hf ε x) ⟨y, hy, rfl⟩

theorem ballSup_le {ε : ℝ} (hε : 0 < ε) {x : Space n} {c : ℝ} (h : ∀ y ∈ ball x ε, f y ≤ c) :
    ballSup f ε x ≤ c :=
  csSup_le ⟨f x, x, mem_ball_self hε, rfl⟩ (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)

theorem lt_ballSup_iff (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) {x : Space n} {t : ℝ} :
    t < ballSup f ε x ↔ ∃ y ∈ ball x ε, t < f y := by
  unfold ballSup
  rw [lt_csSup_iff (bddAbove_image_ball hf ε x) ⟨f x, x, mem_ball_self hε, rfl⟩]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, h⟩; exact ⟨y, hy, h⟩
  · rintro ⟨y, hy, h⟩; exact ⟨_, ⟨y, hy, rfl⟩, h⟩

theorem self_le_ballSup (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) (x : Space n) :
    f x ≤ ballSup f ε x := le_ballSup hf (mem_ball_self hε)

theorem ballSup_le_add (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) (x : Space n) :
    ballSup f ε x ≤ f x + K * ε := by
  refine ballSup_le hε fun y hy => ?_
  have h := hf.dist_le_mul y x
  rw [Real.dist_eq] at h
  have h1 : f y - f x ≤ |f y - f x| := le_abs_self _
  have h2 : dist y x < ε := hy
  have : (K : ℝ) * dist y x ≤ K * ε := by gcongr
  linarith

theorem thickening_superlevel (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    thickening ε {x | t < f x} = {x | t < ballSup f ε x} := by
  ext x
  rw [mem_thickening_iff, Set.mem_ofPred_eq, lt_ballSup_iff hf hε]
  constructor
  · rintro ⟨z, hz, hd⟩
    exact ⟨z, by rw [mem_ball, dist_comm]; exact hd, hz⟩
  · rintro ⟨z, hz, hd⟩
    exact ⟨z, hd, by rw [dist_comm]; exact hz⟩

theorem measurable_ballSup (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) :
    Measurable (ballSup f ε) := by
  have : LowerSemicontinuous (ballSup f ε) := by
    rw [lowerSemicontinuous_iff_isOpen_preimage]
    intro t
    have : ballSup f ε ⁻¹' Set.Ioi t = thickening ε {x | t < f x} := by
      rw [thickening_superlevel hf hε]; rfl
    rw [this]
    exact isOpen_thickening
  exact this.measurable

end BallSup

section Coarea

variable {f : Space n → ℝ} {K : ℝ≥0}

theorem diff_superlevel (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    thickening ε {x | t < f x} \ {x | t < f x} = {x | f x ≤ t ∧ t < ballSup f ε x} := by
  rw [thickening_superlevel hf hε]
  ext x
  simp [not_lt]
  tauto

theorem measurableSet_diffPair (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) :
    MeasurableSet {q : Space n × ℝ | f q.1 ≤ q.2 ∧ q.2 < ballSup f ε q.1} := by
  have h1 := hf.continuous.measurable
  have h2 := measurable_ballSup hf hε
  exact (measurableSet_le (h1.comp measurable_fst) measurable_snd).inter
    (measurableSet_lt measurable_snd (h2.comp measurable_fst))

/-- Measure of the shell between `A_t = {f > t}` and its thickening, integrated over `t > 0`. -/
theorem lintegral_shell_le (ν : Measure (Space n)) [IsProbabilityMeasure ν]
    (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ν (thickening ε {x | t < f x} \ {x | t < f x}) ≤
      ∫⁻ x, ENNReal.ofReal (ballSup f ε x - f x) ∂ν := by
  set P : Set (Space n × ℝ) := {q | f q.1 ≤ q.2 ∧ q.2 < ballSup f ε q.1} with hP
  have hPm : MeasurableSet P := measurableSet_diffPair hf hε
  have e1 : ∀ t, ν (thickening ε {x | t < f x} \ {x | t < f x}) =
      ν ((fun x => (x, t)) ⁻¹' P) := by
    intro t
    rw [diff_superlevel hf hε]
    rfl
  simp_rw [e1]
  rw [← Measure.prod_apply_symm hPm, Measure.prod_apply hPm]
  refine lintegral_mono fun x => ?_
  have : Prod.mk x ⁻¹' P ∩ Set.Ioi 0 ⊆ Set.Ico (f x) (ballSup f ε x) := by
    rintro t ⟨⟨h1, h2⟩, -⟩
    exact ⟨h1, h2⟩
  rw [Measure.restrict_apply (measurable_prodMk_left hPm)]
  refine (measure_mono this).trans ?_
  simp

theorem eventually_ballSup_le {x : Space n} (hx : DifferentiableAt ℝ f x) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ballSup f ε x - f x ≤ (‖fderiv ℝ f x‖ + δ) * ε := by
  have h := hx.hasFDerivAt.isLittleO.def hδ
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 h
  filter_upwards [Ioo_mem_nhdsGT hr] with ε hε
  have hε0 : 0 < ε := hε.1
  have : ballSup f ε x ≤ f x + (‖fderiv ℝ f x‖ + δ) * ε := by
    refine ballSup_le hε0 fun y hy => ?_
    have hyx : dist y x < ε := hy
    have h1 := hball (y := y) (hyx.trans hε.2)
    have h2 : f y - f x ≤ fderiv ℝ f x (y - x) + δ * ‖y - x‖ := by
      rw [Real.norm_eq_abs] at h1
      linarith [(abs_le.1 h1).2]
    have h3 : fderiv ℝ f x (y - x) ≤ ‖fderiv ℝ f x‖ * ‖y - x‖ :=
      (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ (fderiv ℝ f x).le_opNorm (y - x))
    have h4 : ‖y - x‖ < ε := by rwa [dist_eq_norm] at hyx
    have h5 : (‖fderiv ℝ f x‖ + δ) * ‖y - x‖ ≤ (‖fderiv ℝ f x‖ + δ) * ε := by
      gcongr
    nlinarith
  linarith

theorem limsup_ballSup_le {x : Space n} (hx : DifferentiableAt ℝ f x) :
    limsup (fun k : ℕ => ENNReal.ofReal ((ballSup f (1 / ((k : ℝ) + 1)) x - f x) /
      (1 / ((k : ℝ) + 1)))) atTop ≤ ENNReal.ofReal ‖fderiv ℝ f x‖ := by
  have hεt : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity⟩
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hδ' : (0 : ℝ) < δ := hδ
  have hev := hεt.eventually (eventually_ballSup_le hx hδ')
  have : limsup (fun k : ℕ => ENNReal.ofReal ((ballSup f (1 / ((k : ℝ) + 1)) x - f x) /
      (1 / ((k : ℝ) + 1)))) atTop ≤ ENNReal.ofReal (‖fderiv ℝ f x‖ + δ) := by
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [hev] with k hk
    refine ENNReal.ofReal_le_ofReal ?_
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    rw [div_le_iff₀ hpos]
    exact hk
  refine this.trans ?_
  rw [ENNReal.ofReal_add (norm_nonneg _) hδ'.le, ENNReal.ofReal_coe_nnreal]

theorem coarea_inequality (ν : Measure (Space n)) [IsProbabilityMeasure ν] (hν : ν ≪ volume)
    (hf : LipschitzWith K f) :
    ∫⁻ t in Set.Ioi (0 : ℝ), minkowskiContent ν {x | t < f x} ≤
      ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ f x‖ ∂ν := by
  have hfm : Measurable f := hf.continuous.measurable
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hε
  have hεpos : ∀ k, 0 < ε k := fun k => by simp only [hε]; positivity
  have hεt : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hεpos⟩
  set Φ : ℕ → ℝ → ℝ≥0∞ := fun k t =>
    (ν (thickening (ε k) {x | t < f x}) - ν {x | t < f x}) / ENNReal.ofReal (ε k) with hΦ
  set Ψ : ℕ → Space n → ℝ≥0∞ := fun k x =>
    ENNReal.ofReal ((ballSup f (ε k) x - f x) / ε k) with hΨ
  have hshell : ∀ k t, ν (thickening (ε k) {x | t < f x}) - ν {x | t < f x} =
      ν (thickening (ε k) {x | t < f x} \ {x | t < f x}) := fun k t =>
    (measure_sdiff (self_subset_thickening (hεpos k) _)
      (measurableSet_lt measurable_const hfm).nullMeasurableSet (measure_ne_top _ _)).symm
  have hΦm : ∀ k, Measurable (Φ k) := by
    intro k
    have : Measurable fun t : ℝ => ν (thickening (ε k) {x | t < f x} \ {x | t < f x}) := by
      have e : (fun t : ℝ => ν (thickening (ε k) {x | t < f x} \ {x | t < f x})) =
          fun t : ℝ => ν ((fun x => (x, t)) ⁻¹'
            {q : Space n × ℝ | f q.1 ≤ q.2 ∧ q.2 < ballSup f (ε k) q.1}) := by
        funext t
        rw [diff_superlevel hf (hεpos k)]
        rfl
      rw [e]
      exact measurable_measure_prodMk_right (μ := ν) (measurableSet_diffPair hf (hεpos k))
    simp only [hΦ, hshell, div_eq_mul_inv]
    exact this.mul_const _
  have hmin : ∀ t, minkowskiContent ν {x | t < f x} ≤ liminf (fun k => Φ k t) atTop := fun t =>
    hεt.liminf_le_liminf_comp (u := fun ε : ℝ =>
      (ν (thickening ε {x | t < f x}) - ν {x | t < f x}) / ENNReal.ofReal ε)
  have hΦΨ : ∀ k, ∫⁻ t in Set.Ioi (0 : ℝ), Φ k t ≤ ∫⁻ x, Ψ k x ∂ν := by
    intro k
    have hc : (ENNReal.ofReal (ε k))⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (by
      simpa using hεpos k)
    simp only [hΦ, hshell, div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ hc]
    calc (∫⁻ t in Set.Ioi (0 : ℝ), ν (thickening (ε k) {x | t < f x} \ {x | t < f x})) *
          (ENNReal.ofReal (ε k))⁻¹
        ≤ (∫⁻ x, ENNReal.ofReal (ballSup f (ε k) x - f x) ∂ν) * (ENNReal.ofReal (ε k))⁻¹ := by
          gcongr
          exact lintegral_shell_le ν hf (hεpos k)
      _ = ∫⁻ x, Ψ k x ∂ν := by
          rw [← lintegral_mul_const' _ _ hc]
          refine lintegral_congr fun x => ?_
          simp only [hΨ]
          rw [ENNReal.ofReal_div_of_pos (hεpos k), div_eq_mul_inv]
  have hΨm : ∀ k, Measurable (Ψ k) := fun k =>
    (((measurable_ballSup hf (hεpos k)).sub hfm).div_const _).ennreal_ofReal
  have hΨb : ∀ k, Ψ k ≤ᵐ[ν] fun _ => ENNReal.ofReal K := by
    intro k
    refine Eventually.of_forall fun x => ?_
    simp only [hΨ]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ (hεpos k)]
    linarith [ballSup_le_add hf (hεpos k) x]
  have hdiff : ∀ᵐ x ∂ν, DifferentiableAt ℝ f x :=
    hν.ae_le (ae_differentiableAt_of_locallyLipschitz hf.locallyLipschitz volume)
  calc ∫⁻ t in Set.Ioi (0 : ℝ), minkowskiContent ν {x | t < f x}
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ), liminf (fun k => Φ k t) atTop := lintegral_mono hmin
    _ ≤ liminf (fun k => ∫⁻ t in Set.Ioi (0 : ℝ), Φ k t) atTop := lintegral_liminf_le hΦm
    _ ≤ liminf (fun k => ∫⁻ x, Ψ k x ∂ν) atTop :=
        liminf_le_liminf (Eventually.of_forall hΦΨ)
    _ ≤ limsup (fun k => ∫⁻ x, Ψ k x ∂ν) atTop := liminf_le_limsup
    _ ≤ ∫⁻ x, limsup (fun k => Ψ k x) atTop ∂ν :=
        limsup_lintegral_le _ hΨm hΨb (by simp)
    _ ≤ ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ f x‖ ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hdiff] with x hx
        exact limsup_ballSup_le hx

end Coarea

section L1

variable {p : Space n → ℝ} {K : ℝ≥0}

/-- `L¹` Cheeger inequality for a nonnegative Lipschitz function supported in a set of measure at
most `1/2`. -/
theorem cheeger_l1 (ν : Measure (Space n)) [IsProbabilityMeasure ν] (hν : ν ≪ volume)
    {h : ℝ}
    (hcheeger : ∀ A : Set (Space n), MeasurableSet A →
        ENNReal.ofReal h * min (ν A) (1 - ν A) ≤ minkowskiContent ν A)
    (hp : LipschitzWith K p) (hp0 : ∀ x, 0 ≤ p x) (hhalf : ν {x | 0 < p x} ≤ 1 / 2) :
    ENNReal.ofReal h * ∫⁻ x, ENNReal.ofReal (p x) ∂ν ≤
      ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ p x‖ ∂ν := by
  have hpm : Measurable p := hp.continuous.measurable
  rw [lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall hp0) hpm.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans ?_ (coarea_inequality ν hν hp)
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
  have hA : MeasurableSet {x | t < p x} := measurableSet_lt measurable_const hpm
  refine le_trans (le_of_eq ?_) (hcheeger _ hA)
  have hsub : ν {x | t < p x} ≤ 1 / 2 := by
    refine le_trans (measure_mono fun x hx => ?_) hhalf
    have hx' : t < p x := hx
    exact lt_trans (Set.mem_Ioi.1 ht) hx'
  have hle : ν {x | t < p x} ≤ 1 - ν {x | t < p x} := by
    refine ENNReal.le_sub_of_add_le_left (measure_ne_top _ _) ?_
    calc ν {x | t < p x} + ν {x | t < p x} ≤ 1 / 2 + 1 / 2 := add_le_add hsub hsub
      _ = 1 := ENNReal.add_halves 1
  rw [min_eq_left hle]

theorem lipschitzWith_sq_of_bounded (hp : LipschitzWith K p) (hp0 : ∀ x, 0 ≤ p x) {M : ℝ}
    (hM : ∀ x, p x ≤ M) : LipschitzWith (Real.toNNReal (2 * M) * K) (fun x => p x ^ 2) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h1 := hp.dist_le_mul x y
  rw [Real.dist_eq] at h1 ⊢
  have hM0 : 0 ≤ M := (hp0 x).trans (hM x)
  have e : p x ^ 2 - p y ^ 2 = (p x + p y) * (p x - p y) := by ring
  rw [e, abs_mul]
  have h2 : |p x + p y| ≤ 2 * M := by
    rw [abs_of_nonneg (add_nonneg (hp0 x) (hp0 y))]
    linarith [hM x, hM y]
  have h3 : ((Real.toNNReal (2 * M) : ℝ≥0) : ℝ) = 2 * M := Real.coe_toNNReal _ (by positivity)
  push_cast
  rw [h3]
  calc |p x + p y| * |p x - p y| ≤ (2 * M) * (K * dist x y) := by gcongr
    _ = 2 * M * K * dist x y := by ring

theorem fderiv_sq_norm_le {x : Space n} (hx : DifferentiableAt ℝ p x) :
    ‖fderiv ℝ (fun y => p y ^ 2) x‖ ≤ 2 * |p x| * ‖fderiv ℝ p x‖ := by
  have e : (fun y => p y ^ 2) = fun y => p y * p y := by funext y; ring
  have hm : fderiv ℝ (fun y => p y * p y) x = p x • fderiv ℝ p x + p x • fderiv ℝ p x :=
    (hx.hasFDerivAt.mul hx.hasFDerivAt).fderiv
  rw [e, hm]
  calc ‖p x • fderiv ℝ p x + p x • fderiv ℝ p x‖ ≤ ‖p x • fderiv ℝ p x‖ + ‖p x • fderiv ℝ p x‖ :=
        norm_add_le _ _
    _ = 2 * |p x| * ‖fderiv ℝ p x‖ := by
        rw [norm_smul, Real.norm_eq_abs]; ring

/-- `L²` Cheeger-Poincaré inequality for a bounded nonnegative Lipschitz function supported in a
set of measure at most `1/2`. -/
theorem cheeger_l2 (ν : Measure (Space n)) [IsProbabilityMeasure ν] (hν : ν ≪ volume)
    {h : ℝ} (hh : 0 < h)
    (hcheeger : ∀ A : Set (Space n), MeasurableSet A →
        ENNReal.ofReal h * min (ν A) (1 - ν A) ≤ minkowskiContent ν A)
    (hp : LipschitzWith K p) (hp0 : ∀ x, 0 ≤ p x) {M : ℝ} (hM : ∀ x, p x ≤ M)
    (hhalf : ν {x | 0 < p x} ≤ 1 / 2) :
    ∫⁻ x, ENNReal.ofReal (p x ^ 2) ∂ν ≤
      ENNReal.ofReal (4 / h ^ 2) * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ p x‖ ^ 2) ∂ν := by
  have hpm : Measurable p := hp.continuous.measurable
  set I : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (p x ^ 2) ∂ν with hI
  set G : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ p x‖ ^ 2) ∂ν with hG
  have hIfin : I ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _x, ENNReal.ofReal (M ^ 2) ∂ν) (by simp) ?_
    refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
    exact pow_le_pow_left₀ (hp0 x) (hM x) 2
  have hq := cheeger_l1 ν hν hcheeger (lipschitzWith_sq_of_bounded hp hp0 hM)
    (fun x => sq_nonneg _) (by
      refine le_trans (le_of_eq ?_) hhalf
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq]
      exact ⟨fun h' => by
        rcases (hp0 x).lt_or_eq with h1 | h1
        · exact h1
        · rw [← h1] at h'; simp at h', fun h' => by positivity⟩)
  have hdiff : ∀ᵐ x ∂ν, DifferentiableAt ℝ p x :=
    hν.ae_le (ae_differentiableAt_of_locallyLipschitz hp.locallyLipschitz volume)
  have hamgm : ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ (fun y => p y ^ 2) x‖ ∂ν ≤
      ENNReal.ofReal (h / 2) * I + ENNReal.ofReal (2 / h) * G := by
    have hmeas1 : Measurable fun x => ENNReal.ofReal (p x ^ 2) := by
      have := hpm; fun_prop
    rw [hI, hG, ← lintegral_const_mul _ hmeas1]
    have hmeas2 : Measurable fun x => ENNReal.ofReal (‖fderiv ℝ p x‖ ^ 2) := by
      have := hpm
      exact ((measurable_fderiv ℝ p).norm.pow_const 2).ennreal_ofReal
    rw [← lintegral_const_mul _ hmeas2, ← lintegral_add_left (hmeas1.const_mul _)]
    refine lintegral_mono_ae ?_
    filter_upwards [hdiff] with x hx
    have h1 := fderiv_sq_norm_le hx
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal (h1.trans ?_)
    set u := |p x|
    set v := ‖fderiv ℝ p x‖
    have e : (h / 2) * p x ^ 2 + 2 / h * v ^ 2 - 2 * u * v = 2 / h * (h / 2 * u - v) ^ 2 := by
      have : p x ^ 2 = u ^ 2 := (sq_abs _).symm
      rw [this]
      field_simp
      ring
    have : 0 ≤ 2 / h * (h / 2 * u - v) ^ 2 := by positivity
    linarith
  have h2 : ENNReal.ofReal h * I ≤ ENNReal.ofReal (h / 2) * I + ENNReal.ofReal (2 / h) * G := by
    exact hq.trans hamgm
  have hsplit : ENNReal.ofReal h = ENNReal.ofReal (h / 2) + ENNReal.ofReal (h / 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have haI : ENNReal.ofReal (h / 2) * I ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIfin
  have h3 : ENNReal.ofReal (h / 2) * I ≤ ENNReal.ofReal (2 / h) * G := by
    rw [hsplit, add_mul] at h2
    exact (ENNReal.add_le_add_iff_left haI).1 h2
  have h4 : ENNReal.ofReal (2 / h) * ENNReal.ofReal (h / 2) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have : 2 / h * (h / 2) = 1 := by field_simp
    rw [this, ENNReal.ofReal_one]
  calc I = (ENNReal.ofReal (2 / h) * ENNReal.ofReal (h / 2)) * I := by rw [h4, one_mul]
    _ = ENNReal.ofReal (2 / h) * (ENNReal.ofReal (h / 2) * I) := by rw [mul_assoc]
    _ ≤ ENNReal.ofReal (2 / h) * (ENNReal.ofReal (2 / h) * G) := by gcongr
    _ = ENNReal.ofReal (4 / h ^ 2) * G := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp
        norm_num

end L1


/-- A bounded measurable function on a probability space has a median. -/
theorem exists_median {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    {g : α → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) :
    ∃ m : ℝ, ν {x | m < g x} ≤ 1 / 2 ∧ ν {x | g x < m} ≤ 1 / 2 := by
  set S : Set ℝ := {t | ν {x | t < g x} ≤ 1 / 2} with hS
  have hup : ∀ t ∈ S, ∀ t', t ≤ t' → t' ∈ S := fun t ht t' htt' =>
    le_trans (measure_mono fun x hx => lt_of_le_of_lt htt' hx) ht
  have hMS : M ∈ S := by
    have : {x | M < g x} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact (le_abs_self _).trans (hM x)
    show ν {x | M < g x} ≤ 1 / 2
    rw [this]; simp
  have hlow : ∀ t ∈ S, -M ≤ t := by
    intro t ht
    by_contra hlt
    push Not at hlt
    have : {x | t < g x} = Set.univ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      have := neg_abs_le (g x)
      linarith [hM x]
    have h2 : ν {x | t < g x} ≤ 1 / 2 := ht
    rw [this, measure_univ] at h2
    have : (1 / 2 : ℝ≥0∞) < 1 := ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top
    exact absurd h2 (not_le.2 this)
  have hne : S.Nonempty := ⟨M, hMS⟩
  have hbdd : BddBelow S := ⟨-M, hlow⟩
  set m := sInf S with hm
  have hmem : ∀ ε > 0, m + ε ∈ S := by
    intro ε hε
    obtain ⟨s, hs, hsl⟩ := exists_lt_of_csInf_lt hne (show sInf S < m + ε by linarith)
    exact hup s hs _ hsl.le
  have hnmem : ∀ ε > 0, m - ε ∉ S := by
    intro ε hε hmε
    have := csInf_le hbdd hmε
    linarith
  refine ⟨m, ?_, ?_⟩
  · have hmono : Monotone fun k : ℕ => {x | m + 1 / ((k : ℝ) + 1) < g x} := by
      intro a b hab x hx
      have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
        gcongr
      have hx' : m + 1 / ((a : ℝ) + 1) < g x := hx
      exact lt_of_le_of_lt (by linarith) hx'
    have hlim := tendsto_measure_iUnion_atTop (μ := ν) hmono
    have hU : (⋃ k : ℕ, {x | m + 1 / ((k : ℝ) + 1) < g x}) = {x | m < g x} := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨k, hk⟩
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      · intro hx
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
        exact ⟨k, by linarith⟩
    rw [hU] at hlim
    refine le_of_tendsto' hlim fun k => ?_
    exact hmem _ (by positivity)
  · have hmono : Monotone fun k : ℕ => {x | g x ≤ m - 1 / ((k : ℝ) + 1)} := by
      intro a b hab x hx
      have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
        gcongr
      have hx' : g x ≤ m - 1 / ((a : ℝ) + 1) := hx
      exact le_trans hx' (by linarith)
    have hlim := tendsto_measure_iUnion_atTop (μ := ν) hmono
    have hU : (⋃ k : ℕ, {x | g x ≤ m - 1 / ((k : ℝ) + 1)}) = {x | g x < m} := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨k, hk⟩
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      · intro hx
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
        exact ⟨k, by linarith⟩
    rw [hU] at hlim
    refine le_of_tendsto' hlim fun k => ?_
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have h1 := hnmem _ hk
    have h2 : (1 / 2 : ℝ≥0∞) < ν {x | m - 1 / ((k : ℝ) + 1) < g x} := by
      by_contra hcon
      exact h1 (not_lt.1 hcon)
    have hc : {x | g x ≤ m - 1 / ((k : ℝ) + 1)} = {x | m - 1 / ((k : ℝ) + 1) < g x}ᶜ := by
      ext x; simp
    show ν {x | g x ≤ m - 1 / ((k : ℝ) + 1)} ≤ 1 / 2
    rw [hc, prob_compl_eq_one_sub (measurableSet_lt measurable_const hg)]
    rw [tsub_le_iff_right]
    calc (1 : ℝ≥0∞) = 1 / 2 + 1 / 2 := (ENNReal.add_halves 1).symm
      _ ≤ 1 / 2 + ν {x | m - 1 / ((k : ℝ) + 1) < g x} := by gcongr

section Positive

variable {g : Space n → ℝ} {K : ℝ≥0}

theorem fderiv_posPart_norm {m : ℝ} (x : Space n) (hg : Continuous g) :
    ‖fderiv ℝ (fun y => max (g y - m) 0) x‖ = if m < g x then ‖fderiv ℝ g x‖ else 0 := by
  split_ifs with hx
  · have hev : (fun y => max (g y - m) 0) =ᶠ[𝓝 x] fun y => g y - m := by
      filter_upwards [hg.continuousAt.eventually (lt_mem_nhds hx)] with y hy
      exact max_eq_left (by linarith)
    rw [hev.fderiv_eq, fderiv_sub_const]
  · have hmin : IsLocalMin (fun y => max (g y - m) 0) x := by
      refine Eventually.of_forall fun y => ?_
      have : max (g x - m) 0 = 0 := max_eq_right (by linarith [not_lt.1 hx])
      simp [this]
    rw [hmin.fderiv_eq_zero, norm_zero]

theorem fderiv_negPart_norm {m : ℝ} (x : Space n) (hg : Continuous g) :
    ‖fderiv ℝ (fun y => max (m - g y) 0) x‖ = if g x < m then ‖fderiv ℝ g x‖ else 0 := by
  split_ifs with hx
  · have hev : (fun y => max (m - g y) 0) =ᶠ[𝓝 x] fun y => m - g y := by
      filter_upwards [hg.continuousAt.eventually (gt_mem_nhds hx)] with y hy
      exact max_eq_left (by linarith)
    rw [hev.fderiv_eq, fderiv_const_sub, norm_neg]
  · have hmin : IsLocalMin (fun y => max (m - g y) 0) x := by
      refine Eventually.of_forall fun y => ?_
      have : max (m - g x) 0 = 0 := max_eq_right (by linarith [not_lt.1 hx])
      simp [this]
    rw [hmin.fderiv_eq_zero, norm_zero]

/-- The Cheeger inequality implies the Poincaré inequality for bounded Lipschitz functions. -/
theorem cheeger_variance_bounded (ν : Measure (Space n)) [IsProbabilityMeasure ν] (hν : ν ≪ volume)
    {h : ℝ} (hh : 0 < h)
    (hcheeger : ∀ A : Set (Space n), MeasurableSet A →
        ENNReal.ofReal h * min (ν A) (1 - ν A) ≤ minkowskiContent ν A)
    (hg : LipschitzWith K g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) :
    evariance g ν ≤ ENNReal.ofReal (4 / h ^ 2) * gradEnergy ν g := by
  have hgm : Measurable g := hg.continuous.measurable
  obtain ⟨m, hm1, hm2⟩ := exists_median ν hgm hM
  set p : Space n → ℝ := fun y => max (g y - m) 0 with hp
  set q : Space n → ℝ := fun y => max (m - g y) 0 with hq
  have hpL : LipschitzWith K p := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h1 := hg.dist_le_mul x y
    rw [Real.dist_eq] at h1 ⊢
    exact (abs_max_sub_max_le_abs _ _ _).trans (by
      have : g x - m - (g y - m) = g x - g y := by ring
      rw [this]; exact h1)
  have hqL : LipschitzWith K q := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h1 := hg.dist_le_mul x y
    rw [Real.dist_eq] at h1 ⊢
    exact (abs_max_sub_max_le_abs _ _ _).trans (by
      have : m - g x - (m - g y) = -(g x - g y) := by ring
      rw [this, abs_neg]; exact h1)
  have hp0 : ∀ x, 0 ≤ p x := fun x => le_max_right _ _
  have hq0 : ∀ x, 0 ≤ q x := fun x => le_max_right _ _
  have hMm : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hpM : ∀ x, p x ≤ M + |m| := fun x => by
    refine max_le ?_ (by positivity)
    have := (le_abs_self (g x)).trans (hM x)
    linarith [neg_abs_le m, le_abs_self m]
  have hqM : ∀ x, q x ≤ M + |m| := fun x => by
    refine max_le ?_ (by positivity)
    have := (neg_abs_le (g x)).trans' (le_refl _)
    linarith [neg_abs_le (g x), hM x, le_abs_self m]
  have hpset : {x | 0 < p x} = {x | m < g x} := by
    ext x
    simp only [Set.mem_ofPred_eq, hp, lt_max_iff, lt_self_iff_false, or_false, sub_pos]
  have hqset : {x | 0 < q x} = {x | g x < m} := by
    ext x
    simp only [Set.mem_ofPred_eq, hq, lt_max_iff, lt_self_iff_false, or_false, sub_pos]
  have hP := cheeger_l2 ν hν hh hcheeger hpL hp0 hpM (by rw [hpset]; exact hm1)
  have hQ := cheeger_l2 ν hν hh hcheeger hqL hq0 hqM (by rw [hqset]; exact hm2)
  have hpm : Measurable fun x => ENNReal.ofReal (p x ^ 2) := by
    have := hpL.continuous.measurable; fun_prop
  have hdiffsq : ∀ x, ENNReal.ofReal (‖fderiv ℝ p x‖ ^ 2) + ENNReal.ofReal (‖fderiv ℝ q x‖ ^ 2) ≤
      ENNReal.ofReal (‖fderiv ℝ g x‖ ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 := fderiv_posPart_norm (m := m) x hg.continuous
    have e2 := fderiv_negPart_norm (m := m) x hg.continuous
    simp only [← hp] at e1
    simp only [← hq] at e2
    rw [e1, e2]
    rcases lt_trichotomy (g x) m with h1 | h1 | h1
    · simp [h1, not_lt.2 h1.le]
    · simp [h1]
    · simp [h1, not_lt.2 h1.le]
  have hsum : ∀ x, ENNReal.ofReal ((g x - m) ^ 2) =
      ENNReal.ofReal (p x ^ 2) + ENNReal.ofReal (q x ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    congr 1
    simp only [hp, hq]
    rcases le_total (g x) m with h1 | h1
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  -- variance is at most the second moment about the median
  have hgL2 : MemLp g 2 ν := memLp_of_bounded (a := -M) (b := M)
    (Eventually.of_forall fun x => abs_le.mp (hM x)) hgm.aestronglyMeasurable 2
  have hvar : evariance g ν ≤ ∫⁻ x, ENNReal.ofReal ((g x - m) ^ 2) ∂ν := by
    have hgm2 : MemLp (fun x => g x - m) 2 ν := hgL2.sub (memLp_const m)
    have h1 : variance g ν ≤ ∫ x, (g x - m) ^ 2 ∂ν := by
      have := variance_le_expectation_sq (μ := ν) (X := fun x => g x - m)
        (hgm.sub_const m).aestronglyMeasurable
      rwa [variance_sub_const hgm.aestronglyMeasurable] at this
    rw [← hgL2.ofReal_variance_eq,
      ← ofReal_integral_eq_lintegral_ofReal hgm2.integrable_sq
        (Eventually.of_forall fun x => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal h1
  refine hvar.trans ?_
  calc ∫⁻ x, ENNReal.ofReal ((g x - m) ^ 2) ∂ν
      = ∫⁻ x, ENNReal.ofReal (p x ^ 2) ∂ν + ∫⁻ x, ENNReal.ofReal (q x ^ 2) ∂ν := by
        simp_rw [hsum]
        exact lintegral_add_left hpm _
    _ ≤ ENNReal.ofReal (4 / h ^ 2) * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ p x‖ ^ 2) ∂ν +
        ENNReal.ofReal (4 / h ^ 2) * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ q x‖ ^ 2) ∂ν :=
        add_le_add hP hQ
    _ = ENNReal.ofReal (4 / h ^ 2) * ∫⁻ x, (ENNReal.ofReal (‖fderiv ℝ p x‖ ^ 2) +
          ENNReal.ofReal (‖fderiv ℝ q x‖ ^ 2)) ∂ν := by
        rw [← mul_add]
        congr 1
        rw [lintegral_add_left]
        exact ((measurable_fderiv ℝ p).norm.pow_const 2).ennreal_ofReal
    _ ≤ ENNReal.ofReal (4 / h ^ 2) * gradEnergy ν g := by
        exact mul_le_mul_right (lintegral_mono hdiffsq) _

end Positive


section Reduction

/-- Lower semicontinuity of `evariance` along dominated pointwise convergence. -/
theorem evariance_le_liminf {E : Type*} [MeasurableSpace E] (ν : Measure E) {g : ℕ → E → ℝ}
    {f G : E → ℝ} (hG : Integrable G ν) (hmeas : ∀ k, Measurable (g k))
    (hle : ∀ k x, |g k x| ≤ G x) (hlim : ∀ x, Tendsto (fun k => g k x) atTop (𝓝 (f x))) :
    evariance f ν ≤ liminf (fun k => evariance (g k) ν) atTop := by
  set m : ℕ → ℝ := fun k => ∫ y, g k y ∂ν with hmdef
  set m' : ℝ := ∫ y, f y ∂ν with hm'def
  have hm : Tendsto m atTop (𝓝 m') :=
    tendsto_integral_of_dominated_convergence G (fun k => (hmeas k).aestronglyMeasurable) hG
      (fun k => Eventually.of_forall (fun x => by simpa using hle k x))
      (Eventually.of_forall hlim)
  have hmeasF : ∀ k, Measurable (fun x => ENNReal.ofReal ((g k x - m k) ^ 2)) := by
    intro k
    have := hmeas k
    fun_prop
  have hFat := lintegral_liminf_le (μ := ν) (u := (atTop : Filter ℕ)) hmeasF
  have hpt : ∀ x, liminf (fun k => ENNReal.ofReal ((g k x - m k) ^ 2)) atTop =
      ENNReal.ofReal ((f x - m') ^ 2) := by
    intro x
    refine Tendsto.liminf_eq (ENNReal.tendsto_ofReal ?_)
    exact ((hlim x).sub hm).pow 2
  simp only [hpt] at hFat
  simp only [evariance_eq_lintegral_ofReal]
  exact hFat

theorem isPoincareBound_of_bounded_lipschitz (ν : Measure (Space n)) [IsProbabilityMeasure ν]
    (hν : ν ≪ volume) {C : ℝ}
    (h : ∀ g : Space n → ℝ, (∃ K : ℝ≥0, LipschitzWith K g) → (∃ M, ∀ x, |g x| ≤ M) →
      evariance g ν ≤ ENNReal.ofReal C * gradEnergy ν g) :
    IsPoincareBound ν C := by
  intro f hf hfm
  set a : ℝ≥0∞ := ENNReal.ofReal C with ha
  have hatop : a ≠ ⊤ := ENNReal.ofReal_ne_top
  set G : ℝ≥0∞ := gradEnergy ν f with hGdef
  by_cases hGtop : G = ⊤ ∧ a ≠ 0
  · rw [hGtop.1, ENNReal.mul_top hGtop.2]; exact le_top
  have hG' : a = 0 ∨ G ≠ ⊤ := by
    by_cases h0 : a = 0
    · exact Or.inl h0
    · exact Or.inr fun hGt => hGtop ⟨hGt, h0⟩
  obtain ⟨L, χ, hχ⟩ := exists_cutoff (Space n)
  set I : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂ν with hIdef
  have hI : I ≠ ⊤ := hfm.integrable_sq.lintegral_lt_top.ne
  have hfc : Continuous f := hf.continuous
  have hdiff : ∀ᵐ x ∂ν, DifferentiableAt ℝ f x :=
    hν.ae_le (ae_differentiableAt_of_locallyLipschitz hf volume)
  set g : ℕ → Space n → ℝ := fun n x => f x * χ ((n : ℝ) + 1) x with hg
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hχc : ∀ n : ℕ, Continuous (χ ((n : ℝ) + 1)) := fun n =>
    (hχ _ (hpos n)).1.continuous
  have hgc : ∀ n, Continuous (g n) := fun n => hfc.mul (hχc n)
  have hgrad : ∀ n : ℕ, gradEnergy ν (g n) ≤
      ENNReal.ofReal (1 + ((n : ℝ) + 1)⁻¹) * G +
        ENNReal.ofReal ((1 + ((n : ℝ) + 1)) * (L / ((n : ℝ) + 1)) ^ 2) * I := by
    intro n
    obtain ⟨hcd, h01, -, -, hgr, -⟩ := hχ ((n : ℝ) + 1) (hpos n)
    have hmeas : Measurable fun x => ENNReal.ofReal ((1 + ((n : ℝ) + 1)) * (L / ((n : ℝ) + 1)) ^ 2)
        * ENNReal.ofReal (f x ^ 2) := by
      have := hfc
      exact (by fun_prop : Measurable fun x => ENNReal.ofReal (f x ^ 2)).const_mul _
    calc gradEnergy ν (g n)
        ≤ ∫⁻ x, (ENNReal.ofReal (1 + ((n : ℝ) + 1)⁻¹) * ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2)
            + ENNReal.ofReal ((1 + ((n : ℝ) + 1)) * (L / ((n : ℝ) + 1)) ^ 2)
              * ENNReal.ofReal (f x ^ 2)) ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [hdiff] with x hx
          have hp := norm_fderiv_mul_cutoff_sq_le hx (hcd.differentiable one_ne_zero x)
            (h01 x).1 (h01 x).2 (hgr x) (hpos n)
          calc ENNReal.ofReal (‖fderiv ℝ (g n) x‖ ^ 2)
              ≤ ENNReal.ofReal ((1 + ((n : ℝ) + 1)⁻¹) * ‖fderiv ℝ f x‖ ^ 2 +
                  (1 + ((n : ℝ) + 1)) * ((L / ((n : ℝ) + 1)) ^ 2 * f x ^ 2)) :=
                ENNReal.ofReal_le_ofReal hp
            _ = _ := by
                rw [ENNReal.ofReal_add (by positivity) (by positivity)]
                congr 1
                · exact ENNReal.ofReal_mul (by positivity)
                · rw [← ENNReal.ofReal_mul (by positivity)]
                  congr 1
                  ring
      _ = ENNReal.ofReal (1 + ((n : ℝ) + 1)⁻¹) * G +
            ENNReal.ofReal ((1 + ((n : ℝ) + 1)) * (L / ((n : ℝ) + 1)) ^ 2) * I := by
          rw [lintegral_add_right _ hmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          rfl
  have hent : ∀ n : ℕ, evariance (g n) ν ≤
      a * (ENNReal.ofReal (1 + ((n : ℝ) + 1)⁻¹) * G +
        ENNReal.ofReal ((1 + ((n : ℝ) + 1)) * (L / ((n : ℝ) + 1)) ^ 2) * I) := by
    intro n
    obtain ⟨-, h01, -, hsupp, -, Lχ, hLχ⟩ := hχ ((n : ℝ) + 1) (hpos n)
    obtain ⟨K, M, hK, hM⟩ := exists_lipschitzWith_mul_cutoff hf hLχ
      (fun x => by rw [abs_of_nonneg (h01 x).1]; exact (h01 x).2) hsupp
    exact (h _ ⟨K, hK⟩ ⟨M, hM⟩).trans (by gcongr; exact hgrad n)
  have hu : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h1 : Tendsto (fun n : ℕ => 1 + ((n : ℝ) + 1)⁻¹) atTop (𝓝 1) := by
    simpa using hu.const_add 1
  have h2 : Tendsto (fun n : ℕ => (1 + ((n : ℝ) + 1)) * (L / ((n : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
    have h3 : Tendsto (fun n : ℕ => L ^ 2 * (((n : ℝ) + 1)⁻¹ ^ 2 + ((n : ℝ) + 1)⁻¹)) atTop
        (𝓝 (L ^ 2 * (0 ^ 2 + 0))) := (((hu.pow 2).add hu).const_mul _)
    rw [show L ^ 2 * ((0 : ℝ) ^ 2 + 0) = 0 by ring] at h3
    refine h3.congr fun n => ?_
    have := (hpos n).ne'
    field_simp
  have hb : Tendsto (fun n : ℕ => a * (ENNReal.ofReal (1 + ((n : ℝ) + 1)⁻¹) * G +
      ENNReal.ofReal ((1 + ((n : ℝ) + 1)) * (L / ((n : ℝ) + 1)) ^ 2) * I)) atTop (𝓝 (a * G)) := by
    rcases hG' with ha0 | hG
    · simp [ha0]
    have e1 := ENNReal.tendsto_ofReal h1
    have e2 := ENNReal.tendsto_ofReal h2
    rw [ENNReal.ofReal_one] at e1
    rw [ENNReal.ofReal_zero] at e2
    have e3 := (ENNReal.Tendsto.mul_const e1 (Or.inr hG)).add
      (ENNReal.Tendsto.mul_const e2 (Or.inr hI))
    have e4 := ENNReal.Tendsto.const_mul e3 (Or.inr hatop) (a := a)
    simpa using e4
  have hlsc : evariance f ν ≤ liminf (fun k => evariance (g k) ν) atTop := by
    refine evariance_le_liminf ν (G := fun x => |f x|)
      (hfm.integrable (by norm_num)).abs (fun n => ?_) (fun n x => ?_) (fun x => ?_)
    · have := hgc n
      fun_prop
    · obtain ⟨-, h01, -⟩ := hχ ((n : ℝ) + 1) (hpos n)
      simp only [hg, abs_mul]
      have : |χ ((n : ℝ) + 1) x| ≤ 1 := by
        rw [abs_of_nonneg (h01 x).1]; exact (h01 x).2
      calc |f x| * |χ ((n : ℝ) + 1) x| ≤ |f x| * 1 := by gcongr
        _ = |f x| := mul_one _
    · obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      obtain ⟨-, -, h1x, -⟩ := hχ ((n : ℝ) + 1) (hpos n)
      have : ‖x‖ ≤ (n : ℝ) + 1 := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      simp only [hg, h1x x this]
      ring
  exact hlsc.trans ((liminf_le_liminf (Eventually.of_forall hent)).trans_eq hb.liminf_eq)

end Reduction

/-- **A Cheeger-type isoperimetric inequality implies the Poincaré inequality.** -/
theorem isPoincareBound_of_cheeger (ν : Measure (Space n)) [IsProbabilityMeasure ν]
    (hν : ν ≪ volume) {h : ℝ} (hh : 0 < h)
    (hcheeger : ∀ A : Set (Space n), MeasurableSet A →
        ENNReal.ofReal h * min (ν A) (1 - ν A) ≤ minkowskiContent ν A) :
    IsPoincareBound ν (4 / h ^ 2) :=
  isPoincareBound_of_bounded_lipschitz ν hν fun _ ⟨_, hg⟩ ⟨_, hM⟩ =>
    cheeger_variance_bounded ν hν hh hcheeger hg hM

end CvxBody
