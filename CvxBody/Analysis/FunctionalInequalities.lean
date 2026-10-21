module
public import Mathlib.Probability.Moments.CovarianceBilin
public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
# Poincaré and log-Sobolev bounds

Definitions of valid Poincaré and log-Sobolev bounds for a probability measure `ν` on a Euclidean
space, following `eq:functional` of the manuscript (P02.1 of `docs/part1/FORMALIZATION-PLAN.md`).

Conventions (to be reviewed): the test class is the locally Lipschitz functions `f` with
`f ∈ L²(ν)`, the gradient is `fderiv ℝ f` (which is the gradient almost everywhere with respect to
Lebesgue measure by Rademacher, and the manuscript's measures are absolutely continuous), and all
quantities are extended nonnegative numbers so no integrability junk values enter:
`evariance` for the variance, `gradEnergy` for `∫ ‖∇f‖² dν`, and `entropyFun` for `ent_ν g`,
written as the integral of the nonnegative function `m * klFun (g / m)`, `m = ∫ g dν`.
"Valid bound" predicates are used instead of the smallest constants, so that no `sInf` junk value
arises for measures without any bound.

Scope of the predicates (see `docs/part1/P02-REVIEW.md`): they are intended for probability
measures `ν` that are absolutely continuous with respect to Lebesgue measure (for other `ν` the
value `0` of `fderiv` at non-differentiable points only makes the predicate stricter, and for a
non-probability `ν` the variance is taken about `∫ f dν`). The test class requires `f ∈ L²(ν)`,
whereas `eq:functional` quantifies over all locally Lipschitz `f`; as a hypothesis this is the
weaker form, and for the proved bounds the two agree (when `f ∉ L²` one has `∫ ‖∇f‖² = ∞` for
the measures treated, by truncation).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CvxBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- Gradient energy `∫ ‖∇f‖² dν` as an extended nonnegative number (no integrability needed). -/
noncomputable def gradEnergy (ν : Measure E) (f : E → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2) ∂ν

/-- `C` is a valid Poincaré bound for `ν`. -/
def IsPoincareBound (ν : Measure E) (C : ℝ) : Prop :=
  ∀ f : E → ℝ, LocallyLipschitz f → MemLp f 2 ν →
    evariance f ν ≤ ENNReal.ofReal C * gradEnergy ν f

/-- Entropy `ent_ν g = ∫ g log g dν - (∫ g dν) log ∫ g dν` of a nonnegative function, written as
the integral of the nonnegative function `m * klFun (g / m)` with `m = ∫ g dν`, so it is defined
without integrability assumptions. -/
noncomputable def entropyFun (ν : Measure E) (g : E → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((∫ y, g y ∂ν) * InformationTheory.klFun (g x / ∫ y, g y ∂ν)) ∂ν

/-- `C` is a valid log-Sobolev bound for `ν`. -/
def IsLogSobolevBound (ν : Measure E) (C : ℝ) : Prop :=
  ∀ f : E → ℝ, LocallyLipschitz f → MemLp f 2 ν →
    entropyFun ν (fun x => f x ^ 2) ≤ ENNReal.ofReal (2 * C) * gradEnergy ν f

theorem IsPoincareBound.mono {ν : Measure E} {C C' : ℝ} (h : IsPoincareBound ν C) (hC : C ≤ C') :
    IsPoincareBound ν C' := fun f hf hm =>
  (h f hf hm).trans (by gcongr)

theorem IsLogSobolevBound.mono {ν : Measure E} {C C' : ℝ} (h : IsLogSobolevBound ν C)
    (hC : C ≤ C') : IsLogSobolevBound ν C' := fun f hf hm =>
  (h f hf hm).trans (by gcongr)


section Covariance

variable [CompleteSpace E] [BorelSpace E]

/-- A Poincaré bound `C` bounds the covariance: `θᵀ Cov(ν) θ ≤ C ‖θ‖²`. This is the easy half of
`eq:small-A`, namely `‖cov π‖_op ≲ C_PI`. -/
theorem covarianceBilin_self_le_of_isPoincareBound (ν : Measure E) [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0 ≤ C) (hP : IsPoincareBound ν C) (hν : MemLp id 2 ν) (θ : E) :
    covarianceBilin ν θ θ ≤ C * ‖θ‖ ^ 2 := by
  have hlin : MemLp (fun u => inner ℝ θ u) 2 ν := (innerSL ℝ θ).comp_memLp' hν
  have hlip : LocallyLipschitz (fun u => inner ℝ θ u) :=
    (innerSL ℝ θ).lipschitzWith.locallyLipschitz
  have h := hP _ hlip hlin
  have hgrad : gradEnergy ν (fun u => inner ℝ θ u) = ENNReal.ofReal (‖θ‖ ^ 2) := by
    unfold gradEnergy
    have : ∀ u, fderiv ℝ (fun u => inner ℝ θ u) u = innerSL ℝ θ := fun u =>
      (innerSL ℝ θ).fderiv
    simp [this, innerSL_apply_norm]
  rw [hgrad, ← hlin.ofReal_variance_eq, ← ENNReal.ofReal_mul hC,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  rw [covarianceBilin_self hν]
  exact h

end Covariance

section Calculus

open Real InformationTheory Filter Topology

/-- Quantitative second-order Taylor bound for `klFun` at `1`. -/
theorem klFun_one_add_sub_sq_le (u : ℝ) (hu : |u| ≤ 1 / 2) :
    |klFun (1 + u) - u ^ 2 / 2| ≤ 4 * |u| ^ 3 := by
  have hu1 : |-u| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hu1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have hlog : log (1 + u) = u - u ^ 2 / 2 + (log (1 + u) - (u - u ^ 2 / 2)) := by ring
  set r := log (1 + u) - (u - u ^ 2 / 2) with hr
  have hr_bound : |r| ≤ |u| ^ 3 / (1 - |u|) := by
    have e : r = -u + u ^ 2 / (1 + 1) + log (1 + u) := by rw [hr]; ring
    rw [e]
    simpa [abs_neg] using h
  have hk : klFun (1 + u) - u ^ 2 / 2 = -u ^ 3 / 2 + (1 + u) * r := by
    have h1u : log (1 + u) = u - u ^ 2 / 2 + r := by rw [hr]; ring
    simp only [klFun]
    rw [h1u]
    ring
  rw [hk]
  have hpos : 0 < 1 - |u| := by linarith
  have hr2 : |r| ≤ 2 * |u| ^ 3 := by
    refine hr_bound.trans ?_
    rw [div_le_iff₀ hpos]
    have : 0 ≤ |u| ^ 3 := by positivity
    nlinarith
  calc |-u ^ 3 / 2 + (1 + u) * r| ≤ |-u ^ 3 / 2| + |(1 + u) * r| := abs_add_le _ _
    _ ≤ |u| ^ 3 / 2 + (3 / 2) * (2 * |u| ^ 3) := by
        gcongr
        · rw [abs_div, abs_neg, abs_pow]; norm_num
        · rw [abs_mul]
          gcongr
          calc |1 + u| ≤ 1 + |u| := (abs_add_le _ _).trans (by simp)
            _ ≤ 3 / 2 := by linarith
    _ ≤ 4 * |u| ^ 3 := by
        have : 0 ≤ |u| ^ 3 := by positivity
        nlinarith

/-- Pointwise limit behind the linearization `1 + ε f` of the log-Sobolev inequality. -/
theorem tendsto_linearized_entropy (a s : ℝ) (hs : 0 ≤ s) :
    Tendsto (fun ε : ℝ => (1 + ε ^ 2 * s) *
        klFun ((1 + ε * a) ^ 2 / (1 + ε ^ 2 * s)) / ε ^ 2) (𝓝[≠] 0) (𝓝 (2 * a ^ 2)) := by
  set m : ℝ → ℝ := fun ε => 1 + ε ^ 2 * s with hm
  have hmpos : ∀ ε, 0 < m ε := fun ε => by simp only [hm]; positivity
  set w : ℝ → ℝ := fun ε => (2 * a + ε * (a ^ 2 - s)) / m ε with hw
  have hmc : Continuous m := by simp only [hm]; fun_prop
  have hwc : Continuous w := by
    refine Continuous.div (by fun_prop) hmc (fun ε => (hmpos ε).ne')
  have hm0 : m 0 = 1 := by simp [hm]
  have hw0 : w 0 = 2 * a := by simp [hw, hm]
  -- identity
  have hid : ∀ ε, (1 + ε * a) ^ 2 / m ε = 1 + ε * w ε := by
    intro ε
    have := (hmpos ε).ne'
    simp only [hw, hm] at *
    field_simp
    ring
  -- main term and remainder
  set A : ℝ → ℝ := fun ε => m ε * (w ε) ^ 2 / 2 with hA
  have hAc : Continuous A := by simp only [hA]; exact (hmc.mul (hwc.pow 2)).div_const 2
  have hA0 : A 0 = 2 * a ^ 2 := by simp [hA, hm0, hw0]; ring
  set B : ℝ → ℝ := fun ε => m ε * (klFun (1 + ε * w ε) - (ε * w ε) ^ 2 / 2) / ε ^ 2 with hB
  have hAB : ∀ ε ≠ 0, m ε * klFun ((1 + ε * a) ^ 2 / m ε) / ε ^ 2 = A ε + B ε := by
    intro ε hε
    rw [hid ε]
    simp only [hA, hB]
    field_simp
    ring
  have hBlim : Tendsto B (𝓝[≠] 0) (𝓝 0) := by
    have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε * w ε| ≤ 1 / 2 := by
      have hc : Continuous fun ε => |ε * w ε| := continuous_abs.comp (continuous_id.mul hwc)
      have h0 : |(0 : ℝ) * w 0| < 1 / 2 := by simp
      exact (hc.continuousAt.eventually (gt_mem_nhds h0)).mono fun _ h => h.le
    have hbd : Continuous fun ε => 4 * m ε * |ε| * |w ε| ^ 3 := by
      have := hmc; have := hwc
      exact ((continuous_const.mul hmc).mul continuous_abs).mul (continuous_abs.comp hwc |>.pow 3)
    have hb0 : Tendsto (fun ε => 4 * m ε * |ε| * |w ε| ^ 3) (𝓝[≠] 0) (𝓝 0) := by
      have := (hbd.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
      simpa using this
    refine squeeze_zero_norm' ?_ hb0
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with ε hε hε0
    have hε0' : ε ≠ 0 := hε0
    have hE := klFun_one_add_sub_sq_le (ε * w ε) hε
    have hm_pos := hmpos ε
    have hεsq : 0 < ε ^ 2 := by positivity
    have h3 : |ε| ^ 3 = ε ^ 2 * |ε| := by rw [pow_succ, sq_abs]
    calc ‖B ε‖ = m ε * |klFun (1 + ε * w ε) - (ε * w ε) ^ 2 / 2| / ε ^ 2 := by
          simp only [hB, Real.norm_eq_abs]
          rw [abs_div, abs_mul, abs_of_pos hm_pos, abs_of_pos hεsq]
      _ ≤ m ε * (4 * |ε * w ε| ^ 3) / ε ^ 2 := by gcongr
      _ = 4 * m ε * |ε| * |w ε| ^ 3 := by
          rw [abs_mul, mul_pow, h3]
          field_simp
  have := (hAc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  rw [hA0] at this
  have h2 := this.add hBlim
  rw [add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hAB ε hε).symm

end Calculus

section LSIImpliesPI

open InformationTheory Filter Topology

variable [BorelSpace E]

private theorem integral_sq_one_add_mul {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {f : Ω → ℝ}
    (hf : MemLp f 2 ν) (h0 : ∫ x, f x ∂ν = 0) (ε : ℝ) :
    ∫ x, (1 + ε * f x) ^ 2 ∂ν = 1 + ε ^ 2 * ∫ x, f x ^ 2 ∂ν := by
  have h1 : Integrable f ν := hf.integrable (by norm_num)
  have h2 : Integrable (fun x => f x ^ 2) ν := hf.integrable_sq
  have hA : Integrable (fun x => 1 + (2 * ε) * f x) ν := (integrable_const 1).add (h1.const_mul _)
  have hB : Integrable (fun x => ε ^ 2 * f x ^ 2) ν := h2.const_mul _
  have : (fun x => (1 + ε * f x) ^ 2) = fun x => (1 + (2 * ε) * f x) + ε ^ 2 * f x ^ 2 := by
    funext x; ring
  rw [this, integral_add hA hB, integral_add (integrable_const 1) (h1.const_mul _),
    integral_const_mul, integral_const_mul, h0]
  simp

/-- A locally Lipschitz function stays locally Lipschitz after an affine change of value. -/
theorem locallyLipschitz_const_add_mul {α : Type*} [PseudoMetricSpace α] {f : α → ℝ}
    (hf : LocallyLipschitz f) (c ε : ℝ) : LocallyLipschitz fun x => c + ε * f x := by
  intro x
  obtain ⟨K, t, ht, hK⟩ := hf x
  refine ⟨‖ε‖₊ * K, t, ht, LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_⟩
  have h := hK.dist_le_mul a ha b hb
  have e : c + ε * f a - (c + ε * f b) = ε * (f a - f b) := by ring
  rw [Real.dist_eq, e, abs_mul]
  rw [Real.dist_eq] at h
  push_cast
  calc |ε| * |f a - f b| ≤ |ε| * (K * dist a b) := by gcongr
    _ = ‖ε‖ * K * dist a b := by rw [Real.norm_eq_abs]; ring

omit [BorelSpace E] in
private theorem gradEnergy_one_add_mul {ν : Measure E} (f : E → ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    gradEnergy ν (fun x => 1 + ε * f x) = ENNReal.ofReal (ε ^ 2) * gradEnergy ν f := by
  unfold gradEnergy
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext x
  have : fderiv ℝ (fun x => 1 + ε * f x) x = ε • fderiv ℝ f x := by
    have : Invertible ε := invertibleOfNonzero hε
    rw [fderiv_const_add]
    exact fderiv_const_smul_of_invertible (𝕜 := ℝ) (f := f) (x := x) ε
  rw [this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    ENNReal.ofReal_mul (sq_nonneg ε)]

/-- **A log-Sobolev bound is a Poincaré bound** with the same constant, `C_PI ≤ C_LSI`.
The proof linearizes the log-Sobolev inequality at `1 + ε f` and applies Fatou's lemma. -/
theorem IsLogSobolevBound.isPoincareBound (ν : Measure E) [IsProbabilityMeasure ν] {C : ℝ}
    (h : IsLogSobolevBound ν C) : IsPoincareBound ν C := by
  intro f hf hfm
  set c : ℝ := ∫ x, f x ∂ν with hc
  set f₀ : E → ℝ := fun x => f x - c with hf₀
  have hf₀m : MemLp f₀ 2 ν := hfm.sub (memLp_const c)
  have hf₀lip : LocallyLipschitz f₀ := by
    have := locallyLipschitz_const_add_mul hf (-c) 1
    simpa [hf₀, sub_eq_add_neg, add_comm] using this
  have hf₀cont : Continuous f₀ := hf₀lip.continuous
  have hint0 : ∫ x, f₀ x ∂ν = 0 := by
    have hi : Integrable f ν := hfm.integrable (by norm_num)
    have e : ∫ x, f₀ x ∂ν = ∫ x, f x ∂ν - c := by
      simp only [hf₀]
      rw [integral_sub hi (integrable_const c)]
      simp
    rw [e]; simp [hc]
  have hvar : evariance f ν = ∫⁻ x, ENNReal.ofReal (f₀ x ^ 2) ∂ν := by
    rw [evariance_eq_lintegral_ofReal]
  have hgrad : gradEnergy ν f = gradEnergy ν f₀ := by
    unfold gradEnergy
    congr 1
    funext x
    simp only [hf₀, fderiv_sub_const]
  rw [hvar, hgrad]
  set s : ℝ := ∫ x, f₀ x ^ 2 ∂ν with hs
  have hs0 : 0 ≤ s := integral_nonneg fun x => sq_nonneg _
  set G : ℝ≥0∞ := gradEnergy ν f₀ with hG
  -- the sequence of linearizations
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hεpos : ∀ n, 0 < ε n := fun n => by simp only [hε]; positivity
  have hεt : Tendsto ε atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall fun n => (hεpos n).ne'⟩
  set F : ℕ → E → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal (((1 + ε n ^ 2 * s) *
      klFun ((1 + ε n * f₀ x) ^ 2 / (1 + ε n ^ 2 * s))) / ε n ^ 2) with hF
  have hmeas : ∀ n, Measurable fun x => ENNReal.ofReal ((1 + ε n ^ 2 * s) *
      klFun ((1 + ε n * f₀ x) ^ 2 / (1 + ε n ^ 2 * s))) := by
    intro n
    have : Measurable fun x => (1 + ε n ^ 2 * s) *
        klFun ((1 + ε n * f₀ x) ^ 2 / (1 + ε n ^ 2 * s)) := by
      have := continuous_klFun
      have := hf₀cont
      fun_prop
    exact this.ennreal_ofReal
  -- each lintegral is bounded by `ofReal (2 C) * G`
  have hbound : ∀ n, ∫⁻ x, F n x ∂ν ≤ ENNReal.ofReal (2 * C) * G := by
    intro n
    have hlipn : LocallyLipschitz fun x => 1 + ε n * f₀ x :=
      locallyLipschitz_const_add_mul hf₀lip 1 (ε n)
    have hmemn : MemLp (fun x => 1 + ε n * f₀ x) 2 ν := by
      have h1 : MemLp (fun _ : E => (1 : ℝ)) 2 ν := memLp_const 1
      have h2 : MemLp (fun x => ε n * f₀ x) 2 ν := hf₀m.const_mul (ε n)
      exact h1.add h2
    have hn := h (fun x => 1 + ε n * f₀ x) hlipn hmemn
    have hm := integral_sq_one_add_mul hf₀m hint0 (ε n)
    rw [gradEnergy_one_add_mul f₀ (hεpos n).ne'] at hn
    unfold entropyFun at hn
    simp only [hm] at hn
    have hFeq : ∀ x, F n x = ENNReal.ofReal (1 / ε n ^ 2) *
        ENNReal.ofReal ((1 + ε n ^ 2 * s) *
          klFun ((1 + ε n * f₀ x) ^ 2 / (1 + ε n ^ 2 * s))) := by
      intro x
      rw [hF]
      simp only
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    simp_rw [hFeq]
    rw [lintegral_const_mul _ (hmeas n)]
    calc ENNReal.ofReal (1 / ε n ^ 2) * ∫⁻ x, ENNReal.ofReal ((1 + ε n ^ 2 * s) *
          klFun ((1 + ε n * f₀ x) ^ 2 / (1 + ε n ^ 2 * s))) ∂ν
        ≤ ENNReal.ofReal (1 / ε n ^ 2) *
            (ENNReal.ofReal (2 * C) * (ENNReal.ofReal (ε n ^ 2) * G)) := by gcongr
      _ = ENNReal.ofReal (2 * C) * G := by
          have hε2 : 0 < ε n ^ 2 := pow_pos (hεpos n) 2
          have e1 : ENNReal.ofReal (1 / ε n ^ 2) * ENNReal.ofReal (ε n ^ 2) = 1 := by
            rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hε2.ne',
              ENNReal.ofReal_one]
          calc ENNReal.ofReal (1 / ε n ^ 2) *
                (ENNReal.ofReal (2 * C) * (ENNReal.ofReal (ε n ^ 2) * G))
              = (ENNReal.ofReal (1 / ε n ^ 2) * ENNReal.ofReal (ε n ^ 2)) *
                (ENNReal.ofReal (2 * C) * G) := by ring
            _ = ENNReal.ofReal (2 * C) * G := by rw [e1, one_mul]
  -- pointwise limits
  have hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (ENNReal.ofReal (2 * f₀ x ^ 2))) := by
    intro x
    exact (ENNReal.tendsto_ofReal
      ((tendsto_linearized_entropy (f₀ x) s hs0).comp hεt))
  have hFmeas : ∀ n, Measurable (F n) := fun n => by
    have := continuous_klFun
    have := hf₀cont
    exact (by fun_prop : Measurable fun x => ((1 + ε n ^ 2 * s) *
      klFun ((1 + ε n * f₀ x) ^ 2 / (1 + ε n ^ 2 * s))) / ε n ^ 2).ennreal_ofReal
  have hfatou := lintegral_liminf_le (μ := ν) (u := (atTop : Filter ℕ)) hFmeas
  have hl : ∀ x, liminf (fun n => F n x) atTop = ENNReal.ofReal (2 * f₀ x ^ 2) :=
    fun x => (hlim x).liminf_eq
  simp only [hl] at hfatou
  have hup : liminf (fun n => ∫⁻ x, F n x ∂ν) atTop ≤ ENNReal.ofReal (2 * C) * G := by
    have hfreq : ∃ᶠ n in (atTop : Filter ℕ), ∫⁻ x, F n x ∂ν ≤ ENNReal.ofReal (2 * C) * G :=
      (Filter.Eventually.of_forall hbound).frequently
    exact Filter.liminf_le_of_frequently_le' hfreq
  have h2 : ∫⁻ x, ENNReal.ofReal (2 * f₀ x ^ 2) ∂ν = 2 * ∫⁻ x, ENNReal.ofReal (f₀ x ^ 2) ∂ν := by
    have : ∀ x, ENNReal.ofReal (2 * f₀ x ^ 2) = 2 * ENNReal.ofReal (f₀ x ^ 2) := fun x => by
      rw [ENNReal.ofReal_mul (by norm_num)]; simp
    simp_rw [this]
    exact lintegral_const_mul' _ _ (by norm_num)
  have h3 : ENNReal.ofReal (2 * C) = 2 * ENNReal.ofReal C := by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  have h4 : 2 * ∫⁻ x, ENNReal.ofReal (f₀ x ^ 2) ∂ν ≤ 2 * (ENNReal.ofReal C * G) := by
    calc 2 * ∫⁻ x, ENNReal.ofReal (f₀ x ^ 2) ∂ν = ∫⁻ x, ENNReal.ofReal (2 * f₀ x ^ 2) ∂ν := h2.symm
      _ ≤ _ := hfatou
      _ ≤ ENNReal.ofReal (2 * C) * G := hup
      _ = 2 * (ENNReal.ofReal C * G) := by rw [h3, mul_assoc]
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h4

end LSIImpliesPI

end CvxBody
