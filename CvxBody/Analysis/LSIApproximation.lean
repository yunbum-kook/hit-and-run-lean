module
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import CvxBody.Analysis.FunctionalInequalities

@[expose] public section


/-!
# Approximation of the log-Sobolev inequality

A log-Sobolev bound only has to be checked on globally Lipschitz functions that are bounded and
bounded below by a positive constant, provided the measure is absolutely continuous with respect
to Lebesgue measure (`isLogSobolevBound_of_positive_lipschitz`). The proof has three steps.

1. `entropyFun_le_liminf`: lower semicontinuity of `entropyFun` along pointwise convergence with an
   integrable dominating function (dominated convergence for the mean, Fatou for the integral).
2. `entropyFun_sq_le_of_lipschitz_bounded`: a bounded Lipschitz `f` is approximated by the positive
   functions `√(f² + ε²)`, whose squares are `f² + ε²`; their gradients are dominated by `∇f`
   (chain rule, valid `ν`-a.e. by Rademacher's theorem and `ν ≪ volume`).
3. `isLogSobolevBound_of_positiveLipschitzLogSobolev`: a locally Lipschitz `f ∈ L²(ν)` is
   approximated by `f χ_R`, with `χ_R` a smooth cutoff equal to `1` on `closedBall 0 R`, which is
   bounded and globally Lipschitz; `‖∇(f χ_R)‖² ≤ (1 + 1/R) ‖∇f‖² + (1 + R) (L/R)² f²`.
-/

open MeasureTheory ProbabilityTheory Filter Topology InformationTheory
open scoped ENNReal NNReal

namespace CvxBody

section LowerSemicontinuity

variable {E : Type*} [MeasurableSpace E]

/-- Lower semicontinuity of `entropyFun` along dominated pointwise convergence. -/
theorem entropyFun_le_liminf (ν : Measure E) {g : ℕ → E → ℝ} {g' G : E → ℝ}
    (hG : Integrable G ν) (hmeas : ∀ k, Measurable (g k)) (hle : ∀ k x, |g k x| ≤ G x)
    (hlim : ∀ x, Tendsto (fun k => g k x) atTop (𝓝 (g' x))) :
    entropyFun ν g' ≤ liminf (fun k => entropyFun ν (g k)) atTop := by
  set m : ℕ → ℝ := fun k => ∫ y, g k y ∂ν with hmdef
  set m' : ℝ := ∫ y, g' y ∂ν with hm'def
  have hm : Tendsto m atTop (𝓝 m') :=
    tendsto_integral_of_dominated_convergence G (fun k => (hmeas k).aestronglyMeasurable) hG
      (fun k => Eventually.of_forall (fun x => by simpa using hle k x))
      (Eventually.of_forall hlim)
  by_cases h0 : m' = 0
  · have : entropyFun ν g' = 0 := by simp [entropyFun, ← hm'def, h0]
    rw [this]; exact zero_le
  · have hmeasF : ∀ k, Measurable (fun x => ENNReal.ofReal (m k * klFun (g k x / m k))) := by
      intro k
      have := continuous_klFun
      have := hmeas k
      exact (by fun_prop : Measurable fun x => m k * klFun (g k x / m k)).ennreal_ofReal
    have hFat := lintegral_liminf_le (μ := ν) (u := (atTop : Filter ℕ)) hmeasF
    have hpt : ∀ x, liminf (fun k => ENNReal.ofReal (m k * klFun (g k x / m k))) atTop =
        ENNReal.ofReal (m' * klFun (g' x / m')) := by
      intro x
      refine Tendsto.liminf_eq (ENNReal.tendsto_ofReal ?_)
      exact hm.mul (continuous_klFun.continuousAt.tendsto.comp ((hlim x).div hm h0))
    simp only [hpt] at hFat
    exact hFat

theorem entropyFun_le_of_tendsto (ν : Measure E) {g : ℕ → E → ℝ} {g' G : E → ℝ}
    (hG : Integrable G ν) (hmeas : ∀ k, Measurable (g k)) (hle : ∀ k x, |g k x| ≤ G x)
    (hlim : ∀ x, Tendsto (fun k => g k x) atTop (𝓝 (g' x))) {b : ℕ → ℝ≥0∞} {B : ℝ≥0∞}
    (hb : ∀ k, entropyFun ν (g k) ≤ b k) (hbt : Tendsto b atTop (𝓝 B)) :
    entropyFun ν g' ≤ B :=
  (entropyFun_le_liminf ν hG hmeas hle hlim).trans
    ((liminf_le_liminf (Eventually.of_forall hb)).trans_eq hbt.liminf_eq)

end LowerSemicontinuity

section Rademacher

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Rademacher's theorem for locally Lipschitz functions. -/
theorem ae_differentiableAt_of_locallyLipschitz {f : E → ℝ} (hf : LocallyLipschitz f)
    (μ : Measure E) [μ.IsAddHaarMeasure] : ∀ᵐ x ∂μ, DifferentiableAt ℝ f x := by
  have h : ∀ r : ℕ, ∀ᵐ x ∂μ, x ∈ Metric.closedBall (0 : E) r →
      DifferentiableWithinAt ℝ f (Metric.closedBall 0 r) x := by
    intro r
    obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_closedBall (0 : E) (r : ℝ)) hf.locallyLipschitzOn
    exact hK.ae_differentiableWithinAt_of_mem
  filter_upwards [ae_all_iff.2 h] with x hx
  obtain ⟨r, hr⟩ := exists_nat_gt ‖x‖
  have hxr : x ∈ Metric.ball (0 : E) r := by simpa using hr
  exact (hx r (Metric.ball_subset_closedBall hxr)).differentiableAt
    (Metric.closedBall_mem_nhds_of_mem hxr)

end Rademacher

section SqrtShift

theorem hasDerivAt_sqrt_sq_add {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    HasDerivAt (fun s : ℝ => √(s ^ 2 + ε ^ 2)) (s / √(s ^ 2 + ε ^ 2)) s := by
  have hpos : s ^ 2 + ε ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + ε ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).add_const (ε ^ 2)
  have h2 := h1.sqrt hpos
  convert h2 using 1
  have : √(s ^ 2 + ε ^ 2) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  field_simp

theorem abs_div_sqrt_sq_add_le {ε : ℝ} (hε : 0 < ε) (s : ℝ) : |s / √(s ^ 2 + ε ^ 2)| ≤ 1 := by
  have hpos : 0 < √(s ^ 2 + ε ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [abs_div, abs_of_pos hpos, div_le_one hpos]
  exact Real.abs_le_sqrt (by linarith [sq_nonneg ε])

theorem lipschitzWith_sqrt_sq_add {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith 1 (fun s : ℝ => √(s ^ 2 + ε ^ 2)) := by
  refine lipschitzWith_of_nnnorm_deriv_le (fun s => (hasDerivAt_sqrt_sq_add hε s).differentiableAt)
    (fun s => ?_)
  rw [(hasDerivAt_sqrt_sq_add hε s).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
    NNReal.coe_one]
  exact abs_div_sqrt_sq_add_le hε s

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem gradEnergy_sqrt_sq_add_le (ν : Measure E) {f : E → ℝ}
    (hdiff : ∀ᵐ x ∂ν, DifferentiableAt ℝ f x) {ε : ℝ} (hε : 0 < ε) :
    gradEnergy ν (fun x => √(f x ^ 2 + ε ^ 2)) ≤ gradEnergy ν f := by
  refine lintegral_mono_ae ?_
  filter_upwards [hdiff] with x hx
  apply ENNReal.ofReal_le_ofReal
  have h := (hasDerivAt_sqrt_sq_add hε (f x)).comp_hasFDerivAt x hx.hasFDerivAt
  have h' : fderiv ℝ (fun x => √(f x ^ 2 + ε ^ 2)) x
      = (f x / √(f x ^ 2 + ε ^ 2)) • fderiv ℝ f x := h.fderiv
  rw [h', norm_smul, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (by positivity)
    (mul_le_of_le_one_left (norm_nonneg _) (abs_div_sqrt_sq_add_le hε _)) 2

end SqrtShift

section BoundedLipschitz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The log-Sobolev inequality tested only on globally Lipschitz functions that are bounded and
bounded below by a positive constant. -/
def PositiveLipschitzLogSobolev (ν : Measure E) (C : ℝ) : Prop :=
  ∀ f : E → ℝ, (∃ K : ℝ≥0, LipschitzWith K f) → (∃ ε > 0, ∀ x, ε ≤ f x) →
    (∃ M, ∀ x, f x ≤ M) →
      entropyFun ν (fun x => f x ^ 2) ≤ ENNReal.ofReal (2 * C) * gradEnergy ν f

/-- Step 2: pass from positive to arbitrary bounded Lipschitz functions via `√(f² + ε²)`. -/
theorem entropyFun_sq_le_of_lipschitz_bounded (μ : Measure E) [μ.IsAddHaarMeasure]
    (ν : Measure E) [IsProbabilityMeasure ν] (hν : ν ≪ μ) {C : ℝ}
    (h : PositiveLipschitzLogSobolev ν C) {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    entropyFun ν (fun x => f x ^ 2) ≤ ENNReal.ofReal (2 * C) * gradEnergy ν f := by
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hεpos : ∀ n, 0 < ε n := fun n => by simp only [hε]; positivity
  have hεle : ∀ n, ε n ≤ 1 := fun n => by
    simp only [hε]
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdiff : ∀ᵐ x ∂ν, DifferentiableAt ℝ f x :=
    hν.ae_le (ae_differentiableAt_of_locallyLipschitz hf.locallyLipschitz μ)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hbound : ∀ n, entropyFun ν (fun x => f x ^ 2 + ε n ^ 2) ≤
      ENNReal.ofReal (2 * C) * gradEnergy ν f := by
    intro n
    have hsq : (fun x => (√(f x ^ 2 + ε n ^ 2)) ^ 2) = fun x => f x ^ 2 + ε n ^ 2 := by
      funext x; exact Real.sq_sqrt (by positivity)
    have hlip : LipschitzWith (1 * K) (fun x => √(f x ^ 2 + ε n ^ 2)) :=
      (lipschitzWith_sqrt_sq_add (hεpos n)).comp hf
    have h1 := h (fun x => √(f x ^ 2 + ε n ^ 2)) ⟨_, hlip⟩
      ⟨ε n, hεpos n, fun x => by
        calc ε n = √(ε n ^ 2) := (Real.sqrt_sq (hεpos n).le).symm
          _ ≤ √(f x ^ 2 + ε n ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (f x)])⟩
      ⟨M + 1, fun x => by
        refine Real.sqrt_le_iff.2 ⟨by linarith, ?_⟩
        have h2 : f x ^ 2 ≤ M ^ 2 := by
          have := hM x
          calc f x ^ 2 = |f x| ^ 2 := (sq_abs _).symm
            _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        have h3 : ε n ^ 2 ≤ 1 := by
          have := hεle n; have := hεpos n; nlinarith
        nlinarith⟩
    rw [hsq] at h1
    exact h1.trans (by gcongr; exact gradEnergy_sqrt_sq_add_le ν hdiff (hεpos n))
  refine entropyFun_le_of_tendsto ν (g := fun n x => f x ^ 2 + ε n ^ 2) (G := fun _ => M ^ 2 + 1)
    (integrable_const _) (fun n => ?_) (fun n x => ?_) (fun x => ?_) hbound tendsto_const_nhds
  · have := hf.continuous
    fun_prop
  · have h2 : f x ^ 2 ≤ M ^ 2 := by
      calc f x ^ 2 = |f x| ^ 2 := (sq_abs _).symm
        _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
    have h3 : ε n ^ 2 ≤ 1 := by
      have := hεle n; have := hεpos n; nlinarith
    rw [abs_of_nonneg (by positivity)]
    linarith
  · have := (hεt.pow 2).const_add (f x ^ 2)
    simpa using this

end BoundedLipschitz

section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A family of smooth cutoff functions `χ R`, equal to `1` on `closedBall 0 R`, supported in
`closedBall 0 (2R)`, with gradient bounded by `L / R`. -/
theorem exists_cutoff (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ (L : ℝ) (χ : ℝ → E → ℝ), ∀ R, 0 < R →
      ContDiff ℝ 1 (χ R) ∧ (∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧ (∀ x, ‖x‖ ≤ R → χ R x = 1) ∧
      (∀ x, 2 * R ≤ ‖x‖ → χ R x = 0) ∧ (∀ x, ‖fderiv ℝ (χ R) x‖ ≤ L / R) ∧
      (∃ K : ℝ≥0, LipschitzWith K (χ R)) := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) b.hasCompactSupport
    (b.contDiff (n := 1)) one_ne_zero
  refine ⟨L, fun R x => b (R⁻¹ • x), fun R hR => ?_⟩
  have hcd : ContDiff ℝ 1 (fun x => b (R⁻¹ • x)) :=
    (b.contDiff (n := 1)).comp (contDiff_const_smul R⁻¹)
  have hlip : LipschitzWith (L * ‖R⁻¹‖₊) (fun x => b (R⁻¹ • x)) := hL.comp (lipschitzWith_smul R⁻¹)
  have hnorm : ∀ x : E, ‖R⁻¹ • x‖ = R⁻¹ * ‖x‖ := fun x => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
  beta_reduce
  refine ⟨hcd, fun x => ⟨b.nonneg, b.le_one⟩, fun x hx => ?_, fun x hx => ?_, fun x => ?_,
    ⟨_, hlip⟩⟩
  · apply b.one_of_mem_closedBall
    rw [mem_closedBall_zero_iff, hnorm]
    show R⁻¹ * ‖x‖ ≤ 1
    rw [inv_mul_le_iff₀ hR]; linarith
  · apply b.zero_of_le_dist
    rw [dist_zero_right, hnorm]
    show 2 ≤ R⁻¹ * ‖x‖
    rw [le_inv_mul_iff₀ hR]; linarith
  · have := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := x)
    refine this.trans ?_
    simp [div_eq_mul_inv, abs_of_pos hR]


/-- A locally Lipschitz function times a bounded Lipschitz cutoff with bounded support is
globally Lipschitz. -/
theorem exists_lipschitzWith_mul_cutoff {f χ : E → ℝ} (hf : LocallyLipschitz f) {Lχ : ℝ≥0}
    (hχ : LipschitzWith Lχ χ) (hχ1 : ∀ x, |χ x| ≤ 1) {ρ : ℝ} (hsupp : ∀ x, ρ ≤ ‖x‖ → χ x = 0) :
    ∃ (K : ℝ≥0) (M : ℝ), LipschitzWith K (fun x => f x * χ x) ∧ ∀ x, |f x * χ x| ≤ M := by
  set B : Set E := Metric.closedBall (0 : E) (ρ + 1) with hB
  have hBc : IsCompact B := isCompact_closedBall _ _
  obtain ⟨Kf, hKf⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hBc
    hf.locallyLipschitzOn
  obtain ⟨Mf, hMf⟩ := hBc.exists_bound_of_continuousOn hf.continuous.continuousOn
  set M : ℝ := max Mf 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hbd : ∀ x, |f x * χ x| ≤ M := by
    intro x
    by_cases hx : ρ ≤ ‖x‖
    · rw [hsupp x hx]; simpa using hM0
    · have hxB : x ∈ B := by
        rw [hB, mem_closedBall_zero_iff]; linarith [not_le.1 hx]
      rw [abs_mul]
      calc |f x| * |χ x| ≤ |f x| * 1 := by gcongr; exact hχ1 x
        _ ≤ Mf := by simpa using hMf x hxB
        _ ≤ M := le_max_left _ _
  have hloc : ∀ x ∈ B, ∀ y ∈ B,
      dist (f x * χ x) (f y * χ y) ≤ (M * Lχ + Kf) * dist x y := by
    intro x hx y hy
    have h1 : f x * χ x - f y * χ y = f x * (χ x - χ y) + χ y * (f x - f y) := by ring
    have h2 : |f x| ≤ M := (by simpa using hMf x hx : |f x| ≤ Mf).trans (le_max_left _ _)
    have h3 : dist (χ x) (χ y) ≤ Lχ * dist x y := hχ.dist_le_mul x y
    have h4 : dist (f x) (f y) ≤ Kf * dist x y := hKf.dist_le_mul x hx y hy
    rw [Real.dist_eq, h1]
    rw [Real.dist_eq] at h3 h4
    calc |f x * (χ x - χ y) + χ y * (f x - f y)|
        ≤ |f x * (χ x - χ y)| + |χ y * (f x - f y)| := abs_add_le _ _
      _ = |f x| * |χ x - χ y| + |χ y| * |f x - f y| := by rw [abs_mul, abs_mul]
      _ ≤ M * (Lχ * dist x y) + 1 * (Kf * dist x y) := by
          gcongr
          · exact hχ1 y
      _ = (M * Lχ + Kf) * dist x y := by ring
  refine ⟨Real.toNNReal (max (M * Lχ + Kf) (2 * M)), M, LipschitzWith.of_dist_le' fun x y => ?_, hbd⟩
  have hK1 : (M * Lχ + Kf) ≤ max (M * Lχ + Kf) (2 * M) := le_max_left _ _
  have hK2 : 2 * M ≤ max (M * Lχ + Kf) (2 * M) := le_max_right _ _
  have hd0 : 0 ≤ dist x y := dist_nonneg
  by_cases hxy : 1 ≤ dist x y
  · calc dist (f x * χ x) (f y * χ y) ≤ |f x * χ x| + |f y * χ y| := by
          rw [Real.dist_eq]; exact abs_sub _ _
      _ ≤ 2 * M := by linarith [hbd x, hbd y]
      _ ≤ 2 * M * dist x y := by nlinarith
      _ ≤ _ := by gcongr
  · have hxy' := not_le.1 hxy
    by_cases hx : ρ ≤ ‖x‖
    · by_cases hy : ρ ≤ ‖y‖
      · rw [hsupp x hx, hsupp y hy]
        simp only [mul_zero, dist_self]
        positivity
      · have hyB : y ∈ B := by
          rw [hB, mem_closedBall_zero_iff]; linarith [not_le.1 hy]
        have hxB : x ∈ B := by
          rw [hB, mem_closedBall_zero_iff]
          have : ‖x‖ ≤ ‖y‖ + dist x y := by
            have := norm_le_norm_add_norm_sub' x y
            rw [dist_eq_norm]; linarith
          linarith [not_le.1 hy]
        exact (hloc x hxB y hyB).trans (by gcongr)
    · have hxB : x ∈ B := by
        rw [hB, mem_closedBall_zero_iff]; linarith [not_le.1 hx]
      have hyB : y ∈ B := by
        rw [hB, mem_closedBall_zero_iff]
        have : ‖y‖ ≤ ‖x‖ + dist x y := by
          have := norm_le_norm_add_norm_sub' y x
          rw [dist_comm, dist_eq_norm]; linarith
        linarith [not_le.1 hx]
      exact (hloc x hxB y hyB).trans (by gcongr)


theorem add_sq_le_of_pos {A B : ℝ} (t : ℝ) (ht : 0 < t) :
    (A + B) ^ 2 ≤ (1 + t⁻¹) * A ^ 2 + (1 + t) * B ^ 2 := by
  have h : t⁻¹ * A ^ 2 + t * B ^ 2 - 2 * A * B = t⁻¹ * (A - t * B) ^ 2 := by
    field_simp
    ring
  have h2 : 0 ≤ t⁻¹ * (A - t * B) ^ 2 := by positivity
  nlinarith

omit [FiniteDimensional ℝ E] in
/-- Pointwise gradient bound for the product of `f` with a cutoff. -/
theorem norm_fderiv_mul_cutoff_sq_le {f χ : E → ℝ} {x : E} {c t : ℝ}
    (hf : DifferentiableAt ℝ f x) (hχ : DifferentiableAt ℝ χ x) (h0 : 0 ≤ χ x) (h1 : χ x ≤ 1)
    (hc : ‖fderiv ℝ χ x‖ ≤ c) (ht : 0 < t) :
    ‖fderiv ℝ (fun y => f y * χ y) x‖ ^ 2 ≤
      (1 + t⁻¹) * ‖fderiv ℝ f x‖ ^ 2 + (1 + t) * (c ^ 2 * f x ^ 2) := by
  have hm : fderiv ℝ (fun y => f y * χ y) x = f x • fderiv ℝ χ x + χ x • fderiv ℝ f x :=
    (hf.hasFDerivAt.mul hχ.hasFDerivAt).fderiv
  rw [hm]
  have h2 : ‖f x • fderiv ℝ χ x + χ x • fderiv ℝ f x‖ ≤ ‖fderiv ℝ f x‖ + |f x| * c := by
    calc _ ≤ ‖f x • fderiv ℝ χ x‖ + ‖χ x • fderiv ℝ f x‖ := norm_add_le _ _
      _ = |f x| * ‖fderiv ℝ χ x‖ + χ x * ‖fderiv ℝ f x‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0]
      _ ≤ |f x| * c + 1 * ‖fderiv ℝ f x‖ := by
          gcongr
      _ = _ := by ring
  have h3 := add_sq_le_of_pos (A := ‖fderiv ℝ f x‖) (B := |f x| * c) t ht
  have h4 : (|f x| * c) ^ 2 = c ^ 2 * f x ^ 2 := by rw [mul_pow, sq_abs]; ring
  rw [h4] at h3
  exact (pow_le_pow_left₀ (norm_nonneg _) h2 2).trans h3

end Cutoff

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Step 3: cutoff approximation, for a general finite-dimensional inner product space with an
additive Haar measure `μ` dominating `ν`. -/
theorem isLogSobolevBound_of_positiveLipschitzLogSobolev (μ : Measure E) [μ.IsAddHaarMeasure]
    (ν : Measure E) [IsProbabilityMeasure ν] (hν : ν ≪ μ) {C : ℝ}
    (h : PositiveLipschitzLogSobolev ν C) : IsLogSobolevBound ν C := by
  intro f hf hfm
  set a : ℝ≥0∞ := ENNReal.ofReal (2 * C) with ha
  have hatop : a ≠ ⊤ := ENNReal.ofReal_ne_top
  set G : ℝ≥0∞ := gradEnergy ν f with hGdef
  by_cases hGtop : G = ⊤ ∧ a ≠ 0
  · rw [hGtop.1, ENNReal.mul_top hGtop.2]; exact le_top
  have hG' : a = 0 ∨ G ≠ ⊤ := by
    by_cases h0 : a = 0
    · exact Or.inl h0
    · exact Or.inr fun hGt => hGtop ⟨hGt, h0⟩
  obtain ⟨L, χ, hχ⟩ := exists_cutoff E
  set I : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂ν with hIdef
  have hI : I ≠ ⊤ := hfm.integrable_sq.lintegral_lt_top.ne
  have hfc : Continuous f := hf.continuous
  have hdiff : ∀ᵐ x ∂ν, DifferentiableAt ℝ f x :=
    hν.ae_le (ae_differentiableAt_of_locallyLipschitz hf μ)
  set g : ℕ → E → ℝ := fun n x => f x * χ ((n : ℝ) + 1) x with hg
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
  have hent : ∀ n : ℕ, entropyFun ν (fun x => g n x ^ 2) ≤
      a * (ENNReal.ofReal (1 + ((n : ℝ) + 1)⁻¹) * G +
        ENNReal.ofReal ((1 + ((n : ℝ) + 1)) * (L / ((n : ℝ) + 1)) ^ 2) * I) := by
    intro n
    obtain ⟨-, h01, -, hsupp, -, Lχ, hLχ⟩ := hχ ((n : ℝ) + 1) (hpos n)
    obtain ⟨K, M, hK, hM⟩ := exists_lipschitzWith_mul_cutoff hf hLχ
      (fun x => by rw [abs_of_nonneg (h01 x).1]; exact (h01 x).2) hsupp
    exact (entropyFun_sq_le_of_lipschitz_bounded μ ν hν h hK hM).trans (by gcongr; exact hgrad n)
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
  refine entropyFun_le_of_tendsto ν (g := fun n x => g n x ^ 2) (G := fun x => f x ^ 2)
    hfm.integrable_sq (fun n => ?_) (fun n x => ?_) (fun x => ?_) hent hb
  · have := hgc n
    fun_prop
  · obtain ⟨-, h01, -⟩ := hχ ((n : ℝ) + 1) (hpos n)
    rw [abs_of_nonneg (sq_nonneg _), hg]
    simp only
    rw [mul_pow]
    have : χ ((n : ℝ) + 1) x ^ 2 ≤ 1 := by
      have := h01 x
      nlinarith
    nlinarith [sq_nonneg (f x), sq_nonneg (χ ((n : ℝ) + 1) x)]
  · obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    obtain ⟨-, -, h1x, -⟩ := hχ ((n : ℝ) + 1) (hpos n)
    have : ‖x‖ ≤ (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    simp only [hg, h1x x this]
    ring

/-- **Approximation of the log-Sobolev inequality by positive bounded Lipschitz functions.**
If `ν ≪ volume` is a probability measure on `ℝⁿ` and the log-Sobolev inequality with constant `C`
holds for all globally Lipschitz functions that are bounded and bounded below by a positive
constant, then `C` is a valid log-Sobolev bound for `ν` (all locally Lipschitz `f ∈ L²(ν)`). -/
theorem isLogSobolevBound_of_positive_lipschitz {n : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] (hν : ν ≪ volume) {C : ℝ}
    (h : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, (∃ K : ℝ≥0, LipschitzWith K f) →
      (∃ ε > 0, ∀ x, ε ≤ f x) → (∃ M, ∀ x, f x ≤ M) →
        entropyFun ν (fun x => f x ^ 2) ≤ ENNReal.ofReal (2 * C) * gradEnergy ν f) :
    IsLogSobolevBound ν C :=
  isLogSobolevBound_of_positiveLipschitzLogSobolev volume ν hν h

end Main

end CvxBody
