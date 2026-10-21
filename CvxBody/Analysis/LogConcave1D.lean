module
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Interval
public import Mathlib.Topology.MetricSpace.Thickening
public import CvxBody.External.OAI.KLS.Convexity.LogConcavity

@[expose] public section


/-!
# One-dimensional isoperimetry for log-concave probability measures

For a log-concave probability density `ρ` on `ℝ` with measure `ν = ρ dx`, we prove
`isoperimetry_log_concave_1D`: if `ν(|x - m| > r) ≤ 1/4`, then every measurable `S ⊆ ℝ` satisfies
`(1/16)/r · min (ν S) (1 - ν S) ≤ ν⁺(S)`, where `ν⁺ = minkowskiContent1D ν` is the outer
Minkowski content `liminf_{ε → 0+} (ν (thickening ε S) - ν S) / ε`.  The constant is `1/16`.

Proof (no localization, no quantile function, no regularity of `S`):

* Two-point log-concavity `ρ(a) ρ(d) ≤ ρ(b) ρ(c)` for `a + d = b + c`, `b, c ∈ [a, d]`
  (`mul_le_mul_of_isLogConcave`), integrated against translates, gives the cumulative inequalities
  `ρ(q) F(x) ≤ ρ(x) F(q)` and `ρ(s) T(t) ≤ ρ(t) T(s)` for `x ≤ q`, `s ≤ t`, with
  `F = ∫_{(-∞,·]} ρ` and `T = ∫_{(·,∞)} ρ` (`density_mul_cdf_le`, `density_mul_tail_le`).  At the
  median `p` they give `ρ(x) ≥ 2 ρ(p) min (F x) (T x)`, and `ρ(p) ≥ ρ(y)/2` for every `y`.
* The spread hypothesis gives `y` with `ρ(y) > 1/(4r)`, hence `ρ ≥ min(a, 1-a)/(16 r)` on the
  interval `G = {η ≤ F ≤ 1 - η}`, `η = min(a, 1-a)/4`, which carries all but mass `2η` of `ν`.
* A one-dimensional relative Brunn--Minkowski argument (`gain_in_interval`) shows that the
  `ε`-thickening of `S` adds Lebesgue measure at least `ε` inside `G` outside `S`, for all small
  `ε`, whenever `S` meets `G` and `G ∖ S` is not Lebesgue null.  Both conditions follow from the
  mass of `G`.

The measurability hypothesis on `ρ` is not needed (`withDensity_apply` holds for every density), so
`_hm` is unused; it is kept to match the intended interface.
-/

open MeasureTheory Metric Set Filter
open OAI.LeanBlast.KLS
open scoped ENNReal Topology

namespace CvxBody

/-- Outer Minkowski content of `S` for a measure `ν` on `ℝ`:
`liminf_{ε → 0+} (ν (thickening ε S) - ν S) / ε`, with the open thickening
`Metric.thickening`. -/
noncomputable def minkowskiContent1D (ν : Measure ℝ) (S : Set ℝ) : ℝ≥0∞ :=
  liminf (fun ε : ℝ => (ν (thickening ε S) - ν S) / ENNReal.ofReal ε) (𝓝[>] 0)

namespace LogConcave1D

/-- Two-point form of log-concavity: `f a f d ≤ f b f c` when `b, c ∈ [a, d]` and
`a + d = b + c`. -/
theorem mul_le_mul_of_isLogConcave {f : ℝ → ℝ} (hf : IsLogConcaveFunction f) {a b c d : ℝ}
    (hab : a ≤ b) (hbd : b ≤ d) (hac : a ≤ c) (hcd : c ≤ d) (hsum : a + d = b + c) :
    f a * f d ≤ f b * f c := by
  rcases eq_or_lt_of_le (hab.trans hbd) with had | had
  · have hb : b = a := le_antisymm (had ▸ hbd) hab
    have hc : c = a := le_antisymm (had ▸ hcd) hac
    rw [hb, hc, ← had]
  set θ : ℝ := (d - b) / (d - a) with hθ
  have hda : 0 < d - a := sub_pos.2 had
  have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.2 hbd) hda.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hda]; linarith
  have hb : θ * a + (1 - θ) * d = b := by
    rw [hθ]; field_simp; ring
  have hc : (1 - θ) * a + (1 - (1 - θ)) * d = c := by
    have : (1 - θ) * a + (1 - (1 - θ)) * d = a + d - (θ * a + (1 - θ) * d) := by ring
    rw [this, hb]; linarith
  rcases eq_or_lt_of_le hθ0 with h0 | h0
  · have hb' : b = d := by rw [← hb, ← h0]; ring
    have hc' : c = a := by linarith
    rw [hb', hc', mul_comm]
  rcases eq_or_lt_of_le hθ1 with h1 | h1
  · have hb' : b = a := by rw [← hb, h1]; ring
    have hc' : c = d := by linarith
    rw [hb', hc']
  have e1 := hf.rpow_le a d h0 h1
  have e2 := hf.rpow_le a d (sub_pos.2 h1) (by linarith)
  simp only [smul_eq_mul] at e1 e2
  rw [hb] at e1
  rw [hc] at e2
  have n1 := hf.nonnegative a
  have n2 := hf.nonnegative d
  calc f a * f d = (f a ^ θ * f d ^ (1 - θ)) * (f a ^ (1 - θ) * f d ^ (1 - (1 - θ))) := by
        have h1' : f a ^ θ * f a ^ (1 - θ) = f a := by
          rw [← Real.rpow_add' n1 (by linarith)]; simp
        have h2' : f d ^ (1 - θ) * f d ^ (1 - (1 - θ)) = f d := by
          rw [← Real.rpow_add' n2 (by linarith)]; simp
        calc f a * f d = (f a ^ θ * f a ^ (1 - θ)) * (f d ^ (1 - θ) * f d ^ (1 - (1 - θ))) := by
              rw [h1', h2']
          _ = _ := by ring
    _ ≤ f b * f c := by
        apply mul_le_mul e1 e2 (by positivity) (hf.nonnegative b)


theorem integral_Iic_add_const (f : ℝ → ℝ) (x c : ℝ) :
    ∫ y in Iic x, f (y + c) = ∫ y in Iic (x + c), f y := by
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic,
    ← integral_add_right_eq_self (fun y => (Iic (x + c)).indicator f y) c]
  congr 1; ext y
  simp [indicator]

theorem integral_Ioi_add_const (f : ℝ → ℝ) (x c : ℝ) :
    ∫ y in Ioi x, f (y + c) = ∫ y in Ioi (x + c), f y := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (fun y => (Ioi (x + c)).indicator f y) c]
  congr 1; ext y
  simp [indicator]

section ratio

variable {ρ : ℝ → ℝ}

/-- Left cumulative inequality: `ρ(q) F(x) ≤ ρ(x) F(q)` for `x ≤ q`. -/
theorem density_mul_cdf_le (hρ : IsLogConcaveFunction ρ) (hi : Integrable ρ) {x q : ℝ}
    (hxq : x ≤ q) :
    ρ q * ∫ y in Iic x, ρ y ≤ ρ x * ∫ y in Iic q, ρ y := by
  have h1 : ρ q * ∫ y in Iic x, ρ y = ∫ y in Iic x, ρ q * ρ y := by
    rw [integral_const_mul]
  have h2 : ρ x * ∫ y in Iic q, ρ y = ∫ y in Iic x, ρ x * ρ (y + (q - x)) := by
    rw [integral_const_mul, integral_Iic_add_const]; simp
  rw [h1, h2]
  apply setIntegral_mono_on
  · exact (hi.integrableOn).const_mul _
  · exact ((hi.comp_add_right (q - x)).const_mul _).integrableOn
  · exact measurableSet_Iic
  · intro y hy
    have hy : y ≤ x := hy
    have := mul_le_mul_of_isLogConcave hρ (a := y) (b := x) (c := y + (q - x)) (d := q)
      hy hxq (by linarith) (by linarith) (by ring)
    linarith [mul_comm (ρ y) (ρ q), mul_comm (ρ x) (ρ (y + (q - x)))]

/-- Right cumulative inequality: `ρ(s) T(t) ≤ ρ(t) T(s)` for `s ≤ t`, with `T(u) = ∫_{(u, ∞)} ρ`. -/
theorem density_mul_tail_le (hρ : IsLogConcaveFunction ρ) (hi : Integrable ρ) {s t : ℝ}
    (hst : s ≤ t) :
    ρ s * ∫ y in Ioi t, ρ y ≤ ρ t * ∫ y in Ioi s, ρ y := by
  have h1 : ρ s * ∫ y in Ioi t, ρ y = ∫ y in Ioi t, ρ s * ρ y := by
    rw [integral_const_mul]
  have h2 : ρ t * ∫ y in Ioi s, ρ y = ∫ y in Ioi t, ρ t * ρ (y + (s - t)) := by
    rw [integral_const_mul, integral_Ioi_add_const]; simp
  rw [h1, h2]
  apply setIntegral_mono_on
  · exact (hi.integrableOn).const_mul _
  · exact ((hi.comp_add_right (s - t)).const_mul _).integrableOn
  · exact measurableSet_Ioi
  · intro y hy
    have hy : t < y := hy
    have := mul_le_mul_of_isLogConcave hρ (a := s) (b := t) (c := y + (s - t)) (d := y)
      hst hy.le (by linarith) (by linarith) (by ring)
    linarith [mul_comm (ρ y) (ρ s), mul_comm (ρ t) (ρ (y + (s - t)))]

end ratio



/-- One-dimensional relative Brunn--Minkowski: inside `G = [g₀, g₁]`, the `ε`-thickening of a set
`S` meeting `G` adds Lebesgue measure at least `ε` outside `S`, unless `G ∖ S` has measure
less than `ε`. -/
theorem gain_in_interval {g₀ g₁ ε : ℝ} {S : Set ℝ}
    (hne : (S ∩ Icc g₀ g₁).Nonempty)
    (hvol : ENNReal.ofReal ε ≤ volume (Icc g₀ g₁ \ S)) :
    ENNReal.ofReal ε ≤ volume ((thickening ε S \ S) ∩ Icc g₀ g₁) := by
  set G : Set ℝ := Icc g₀ g₁ with hG
  set W : Set ℝ := S ∩ G with hW
  have hWthick : thickening ε W ⊆ thickening ε S :=
    thickening_subset_of_subset ε inter_subset_left
  have hIoo : ∀ a b : ℝ, Ioo a b ⊆ (thickening ε S \ S) ∩ G → b - a = ε →
      ENNReal.ofReal ε ≤ volume ((thickening ε S \ S) ∩ G) := by
    intro a b h hb
    calc ENNReal.ofReal ε = volume (Ioo a b) := by rw [Real.volume_Ioo, hb]
      _ ≤ _ := measure_mono h
  by_cases hcase : ∃ z ∈ G, z ∉ thickening ε W
  · obtain ⟨z, hzG, hz⟩ := hcase
    have hz' : ∀ w ∈ W, ε ≤ |z - w| := by
      intro w hw
      by_contra h
      push Not at h
      exact hz (mem_thickening_iff.2 ⟨w, hw, by rwa [Real.dist_eq]⟩)
    by_cases h1 : ∃ w ∈ W, w < z
    · obtain ⟨w₀, hw₀, hw₀z⟩ := h1
      set W₁ : Set ℝ := {w | w ∈ W ∧ w ≤ z - ε} with hW₁
      have hw₀1 : w₀ ∈ W₁ := by
        refine ⟨hw₀, ?_⟩
        have := hz' w₀ hw₀
        rw [abs_of_pos (by linarith)] at this
        linarith
      have hne1 : W₁.Nonempty := ⟨w₀, hw₀1⟩
      have hbdd : BddAbove W₁ := ⟨z - ε, fun w hw => hw.2⟩
      set s := sSup W₁ with hs
      have hsle : s ≤ z - ε := csSup_le hne1 (fun w hw => hw.2)
      have hg₀s : g₀ ≤ s := by
        have := le_csSup hbdd hw₀1
        exact le_trans hw₀.2.1 this
      refine hIoo s (s + ε) ?_ (by ring)
      intro t ht
      obtain ⟨hts, hts'⟩ := ht
      have htG : t ∈ G := ⟨by linarith, by linarith [hzG.2]⟩
      refine ⟨⟨?_, ?_⟩, htG⟩
      · obtain ⟨w, hw, hw'⟩ := exists_lt_of_lt_csSup hne1 (show t - ε < s by linarith)
        refine mem_thickening_iff.2 ⟨w, hw.1.1, ?_⟩
        have : w ≤ s := le_csSup hbdd hw
        rw [Real.dist_eq, abs_of_pos (by linarith)]
        linarith
      · intro htS
        have htW : t ∈ W := ⟨htS, htG⟩
        have := hz' t htW
        rw [abs_of_pos (by linarith)] at this
        have : t ∈ W₁ := ⟨htW, by linarith⟩
        have := le_csSup hbdd this
        linarith
    · push Not at h1
      have hzw : ∀ w ∈ W, z + ε ≤ w := by
        intro w hw
        have := hz' w hw
        have h2 := h1 w hw
        rw [abs_of_nonpos (by linarith)] at this
        linarith
      have hne1 : W.Nonempty := hne
      have hbdd : BddBelow W := ⟨z, fun w hw => by linarith [h1 w hw]⟩
      set s := sInf W with hs
      have hsge : z + ε ≤ s := le_csInf hne1 hzw
      obtain ⟨w₀, hw₀⟩ := hne1
      have hsg₁ : s ≤ g₁ := le_trans (csInf_le hbdd hw₀) hw₀.2.2
      refine hIoo (s - ε) s ?_ (by ring)
      intro t ht
      obtain ⟨hts, hts'⟩ := ht
      have htG : t ∈ G := ⟨by linarith [hzG.1], by linarith⟩
      refine ⟨⟨?_, ?_⟩, htG⟩
      · obtain ⟨w, hw, hw'⟩ := exists_lt_of_csInf_lt ⟨w₀, hw₀⟩ (show s < t + ε by linarith)
        refine mem_thickening_iff.2 ⟨w, hw.1, ?_⟩
        have : s ≤ w := csInf_le hbdd hw
        rw [Real.dist_eq, abs_of_neg (by linarith)]
        linarith
      · intro htS
        have htW : t ∈ W := ⟨htS, htG⟩
        have := csInf_le hbdd htW
        linarith
  · push Not at hcase
    refine le_trans hvol (measure_mono ?_)
    intro x hx
    exact ⟨⟨hWthick (hcase x hx.1), hx.2⟩, hx.1⟩



/-- The probability measure on `ℝ` with density `ρ`. -/
noncomputable abbrev densityMeasure (ρ : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (ρ x)

section cdf

variable {ρ : ℝ → ℝ}

theorem densityMeasure_apply (hρ0 : ∀ x, 0 ≤ ρ x) (hi : Integrable ρ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    densityMeasure ρ A = ENNReal.ofReal (∫ y in A, ρ y) := by
  rw [withDensity_apply _ hA, ofReal_integral_eq_lintegral_ofReal hi.integrableOn
    (Eventually.of_forall hρ0)]

theorem densityMeasure_univ (hρ0 : ∀ x, 0 ≤ ρ x) (hi : Integrable ρ) (h1 : ∫ x, ρ x = 1) :
    densityMeasure ρ univ = 1 := by
  rw [densityMeasure_apply hρ0 hi MeasurableSet.univ]
  simp [h1]

/-- The cumulative distribution function attains every value in `(0, 1)`. -/
theorem exists_cdf_eq (hρ0 : ∀ x, 0 ≤ ρ x) (hi : Integrable ρ) (h1 : ∫ x, ρ x = 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : ∃ x, ∫ y in Iic x, ρ y = t := by
  have hcont : Continuous fun x => ∫ y in Iic x, ρ y := by
    have : (fun x => ∫ y in Iic x, ρ y) =
        fun x => (∫ y in Iic 0, ρ y) + ∫ y in (0 : ℝ)..x, ρ y := by
      ext x
      rw [← intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]
      ring
    rw [this]
    exact continuous_const.add (hi.continuous_primitive 0)
  have hbot : Tendsto (fun x : ℝ => ∫ y in Iic x, ρ y) atBot (𝓝 0) :=
    tendsto_integral_Iic_zero (a := fun x : ℝ => x) (l := atBot) tendsto_id
  have htop : Tendsto (fun x : ℝ => ∫ y in Iic x, ρ y) atTop (𝓝 1) := by
    have h := (ENNReal.tendsto_toReal (ENNReal.one_ne_top)).comp
      (densityMeasure_univ hρ0 hi h1 ▸ tendsto_measure_Iic_atTop (densityMeasure ρ))
    refine h.congr (fun x => ?_)
    simp only [Function.comp]
    rw [densityMeasure_apply hρ0 hi measurableSet_Iic,
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic fun y _ => hρ0 y)]
  obtain ⟨a, ha⟩ := (hbot.eventually (gt_mem_nhds ht0)).exists
  obtain ⟨b, hb⟩ := (htop.eventually (lt_mem_nhds ht1)).exists
  exact mem_range_of_exists_le_of_exists_ge hcont ⟨a, ha.le⟩ ⟨b, hb.le⟩

end cdf


/-- **One-dimensional isoperimetry for log-concave measures.**  If the log-concave probability
density `ρ` has `ν(|x - m| > r) ≤ 1/4`, then for every measurable `S`,
`(1/16)/r · min (ν S) (1 - ν S) ≤ ν⁺(S)`. -/
theorem isoperimetry_log_concave_1D {ρ : ℝ → ℝ} (hρ : IsLogConcaveFunction ρ)
    (_hm : Measurable ρ) (hi : Integrable ρ) (h1 : ∫ x, ρ x = 1) {m r : ℝ} (hr : 0 < r)
    (hspread : densityMeasure ρ {x | r < |x - m|} ≤ 1 / 4)
    {S : Set ℝ} (hS : MeasurableSet S) :
    ENNReal.ofReal (1 / 16 / r) * min (densityMeasure ρ S) (1 - densityMeasure ρ S) ≤
      minkowskiContent1D (densityMeasure ρ) S := by
  have hρ0 := hρ.nonnegative
  set ν := densityMeasure ρ with hν
  have hνapp : ∀ {A : Set ℝ}, MeasurableSet A → ν A = ENNReal.ofReal (∫ y in A, ρ y) :=
    fun hA => densityMeasure_apply hρ0 hi hA
  have : IsProbabilityMeasure ν := ⟨densityMeasure_univ hρ0 hi h1⟩
  have hac : ν ≪ volume := withDensity_absolutelyContinuous _ _
  by_cases hS0 : ν S = 0
  · simp [hS0]
  by_cases hS1 : ν S = 1
  · simp [hS1]
  set a := (ν S).toReal with ha
  have hνS : ν S = ENNReal.ofReal a := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have ha0 : 0 < a := ENNReal.toReal_pos hS0 (measure_ne_top _ _)
  have ha1 : a < 1 := by
    have : ν S < 1 := lt_of_le_of_ne prob_le_one hS1
    have := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2 this
    simpa using this
  have hνSc : ν Sᶜ = ENNReal.ofReal (1 - a) := by
    rw [prob_compl_eq_one_sub hS, hνS, ENNReal.ofReal_sub 1 ha0.le, ENNReal.ofReal_one]
  set q : ℝ := min a (1 - a) with hq
  have hq0 : 0 < q := lt_min ha0 (by linarith)
  have hqa : q ≤ a := min_le_left _ _
  have hqa' : q ≤ 1 - a := min_le_right _ _
  set η : ℝ := q / 4 with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η < 1 / 2 := by rw [hη]; linarith
  -- cumulative distribution function facts
  set F : ℝ → ℝ := fun x => ∫ y in Iic x, ρ y with hF
  set T : ℝ → ℝ := fun x => ∫ y in Ioi x, ρ y with hT
  have hFT : ∀ x, F x + T x = 1 := by
    intro x
    have := integral_add_compl (measurableSet_Iic (a := x)) hi
    rwa [compl_Iic, h1] at this
  have hFmono : Monotone F := by
    intro x x' hxx
    exact setIntegral_mono_set hi.integrableOn (Eventually.of_forall hρ0)
      (Iic_subset_Iic.2 hxx).eventuallyLE
  have hF0 : ∀ x, 0 ≤ F x := fun x => setIntegral_nonneg measurableSet_Iic fun y _ => hρ0 y
  have hT0 : ∀ x, 0 ≤ T x := fun x => setIntegral_nonneg measurableSet_Ioi fun y _ => hρ0 y
  obtain ⟨p, hp⟩ := exists_cdf_eq hρ0 hi h1 (t := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨g₀, hg₀⟩ := exists_cdf_eq hρ0 hi h1 (t := η) hη0 (by linarith)
  obtain ⟨g₁, hg₁⟩ := exists_cdf_eq hρ0 hi h1 (t := 1 - η) (by linarith) (by linarith)
  have hFp : F p = 1 / 2 := hp
  have hTp : T p = 1 / 2 := by linarith [hFT p]
  have hFg₀ : F g₀ = η := hg₀
  have hTg₁ : T g₁ = η := by linarith [hFT g₁, show F g₁ = 1 - η from hg₁]
  -- a point of large density inside the spread interval
  have hy : ∃ y, 1 / (4 * r) < ρ y := by
    by_contra hcon
    push Not at hcon
    have hbad : MeasurableSet {x : ℝ | r < |x - m|} :=
      measurableSet_lt measurable_const (by fun_prop)
    have hIcc : {x : ℝ | r < |x - m|}ᶜ = Icc (m - r) (m + r) := by
      ext x; simp only [mem_compl_iff, mem_ofPred_eq, not_lt, mem_Icc, abs_le]; constructor <;>
        intro h <;> constructor <;> linarith [h.1, h.2]
    have hI : ∫ y in Icc (m - r) (m + r), ρ y ≤ 1 / 2 := by
      calc ∫ y in Icc (m - r) (m + r), ρ y ≤ ∫ _y in Icc (m - r) (m + r), 1 / (4 * r) :=
            setIntegral_mono_on hi.integrableOn (integrableOn_const (by simp)) measurableSet_Icc
              (fun y _ => hcon y)
        _ = 1 / 2 := by
            rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith)]
            simp only [smul_eq_mul]
            field_simp
            ring
    have hJ : ∫ y in {x : ℝ | r < |x - m|}, ρ y ≤ 1 / 4 := by
      have h := hspread
      rw [hνapp hbad] at h
      have := (ENNReal.ofReal_le_iff_le_toReal (by simp)).1 h
      have e : ((1 : ℝ≥0∞) / 4).toReal = 1 / 4 := by
        simp
      linarith
    have hsum := integral_add_compl hbad hi
    rw [h1] at hsum
    rw [hIcc] at hsum
    have : ∫ y in {x : ℝ | r < |x - m|}ᶜ, ρ y = ∫ y in Icc (m - r) (m + r), ρ y := by
      rw [hIcc]
    linarith
  obtain ⟨y, hy⟩ := hy
  have hρp : 1 / (8 * r) < ρ p := by
    have key : ρ y / 2 ≤ ρ p := by
      rcases le_total y p with hyp | hpy
      · have := density_mul_tail_le hρ hi hyp
        change ρ y * T p ≤ ρ p * T y at this
        have : T y ≤ 1 := by linarith [hFT y, hF0 y]
        nlinarith [hρ0 p, hρ0 y]
      · have := density_mul_cdf_le hρ hi hpy
        change ρ y * F p ≤ ρ p * F y at this
        have : F y ≤ 1 := by linarith [hFT y, hT0 y]
        nlinarith [hρ0 p, hρ0 y]
    have : 1 / (8 * r) = (1 / (4 * r)) / 2 := by field_simp; ring
    linarith
  set G : Set ℝ := Icc g₀ g₁ with hG
  have hGmeas : MeasurableSet G := measurableSet_Icc
  -- lower bound for the density on `G`
  have hlow : ∀ x ∈ G, η / (4 * r) ≤ ρ x := by
    intro x hx
    have hbound : η * ρ p * 2 ≤ ρ x := by
      rcases le_total x p with hxp | hpx
      · have := density_mul_cdf_le hρ hi hxp
        change ρ p * F x ≤ ρ x * F p at this
        have hFx : η ≤ F x := hFg₀ ▸ hFmono hx.1
        rw [hFp] at this
        nlinarith [mul_le_mul_of_nonneg_left hFx (hρ0 p)]
      · have := density_mul_tail_le hρ hi hpx
        change ρ p * T x ≤ ρ x * T p at this
        have hTx : η ≤ T x := by
          have := hFmono hx.2
          rw [show F g₁ = 1 - η from hg₁] at this
          linarith [hFT x]
        rw [hTp] at this
        nlinarith [mul_le_mul_of_nonneg_left hTx (hρ0 p)]
    have : η / (4 * r) ≤ η * ρ p * 2 := by
      have e : η / (4 * r) = η * (1 / (8 * r)) * 2 := by field_simp; ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hρp.le hη0.le
      linarith
    linarith
  -- mass outside `G`
  have hGc : ν Gᶜ ≤ ENNReal.ofReal (2 * η) := by
    have hc : Gᶜ = Iio g₀ ∪ Ioi g₁ := by
      ext x
      simp only [hG, mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]
    have h0 : ν (Iio g₀) = ENNReal.ofReal η := by
      rw [hνapp measurableSet_Iio, ← integral_Iic_eq_integral_Iio]
      exact congrArg ENNReal.ofReal hg₀
    have h1' : ν (Ioi g₁) = ENNReal.ofReal η := by
      rw [hνapp measurableSet_Ioi]
      exact congrArg ENNReal.ofReal hTg₁
    calc ν Gᶜ ≤ ν (Iio g₀) + ν (Ioi g₁) := by rw [hc]; exact measure_union_le _ _
      _ = ENNReal.ofReal (2 * η) := by
          rw [h0, h1', ← ENNReal.ofReal_add hη0.le hη0.le]; ring_nf
  have hne : (S ∩ G).Nonempty := by
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    have hsub : S ⊆ Gᶜ := fun x hx hxG => by
      have : x ∈ S ∩ G := ⟨hx, hxG⟩
      rw [hcon] at this; exact this
    have := (measure_mono (μ := ν) hsub).trans hGc
    rw [hνS, ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
    rw [hη] at this
    linarith
  have hGS_fin : volume (G \ S) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [hG]) (measure_mono sdiff_subset)
  have hvolpos : 0 < volume (G \ S) := by
    by_contra hcon
    have h0 : volume (G \ S) = 0 := nonpos_iff_eq_zero.1 (not_lt.1 hcon)
    have h0' : ν (G \ S) = 0 := hac h0
    have hsub : Sᶜ ⊆ (G \ S) ∪ Gᶜ := by
      intro x hx
      by_cases hxG : x ∈ G
      · exact Or.inl ⟨hxG, hx⟩
      · exact Or.inr hxG
    have := (measure_mono (μ := ν) hsub).trans (measure_union_le _ _)
    rw [hνSc, h0', zero_add] at this
    have := this.trans hGc
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
    rw [hη] at this
    linarith
  set ε₀ : ℝ := (volume (G \ S)).toReal with hε₀
  have hε₀pos : 0 < ε₀ := ENNReal.toReal_pos hvolpos.ne' hGS_fin
  have hmin : min (ν S) (1 - ν S) = ENNReal.ofReal q := by
    have h1a : 1 - ν S = ENNReal.ofReal (1 - a) := by
      rw [hνS, ENNReal.ofReal_sub 1 ha0.le, ENNReal.ofReal_one]
    rw [hq, ENNReal.ofReal_min, h1a, hνS]
  rw [hmin]
  unfold minkowskiContent1D
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [Ioo_mem_nhdsGT hε₀pos] with ε hε
  have hε0 : 0 < ε := hε.1
  have hεvol : ENNReal.ofReal ε ≤ volume (G \ S) :=
    (ENNReal.ofReal_le_iff_le_toReal hGS_fin).2 hε.2.le
  have hgain := gain_in_interval (g₀ := g₀) (g₁ := g₁) hne hεvol
  have hAmeas : MeasurableSet ((thickening ε S \ S) ∩ G) :=
    (isOpen_thickening.measurableSet.diff hS).inter hGmeas
  have hδ : ν ((thickening ε S \ S) ∩ G) ≥ ENNReal.ofReal (η / (4 * r)) *
      volume ((thickening ε S \ S) ∩ G) := by
    rw [hν, withDensity_apply _ hAmeas]
    calc ENNReal.ofReal (η / (4 * r)) * volume ((thickening ε S \ S) ∩ G)
        = ∫⁻ _x in (thickening ε S \ S) ∩ G, ENNReal.ofReal (η / (4 * r)) := by
          rw [setLIntegral_const]
      _ ≤ _ := setLIntegral_mono' hAmeas (fun x hx =>
          ENNReal.ofReal_le_ofReal (hlow x hx.2))
  have hdiff : ν (thickening ε S) - ν S = ν (thickening ε S \ S) :=
    (measure_sdiff (self_subset_thickening hε0 S) hS.nullMeasurableSet (measure_ne_top _ _)).symm
  have hcoef : ENNReal.ofReal (1 / 16 / r) * ENNReal.ofReal q =
      ENNReal.ofReal (η / (4 * r)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hη]; field_simp; ring
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hε0)) (Or.inl ENNReal.ofReal_ne_top),
    hcoef, hdiff]
  calc ENNReal.ofReal (η / (4 * r)) * ENNReal.ofReal ε
      ≤ ENNReal.ofReal (η / (4 * r)) * volume ((thickening ε S \ S) ∩ G) :=
        mul_le_mul' le_rfl hgain
    _ ≤ ν ((thickening ε S \ S) ∩ G) := hδ
    _ ≤ ν (thickening ε S \ S) := measure_mono inter_subset_left

end LogConcave1D
end CvxBody
