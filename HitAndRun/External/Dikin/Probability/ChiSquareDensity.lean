module
public import HitAndRun.External.Dikin.Markov.ReversibleSupport
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Function.L2Space
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Classical
namespace DikinD2.ChiSquareDensity
variable {α : Type*} [MeasurableSpace α]

/-- The source integrand, extended to an infinite Radon–Nikodym value. -/
def centeredSquare (r : ℝ≥0∞) : ℝ≥0∞ :=
  if r = ∞ then ∞ else ENNReal.ofReal ((r.toReal - 1) ^ 2)

/-- Source line 351: the nonnegative integral if absolutely continuous, infinity otherwise.
The guard in centeredSquare prevents interpreting an infinite derivative as the real zero. -/
def chiSquare (ν π : Measure α) : ℝ≥0∞ :=
  if ν ≪ π then ∫⁻ x, centeredSquare (ν.rnDeriv π x) ∂π else ∞

theorem chiSquare_of_not_ac {ν π : Measure α} (h : ¬ ν ≪ π) :
    chiSquare ν π = ∞ := by simp [chiSquare, h]

variable {ν π : Measure α} [IsProbabilityMeasure ν] [IsProbabilityMeasure π]

omit [IsProbabilityMeasure π] in
/-- Finiteness of the derivative is established before its real-valued density is used. -/
theorem rnDeriv_finite : ∀ᵐ x ∂π, ν.rnDeriv π x ≠ ∞ :=
  (Measure.rnDeriv_lt_top ν π).mono fun _ hx => hx.ne

def density (ν π : Measure α) : α → ℝ := fun x => (ν.rnDeriv π x).toReal

omit [IsProbabilityMeasure ν] [IsProbabilityMeasure π] in
theorem density_measurable : Measurable (density ν π) :=
  (Measure.measurable_rnDeriv ν π).ennreal_toReal

omit [IsProbabilityMeasure ν] [IsProbabilityMeasure π] in
theorem density_nonneg (x : α) : 0 ≤ density ν π x := ENNReal.toReal_nonneg

theorem density_representation (h : ν ≪ π) :
    ν = π.withDensity (fun x => ENNReal.ofReal (density ν π x)) := by
  calc
    ν = π.withDensity (ν.rnDeriv π) := (Measure.withDensity_rnDeriv_eq ν π h).symm
    _ = _ := by
      apply withDensity_congr_ae
      filter_upwards [rnDeriv_finite (ν := ν) (π := π)] with x hx
      exact (ENNReal.ofReal_toReal hx).symm

theorem density_mass (h : ν ≪ π) : ∫ x, density ν π x ∂π = 1 := by
  simpa [density] using Measure.integral_toReal_rnDeriv h

omit [IsProbabilityMeasure π] in
theorem chiSquare_eq_lintegral (h : ν ≪ π) :
    chiSquare ν π = ∫⁻ x, ENNReal.ofReal ((density ν π x - 1) ^ 2) ∂π := by
  rw [chiSquare, ite_eq_left h]
  apply lintegral_congr_ae
  filter_upwards [rnDeriv_finite (ν := ν) (π := π)] with x hx
  simp [centeredSquare, hx, density]

theorem finite_iff_ac_memLp :
    chiSquare ν π ≠ ∞ ↔ ν ≪ π ∧ MemLp (density ν π) 2 π := by
  constructor
  · intro hc
    have ha : ν ≪ π := by
      by_contra hn
      exact hc (chiSquare_of_not_ac hn)
    refine ⟨ha, ?_⟩
    rw [chiSquare_eq_lintegral ha] at hc
    have hm : AEStronglyMeasurable (density ν π) π := (density_measurable (ν := ν) (π := π)).aestronglyMeasurable
    have hi : Integrable (fun x => (density ν π x - 1) ^ 2) π :=
      (lintegral_ofReal_ne_top_iff_integrable
        ((hm.sub aestronglyMeasurable_const).pow 2)
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp hc
    have hl := (memLp_two_iff_integrable_sq (hm.sub aestronglyMeasurable_const)).mpr hi
    convert hl.add (memLp_const (1 : ℝ)) using 1; simp
  · rintro ⟨ha, hf⟩
    rw [chiSquare_eq_lintegral ha]
    exact (lintegral_ofReal_ne_top_iff_integrable
      ((hf.aestronglyMeasurable.sub aestronglyMeasurable_const).pow 2)
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mpr
      ((hf.sub (memLp_const (1 : ℝ))).integrable_sq)

/-- Finite source divergence yields an actual normalized L2 density of the initial law. -/
theorem finite_density_package (h : chiSquare ν π ≠ ∞) :
    Measurable (density ν π) ∧ (∀ x, 0 ≤ density ν π x) ∧
    ν = π.withDensity (fun x => ENNReal.ofReal (density ν π x)) ∧
    MemLp (density ν π) 2 π ∧ ∫ x, density ν π x ∂π = 1 := by
  obtain ⟨ha, hf⟩ := finite_iff_ac_memLp.mp h
  exact ⟨density_measurable, density_nonneg, density_representation ha, hf, density_mass ha⟩

omit [IsProbabilityMeasure ν] in
/-- Identifies any actual nonnegative measurable real density, not merely a symbolic L2 input. -/
theorem density_eq_of_representation {f : α → ℝ} (hm : Measurable f)
    (hn : ∀ x, 0 ≤ f x)
    (hr : ν = π.withDensity (fun x => ENNReal.ofReal (f x))) :
    density ν π =ᵐ[π] f := by
  have he := Measure.rnDeriv_withDensity π (hm.ennreal_ofReal)
  rw [← hr] at he
  filter_upwards [he] with x hx
  simp only [density, hx, ENNReal.toReal_ofReal (hn x)]

theorem chiSquare_eq_integral_of_density {f : α → ℝ} (hm : Measurable f)
    (hn : ∀ x, 0 ≤ f x) (hf : MemLp f 2 π)
    (hr : ν = π.withDensity (fun x => ENNReal.ofReal (f x))) :
    chiSquare ν π = ENNReal.ofReal (∫ x, (f x - 1) ^ 2 ∂π) := by
  have ha : ν ≪ π := hr ▸ withDensity_absolutelyContinuous π _
  rw [chiSquare_eq_lintegral ha]
  calc
    _ = ∫⁻ x, ENNReal.ofReal ((f x - 1) ^ 2) ∂π := by
      apply lintegral_congr_ae
      filter_upwards [density_eq_of_representation hm hn hr] with x hx
      rw [hx]
    _ = _ := (ofReal_integral_eq_lintegral_ofReal
      ((hf.sub (memLp_const (1 : ℝ))).integrable_sq)
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm

/-- The genuine Hilbert L2 element has precisely the centered-density integral as norm square. -/
theorem centered_integral_eq_norm_sq {f : α → ℝ} (hf : MemLp f 2 π) :
    ∫ x, (f x - 1) ^ 2 ∂π =
      ‖(hf.sub (memLp_const (1 : ℝ))).toLp (fun x => f x - 1)‖ ^ 2 := by
  let g := (hf.sub (memLp_const (1 : ℝ))).toLp (fun x => f x - 1)
  have he : g =ᵐ[π] (fun x => f x - 1) := MemLp.coeFn_toLp _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [he] with x hx
  dsimp [g] at hx
  simp [hx, pow_two]

theorem chiSquare_eq_centered_norm_sq {f : α → ℝ} (hm : Measurable f)
    (hn : ∀ x, 0 ≤ f x) (hf : MemLp f 2 π)
    (hr : ν = π.withDensity (fun x => ENNReal.ofReal (f x))) :
    chiSquare ν π = ENNReal.ofReal
      (‖(hf.sub (memLp_const (1 : ℝ))).toLp (fun x => f x - 1)‖ ^ 2) := by
  rw [chiSquare_eq_integral_of_density hm hn hf hr, centered_integral_eq_norm_sq hf]

/-- Normalization constructs a probability measure, rather than assuming one. -/
theorem density_isProbability {f : α → ℝ}
    (hn : ∀ x, 0 ≤ f x) (hf : MemLp f 2 π) (h1 : ∫ x, f x ∂π = 1) :
    IsProbabilityMeasure (π.withDensity (fun x => ENNReal.ofReal (f x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hf.integrable (by norm_num))
      (Filter.Eventually.of_forall hn), h1]
  simp


theorem chiSquare_eq_eLpNorm_sq {f : α → ℝ} (hm : Measurable f)
    (hn : ∀ x, 0 ≤ f x) (hf : MemLp f 2 π)
    (hr : ν = π.withDensity (fun x => ENNReal.ofReal (f x))) :
    chiSquare ν π = (eLpNorm (fun x => f x - 1) 2 π) ^ 2 := by
  have ht : eLpNorm (fun x => f x - 1) 2 π ≠ ∞ :=
    (hf.sub (memLp_const (1 : ℝ))).eLpNorm_ne_top
  rw [chiSquare_eq_centered_norm_sq hm hn hf hr, ENNReal.ofReal_pow (norm_nonneg _),
    Lp.norm_toLp, ENNReal.ofReal_toReal ht]

/-- Converse package from a normalized, measurable, nonnegative L2 density. -/
theorem normalized_density_converse {f : α → ℝ} (hm : Measurable f)
    (hn : ∀ x, 0 ≤ f x) (hf : MemLp f 2 π) (h1 : ∫ x, f x ∂π = 1) :
    let νf := π.withDensity (fun x => ENNReal.ofReal (f x))
    IsProbabilityMeasure νf ∧ chiSquare νf π ≠ ∞ ∧
    chiSquare νf π = ENNReal.ofReal (∫ x, (f x - 1) ^ 2 ∂π) ∧
    chiSquare νf π = (eLpNorm (fun x => f x - 1) 2 π) ^ 2 := by
  dsimp
  let := density_isProbability hn hf h1
  have he := chiSquare_eq_integral_of_density hm hn hf rfl
  exact ⟨inferInstance, he ▸ ENNReal.ofReal_ne_top, he,
    chiSquare_eq_eLpNorm_sq hm hn hf rfl⟩

end DikinD2.ChiSquareDensity
