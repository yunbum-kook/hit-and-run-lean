module
public import Mathlib.Probability.CDF
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace DikinD2.Cheeger

/-- Every real probability measure has a median, with both strict tails at most one half.
No atomlessness assumption is needed. -/
theorem exists_real_probability_median (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ m : ℝ, μ (Iio m) ≤ (1 / 2 : ℝ≥0∞) ∧ μ (Ioi m) ≤ (1 / 2 : ℝ≥0∞) := by
  let F := cdf μ
  let S : Set ℝ := {x | (1 / 2 : ℝ) ≤ F x}
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop μ).eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1)).exists
    exact ⟨x, hx.le⟩
  have hB : BddBelow S := by
    obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)).exists
    refine ⟨a, fun x hx => ?_⟩
    by_contra h
    have := (monotone_cdf μ) (le_of_lt (lt_of_not_ge h))
    have hx' : (1 / 2 : ℝ) ≤ F x := hx
    change F x ≤ F a at this
    linarith
  let m := sInf S
  have hleft : Function.leftLim F m ≤ (1 / 2 : ℝ) := by
    rw [F.mono.leftLim_eq_sSup]
    apply csSup_le
    · exact (show (Iio m).Nonempty from ⟨m - 1, by simp only [mem_Iio]; linarith⟩).image F
    · rintro _ ⟨x, hx, rfl⟩
      apply le_of_lt
      by_contra h
      have hm : m ≤ x := csInf_le hB (show x ∈ S from le_of_not_gt h)
      exact (not_lt_of_ge hm) hx
  have hright : (1 / 2 : ℝ) ≤ F m := by
    rw [← F.iInf_Ioi_eq m]
    apply le_ciInf
    intro x
    obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hS x.property
    exact (show (1 / 2 : ℝ) ≤ F y from hy).trans (F.mono hyx.le)
  refine ⟨m, ?_, ?_⟩
  · rw [← measure_cdf μ, F.measure_Iio (tendsto_cdf_atBot μ), sub_zero]
    calc ENNReal.ofReal (Function.leftLim F m) ≤ ENNReal.ofReal (1 / 2 : ℝ) :=
          ENNReal.ofReal_le_ofReal hleft
         _ = 1 / 2 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
  · rw [← measure_cdf μ, F.measure_Ioi (tendsto_cdf_atTop μ)]
    calc ENNReal.ofReal (1 - F m) ≤ ENNReal.ofReal (1 / 2 : ℝ) :=
          ENNReal.ofReal_le_ofReal (by linarith)
         _ = 1 / 2 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num

/-- A measurable real function on any probability space admits a median, including at atoms. -/
theorem exists_probability_median {α : Type*} [MeasurableSpace α]
    (π : Measure α) [IsProbabilityMeasure π] (f : α → ℝ) (hf : Measurable f) :
    ∃ m : ℝ, π {x | f x < m} ≤ (1 / 2 : ℝ≥0∞) ∧
      π {x | m < f x} ≤ (1 / 2 : ℝ≥0∞) := by
  obtain ⟨m, hm₁, hm₂⟩ := exists_real_probability_median (π.map f)
  refine ⟨m, ?_, ?_⟩
  · rw [Measure.map_apply hf measurableSet_Iio] at hm₁
    have hs : f ⁻¹' Iio m = {x | f x < m} := by ext x; simp
    rwa [hs] at hm₁
  · rw [Measure.map_apply hf measurableSet_Ioi] at hm₂
    have hs : f ⁻¹' Ioi m = {x | m < f x} := by ext x; simp
    rwa [hs] at hm₂
end DikinD2.Cheeger
