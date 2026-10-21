module
public import HitAndRun.Markov.HitAndRunOperatorReversible
public import HitAndRun.Markov.HitAndRunGap
@[expose] public section

namespace HitAndRun.Markov
open MeasureTheory ProbabilityTheory HitAndRun.Sobolev DikinD2
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
local instance : IsMarkovKernel (hitAndRun K.carrier K.isOpen K.isBounded) :=
  hitAndRun_markov K.isOpen K.isBounded

theorem hitAndRun_gap_at_most_one (hC : K.constant < ⊤) :
    ((n : ℝ) + 2) / ((n : ℝ) * (2 + K.constant.toReal)) ≤ 1 := by
  letI := target_nontrivial K
  obtain ⟨f, hf⟩ := exists_ne (0 : K.Target)
  have hg := hitAndRunOperator_rayleigh_bound K hC f hf
  apply hg.trans
  apply (div_le_one (sq_pos_of_pos (norm_pos_iff.mpr hf))).2
  have hp : 0 ≤ inner ℝ (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) (hitAndRunOperator K f) := by
    rw [hitAndRunOperator_inner_average]
    exact integral_nonneg (fun θ => conditionalProjection_positive _ _)
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  change ‖(f : Lp ℝ 2 (K.ambient.restrict K.carrier))‖ ^ 2 - _ ≤ _
  simpa only [Submodule.norm_coe] using sub_le_self
    (‖(f : Lp ℝ 2 (K.ambient.restrict K.carrier))‖ ^ 2) hp

theorem hitAndRunNativeOperator_gap (hC : K.constant < ⊤)
    (f : Lp ℝ 2 K.bodyUniform) (hf : f ∈ NativeL2.meanZero K.bodyUniform) :
    (((n : ℝ) + 2) / ((n : ℝ) * (2 + K.constant.toReal))) * ‖f‖ ^ 2 ≤
      inner ℝ f (f - hitAndRunNativeOperator K f) := by
  obtain ⟨u, rfl⟩ := K.bodyL2Isometry_surjective f
  have hmean : ∫ x, u x ∂K.ambient.restrict K.carrier = 0 := by
    rw [NativeL2.mem_meanZero] at hf
    calc
      _ = ∫ x : K.carrier, u x.val ∂K.bodyUniform :=
        (K.bodyUniform_measurePreserving.integral_comp
          (MeasurableEmbedding.subtype_coe K.isOpen.measurableSet) u).symm
      _ = ∫ x, K.bodyL2Isometry u x ∂K.bodyUniform := integral_congr_ae (K.bodyL2Isometry_coe u).symm
      _ = 0 := hf
  have hu : u ∈ centeredL2 (μ := K.ambient) (Ω := K.carrier) := by
    change meanCLM K.ambient K.carrier u = 0
    rw [meanCLM_eq_integral]
    exact hmean
  let u0 : K.Target := ⟨u, hu⟩
  rw [← hitAndRunOperator_body, ← map_sub, K.bodyL2Isometry.inner_map_map,
    K.bodyL2Isometry.norm_map]
  by_cases hz : u0 = 0
  · have huz : u = 0 := congrArg Subtype.val hz
    simp [huz]
  · have hg := hitAndRunOperator_rayleigh_bound K hC u0 hz
    exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hz))).1 hg

/-- Actual non-lazy random-direction chain law contracts chi-square at the exact BA rate. -/
theorem hitAndRun_chiSquare (hC : K.constant < ⊤)
    (ν : Measure K.carrier) [IsProbabilityMeasure ν] (N : ℕ) :
    ChiSquareDensity.chiSquare
      (NativeL2.lawOrbit (hitAndRun K.carrier K.isOpen K.isBounded) ν N) K.bodyUniform ≤
      ChiSquareDensity.chiSquare ν K.bodyUniform *
        ENNReal.ofReal (Real.exp (-2 * (((n : ℝ) + 2) / ((n : ℝ) * (2 + K.constant.toReal))) * N)) := by
  apply chiSquare_lawOrbit_le_exp_of_gap (hitAndRun_jointReversible K)
    (hitAndRunNativeOperator_positive K)
    (((n : ℝ) + 2) / ((n : ℝ) * (2 + K.constant.toReal))) (by positivity) (hitAndRun_gap_at_most_one K hC)
  exact hitAndRunNativeOperator_gap K hC

end HitAndRun.Markov
