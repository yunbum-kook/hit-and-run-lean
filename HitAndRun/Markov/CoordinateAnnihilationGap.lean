module
public import HitAndRun.Markov.CoordinateAnnihilationSobolev
public import HitAndRun.Markov.CoordinateAnnihilationCertificate
public import HitAndRun.Sobolev.CurlEnergy
public import HitAndRun.Markov.SpectralGap
@[expose] public section

/-! Actual Sobolev certificate for the coordinate conditional-projection operator.
Identification with the chord transition kernel remains a separate theorem. -/
namespace HitAndRun.Markov
open MeasureTheory HitAndRun.Sobolev
open scoped BigOperators RealInnerProductSpace
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

noncomputable def coordinateHeatBath
    (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) : Lp ℝ 2 (K.ambient.restrict K.carrier) :=
  coordinateAverage coordinateSigma coordinateSigma_le f

/-- The source's exact n*CBA energy inequality on actual coordinate projections. -/
theorem coordinateHeatBath_energy_bound (hC : K.constant < ⊤) (f : K.Target) :
    ‖f‖ ^ 2 ≤ (n : ℝ) * K.constant.toReal *
      inner ℝ (f : Lp ℝ 2 (K.ambient.restrict K.carrier))
        ((f : Lp ℝ 2 (K.ambient.restrict K.carrier)) - coordinateHeatBath K f) := by
  obtain ⟨u, hu, he⟩ := K.attained_solver hC f
  let g (i : Fin n) := weakPartial u i i
  have hs : ∑ i, g i = (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) := by
    have hh := congrArg Subtype.val hu
    change divergence K.ambient K.carrier u = _ at hh
    rw [← hh]
    simp only [divergence, sum_apply]
    rfl
  have hz : ∀ i, conditionalProjection (coordinateSigma_le i) (g i) = 0 := by
    intro i
    exact gradient_partial_coordinate_projection K i (u i)
  have hd : ∑ i, ‖g i‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [vectorField_energy]
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖weakPartial u i j‖) (Finset.mem_univ i)
  have hc := coordinate_certificate_energy coordinateSigma coordinateSigma_le
    (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) g K.constant.toReal hs hz (hd.trans he)
  have ha := coordinateAverage_energy coordinateSigma coordinateSigma_le
    (f : Lp ℝ 2 (K.ambient.restrict K.carrier))
  simp only [Fintype.card_fin] at ha
  change inner ℝ (f : Lp ℝ 2 (K.ambient.restrict K.carrier))
    ((f : Lp ℝ 2 (K.ambient.restrict K.carrier)) - coordinateHeatBath K f) = _ at ha
  rw [ha]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  convert hc using 1 <;> simp only [Submodule.norm_coe] <;> field_simp

/-- Exact reciprocal Rayleigh bound on every nonzero centered function. -/
theorem coordinateHeatBath_rayleigh_bound (hC : K.constant < ⊤)
    (f : K.Target) (hf : f ≠ 0) :
    1 / ((n : ℝ) * K.constant.toReal) ≤
      inner ℝ (f : Lp ℝ 2 (K.ambient.restrict K.carrier))
        ((f : Lp ℝ 2 (K.ambient.restrict K.carrier)) - coordinateHeatBath K f) / ‖f‖ ^ 2 := by
  have hc := coordinateHeatBath_energy_bound K hC f
  have hp : 0 < ‖f‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
  by_cases hzero : K.constant.toReal = 0
  · rw [hzero, mul_zero, zero_mul] at hc
    exact False.elim (not_le_of_gt hp hc)
  · have hcp : 0 < K.constant.toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
    have hnp : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
    apply (div_le_div_iff₀ (mul_pos hnp hcp) hp).2
    simpa only [one_mul, mul_comm] using hc

/-- The literal Rayleigh gap of the actual coordinate conditional-expectation
operator, prior to its chord-kernel identification. -/
theorem coordinateHeatBath_spectralGap (hC : K.constant < ⊤) :
    1 / ((n : ℝ) * K.constant.toReal) ≤ spectralGap K (coordinateHeatBath K) :=
  le_spectralGap K (coordinateHeatBath K) _ (coordinateHeatBath_rayleigh_bound K hC)

end HitAndRun.Markov
