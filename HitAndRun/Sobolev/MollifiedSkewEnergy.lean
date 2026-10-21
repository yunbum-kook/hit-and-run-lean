module
public import HitAndRun.Sobolev.DistributionMollifier
public import HitAndRun.Analysis.MollifiedL2

/-! Probability-kernel smoothing preserves antisymmetry and does not increase
the actual upper-triangle skew energy. No Frobenius factor is inserted. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph EllipticPdes.Embedding
open scoped Convolution BigOperators ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem mollified_memLp (rho : ContDiffBump (0 : E)) {f : E → ℝ} (hf : MemLp f 2 μ) :
    MemLp (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) 2 μ := by
  rw [convolution_lsmul_comm]
  exact lt_of_le_of_lt
    (eLpNorm_convolution_le_of_integral_eq_one (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num) rho.nonneg_normed
      (rho.contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) (rho.normed μ)).continuous.aestronglyMeasurable
      rho.integral_normed hf.aestronglyMeasurable) hf.eLpNorm_lt_top

theorem mollified_sq_integral_le (rho : ContDiffBump (0 : E))
    {f : E → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x ^ 2 ∂μ) ≤
      ∫ x, f x ^ 2 ∂μ := by
  have he := eLpNorm_convolution_le_of_integral_eq_one (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (by norm_num) rho.nonneg_normed
    (rho.contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) (rho.normed μ)).continuous.aestronglyMeasurable
    rho.integral_normed hf.aestronglyMeasurable
  rw [convolution_lsmul_comm] at he
  have hn : ‖(mollified_memLp rho hf).toLp _‖ ≤ ‖hf.toLp f‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp]
    exact ENNReal.toReal_mono hf.eLpNorm_ne_top he
  have heq {g : E → ℝ} (hg : MemLp g 2 μ) : ‖hg.toLp g‖ ^ 2 = ∫ x, g x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, inner_toLp_toLp]
    simp [sq]
  rw [← heq (mollified_memLp rho hf), ← heq hf]
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

theorem mollified_skew {ι : Type*} (rho : ContDiffBump (0 : E))
    (G : ι → ι → E → ℝ) (hs : ∀ x i j, G i j x = -G j i x) (x : E) (i j : ι) :
    (G i j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x =
      -(G j i ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x := by
  change (∫ y, G i j y * rho.normed μ (x - y) ∂μ) =
    -(∫ y, G j i y * rho.normed μ (x - y) ∂μ)
  rw [← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by dsimp only; rw [hs y i j]; ring
theorem mollified_upper_energy_le {n : ℕ} (rho : ContDiffBump (0 : E))
    (G : Fin n → Fin n → E → ℝ) (hG : ∀ i j, MemLp (G i j) 2 μ) :
    (∫ x, ∑ i, ∑ j, if i < j then
      (G i j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x ^ 2 else 0 ∂μ) ≤
      ∫ x, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂μ := by
  have hi (i j : Fin n) : Integrable (fun x => if i < j then G i j x ^ 2 else 0) μ := by
    split_ifs
    · exact (hG i j).integrable_sq
    · exact integrable_zero _ _ _
  have hm (i j : Fin n) : Integrable (fun x => if i < j then
      (G i j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x ^ 2 else 0) μ := by
    split_ifs
    · exact (mollified_memLp rho (hG i j)).integrable_sq
    · exact integrable_zero _ _ _
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hm i j)),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_le_sum
  intro i _
  rw [integral_finsetSum _ (fun j _ => hm i j), integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact mollified_sq_integral_le rho (hG i j)
  · rfl
end HitAndRun.Sobolev
