module
/-
Project-side L1 adaptation of CvxBody/Analysis/Cheeger.lean from
chewisinho/cvx_body_lean, commit 41678c03373f8d3ac9d95bab31bcc17022d85bec.
The source repository is private. Its complete source notices are preserved
in the vendored module. No new license or public redistribution permission
is assigned by this adaptation.
-/
public import HitAndRun.Geometry.ReverseBuserUniformRegularity
public import CvxBody.Analysis.Cheeger
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory ProbabilityTheory Filter Topology Metric
open OAI.LeanBlast.KLS
open scoped ENNReal NNReal
variable {n : ℕ}

/-- The L1 median inequality is obtained before the source's L2 squaring step.
It uses Sinho Cheeger coarea, the source median, and the two disjoint derivative formulas. -/
theorem cheeger_l1_median_bounded (ν : Measure (Space n)) [IsProbabilityMeasure ν]
    (hν : ν ≪ volume) {h : ℝ} (hh : 0 < h)
    (hcheeger : ∀ A : Set (Space n), MeasurableSet A →
      ENNReal.ofReal h * min (ν A) (1 - ν A) ≤ CvxBody.minkowskiContent ν A)
    {g : Space n → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g) {M : ℝ}
    (hM : ∀ x, |g x| ≤ M) :
    ∃ m : ℝ, (∫ x, |g x-m| ∂ν) ≤ h⁻¹ * ∫ x, ‖fderiv ℝ g x‖ ∂ν := by
  obtain ⟨m, hm1, hm2⟩ := CvxBody.exists_median ν hg.continuous.measurable hM
  set p : Space n → ℝ := fun y => max (g y - m) 0 with hp
  set q : Space n → ℝ := fun y => max (m - g y) 0 with hq
  have hpL : LipschitzWith L p := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h1 := hg.dist_le_mul x y
    rw [Real.dist_eq] at h1 ⊢
    exact (abs_max_sub_max_le_abs _ _ _).trans (by
      have : g x - m - (g y - m) = g x - g y := by ring
      rw [this]; exact h1)
  have hqL : LipschitzWith L q := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h1 := hg.dist_le_mul x y
    rw [Real.dist_eq] at h1 ⊢
    exact (abs_max_sub_max_le_abs _ _ _).trans (by
      have : m - g x - (m - g y) = -(g x - g y) := by ring
      rw [this, abs_neg]; exact h1)
  have hp0 : ∀ x, 0 ≤ p x := fun x => le_max_right _ _
  have hq0 : ∀ x, 0 ≤ q x := fun x => le_max_right _ _
  have hpset : {x | 0 < p x} = {x | m < g x} := by
    ext x
    simp only [Set.mem_ofPred_eq, hp, lt_max_iff, lt_self_iff_false, or_false, sub_pos]
  have hqset : {x | 0 < q x} = {x | g x < m} := by
    ext x
    simp only [Set.mem_ofPred_eq, hq, lt_max_iff, lt_self_iff_false, or_false, sub_pos]
  have hP := CvxBody.cheeger_l1 ν hν hcheeger hpL hp0 (by rw [hpset]; exact hm1)
  have hQ := CvxBody.cheeger_l1 ν hν hcheeger hqL hq0 (by rw [hqset]; exact hm2)
  have hsum : ∀ x, ENNReal.ofReal |g x-m| =
      ENNReal.ofReal (p x) + ENNReal.ofReal (q x) := by
    intro x
    rw [← ENNReal.ofReal_add (hp0 x) (hq0 x)]
    congr 1
    simp only [hp, hq]
    rcases le_total (g x) m with h1 | h1
    · rw [max_eq_right (by linarith), max_eq_left (by linarith),
        abs_of_nonpos (by linarith)]
      ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith),
        abs_of_nonneg (by linarith)]
      ring
  have hderiv : ∀ x, ENNReal.ofReal ‖fderiv ℝ p x‖ +
      ENNReal.ofReal ‖fderiv ℝ q x‖ ≤ ENNReal.ofReal ‖fderiv ℝ g x‖ := by
    intro x
    rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have e1 := CvxBody.fderiv_posPart_norm (m := m) x hg.continuous
    have e2 := CvxBody.fderiv_negPart_norm (m := m) x hg.continuous
    simp only [← hp] at e1
    simp only [← hq] at e2
    rw [e1, e2]
    rcases lt_trichotomy (g x) m with h1 | h1 | h1
    · simp [h1, not_lt.2 h1.le]
    · simp [h1]
    · simp [h1, not_lt.2 h1.le]
  have hineq : ENNReal.ofReal h * ∫⁻ x, ENNReal.ofReal |g x-m| ∂ν ≤
      ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ g x‖ ∂ν := by
    calc ENNReal.ofReal h * ∫⁻ x, ENNReal.ofReal |g x-m| ∂ν
        = ENNReal.ofReal h * ∫⁻ x, ENNReal.ofReal (p x) ∂ν +
            ENNReal.ofReal h * ∫⁻ x, ENNReal.ofReal (q x) ∂ν := by
          simp_rw [hsum]
          rw [lintegral_add_left hpL.continuous.measurable.ennreal_ofReal, mul_add]
      _ ≤ (∫⁻ x, ENNReal.ofReal ‖fderiv ℝ p x‖ ∂ν) +
          ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ q x‖ ∂ν := add_le_add hP hQ
      _ = ∫⁻ x, (ENNReal.ofReal ‖fderiv ℝ p x‖ +
          ENNReal.ofReal ‖fderiv ℝ q x‖) ∂ν := by
          rw [lintegral_add_left ((measurable_fderiv ℝ p).norm.ennreal_ofReal)]
      _ ≤ ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ g x‖ ∂ν := lintegral_mono hderiv
  have hgI : Integrable g ν := by
    exact (MemLp.of_bound hg.continuous.aestronglyMeasurable M
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hM x)
      (p := 1)).integrable (by norm_num)
  have hGI : Integrable (fun x => ‖fderiv ℝ g x‖) ν := by
    exact (MemLp.of_bound (measurable_fderiv ℝ g).norm.aestronglyMeasurable L
      (Eventually.of_forall fun x => by
        simpa only [norm_norm] using norm_fderiv_le_of_lipschitz ℝ hg (x₀ := x))
      (p := 1)).integrable (by norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x => |g x-m|) (hgI.sub (integrable_const m)).abs
      (Eventually.of_forall fun x => abs_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hGI
      (Eventually.of_forall fun x => norm_nonneg _),
    ← ENNReal.ofReal_mul hh.le] at hineq
  have hreal : h * (∫ x, |g x-m| ∂ν) ≤ ∫ x, ‖fderiv ℝ g x‖ ∂ν :=
    (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x => norm_nonneg _)).1 hineq
  refine ⟨m, ?_⟩
  have ht := mul_le_mul_of_nonneg_left hreal (inv_nonneg.2 hh.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul] using ht
end HitAndRun.Geometry
