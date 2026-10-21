module
public import HitAndRun.Markov.HitAndRunOperatorMeasurable
@[expose] public section

namespace HitAndRun.Markov
open MeasureTheory
open scoped RealInnerProductSpace

/-- A uniformly L2-bounded measurable family of scalar representatives is jointly L2. -/
theorem memLp_joint_of_L2_representatives {A X : Type*} [MeasurableSpace A]
    [MeasurableSpace X] (σ : Measure A) [IsFiniteMeasure σ] (μ : Measure X) [SFinite μ]
    (v : A → Lp ℝ 2 μ) (g : A × X → ℝ) (hg : StronglyMeasurable g)
    (hrep : ∀ a, v a =ᵐ[μ] fun x => g (a, x))
    (B : ℝ) (hbound : ∀ a, ‖v a‖ ≤ B) : MemLp g 2 (σ.prod μ) := by
  have hmem (a : A) : MemLp (fun x => g (a, x)) 2 μ := (memLp_congr_ae (hrep a)).1 (Lp.memLp (v a))
  have hid (a : A) : (∫ x, ‖g (a, x) ^ 2‖ ∂μ) = ‖v a‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hrep a] with x hx
    simp only [hx, Real.inner_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg (g (a, x))), pow_two]
  apply (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2
  apply (integrable_prod_iff (hg.pow 2).aestronglyMeasurable).2
  refine ⟨Filter.Eventually.of_forall (fun a => (memLp_two_iff_integrable_sq (hmem a).aestronglyMeasurable).1 (hmem a)), ?_⟩
  apply (integrable_const (B ^ 2)).mono' ((hg.pow 2).norm.integral_prod_right'.aestronglyMeasurable)
  filter_upwards with a
  change ‖∫ x, ‖g (a, x) ^ 2‖ ∂μ‖ ≤ B ^ 2
  rw [hid, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbound a) 2

/-- Fubini identifies an averaged L2 bilinear form with scalar kernel averaging. -/
theorem integral_inner_L2_representatives {A X : Type*} [MeasurableSpace A]
    [MeasurableSpace X] (σ : Measure A) [IsProbabilityMeasure σ] (μ : Measure X) [SFinite μ]
    (v : A → Lp ℝ 2 μ) (g : A × X → ℝ) (hg : StronglyMeasurable g)
    (hrep : ∀ a, v a =ᵐ[μ] fun x => g (a, x))
    (B : ℝ) (hbound : ∀ a, ‖v a‖ ≤ B) (f : Lp ℝ 2 μ) :
    (∫ a, inner ℝ f (v a) ∂σ) = ∫ x, f x * (∫ a, g (a, x) ∂σ) ∂μ := by
  have hm := memLp_joint_of_L2_representatives σ μ v g hg hrep B hbound
  have hf : MemLp (fun p : A × X => f p.2) 2 (σ.prod μ) :=
    (Lp.memLp f).comp_measurePreserving (measurePreserving_snd (μ := σ) (ν := μ))
  have hi : Integrable (fun p : A × X => f p.2 * g p) (σ.prod μ) := hf.integrable_mul hm
  have he (a : A) : inner ℝ f (v a) = ∫ x, f x * g (a, x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hrep a] with x hx
    simp only [hx, Real.inner_apply, Real.inner_apply]
  simp_rw [he]
  rw [← integral_prod _ hi, integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards with x
  exact integral_const_mul _ _

end HitAndRun.Markov
