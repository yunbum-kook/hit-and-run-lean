module
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
@[expose] public section

namespace HitAndRun.Markov
open Set MeasureTheory TopologicalSpace
open scoped RealInnerProductSpace

/-- Scalar distances determine measurability into a second-countable metric space. -/
theorem measurable_of_measurable_dist {A H : Type*} [MeasurableSpace A]
    [MetricSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (f : A → H) (hf : ∀ z, Measurable (fun a => dist (f a) z)) : Measurable f := by
  have hb : IsTopologicalBasis {s : Set H | ∃ z r, s = Metric.ball z r} := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro s ⟨z, r, rfl⟩
      exact Metric.isOpen_ball
    · intro z s hz hs
      obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hs z hz
      exact ⟨Metric.ball z r, ⟨z, r, rfl⟩, Metric.mem_ball_self hr, hrs⟩
  rw [‹BorelSpace H›.measurable_eq, hb.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro s ⟨z, r, rfl⟩
  exact measurableSet_lt (hf z) measurable_const

/-- Joint scalar representatives give a strongly measurable family of genuine L2 elements.
The proof uses separability of L2 and scalar distance integrals, not a measurable-family axiom. -/
theorem stronglyMeasurable_L2_of_representatives {A X : Type*}
    [MeasurableSpace A] [MeasurableSpace X] (μ : Measure X) [SFinite μ] [IsSeparable μ]
    (v : A → Lp ℝ 2 μ) (g : A × X → ℝ) (hg : StronglyMeasurable g)
    (hrep : ∀ a, v a =ᵐ[μ] fun x => g (a, x)) : StronglyMeasurable v := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  letI : MeasurableSpace (Lp ℝ 2 μ) := borel _
  letI : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  apply Measurable.stronglyMeasurable
  apply measurable_of_measurable_dist
  intro z
  have hsq : Measurable (fun a => ∫ x, (g (a, x) - z x) ^ 2 ∂μ) :=
    ((hg.sub ((Lp.stronglyMeasurable z).comp_measurable measurable_snd)).pow 2).integral_prod_right'.measurable
  have hid (a : A) : (∫ x, (g (a, x) - z x) ^ 2 ∂μ) = ‖v a - z‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (v a) z, hrep a] with x hx hv
    simp only [hx, Pi.sub_apply, hv, Real.inner_apply, pow_two]
  have hroot := hsq.sqrt
  simpa only [hid, Real.sqrt_sq (norm_nonneg _), dist_eq_norm] using hroot

end HitAndRun.Markov
