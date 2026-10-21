module
public import HitAndRun.Markov.ConditionalProjection
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
@[expose] public section

/-! Analytic cancellation tools for coordinate heat-bath projections.
The Sobolev and Euclidean chart instantiations are separate obligations. -/
namespace HitAndRun.Markov
open MeasureTheory Set

/-- A compact C1 derivative has zero total Lebesgue integral. -/
theorem integral_compact_derivative_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∫ t, deriv f t) = 0 := by
  have hi : Integrable (deriv f) :=
    hf.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport hc.deriv
  have he := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hi
  rw [compl_Iic, HasCompactSupport.integral_Iic_deriv_eq hf hc 0, HasCompactSupport.integral_Ioi_deriv_eq hf hc 0] at he
  linarith

/-- Fubini cancellation on every cylinder for genuine compact C1 fiber derivatives. -/
theorem integral_fiber_derivative_cylinder_zero {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SFinite μ] (φ : A → ℝ → ℝ)
    (hf : ∀ x, ContDiff ℝ 1 (φ x)) (hc : ∀ x, HasCompactSupport (φ x))
    (hi : Integrable (fun z : A × ℝ => deriv (φ z.1) z.2) (μ.prod volume))
    (s : Set A) :
    (∫ z in s ×ˢ (univ : Set ℝ), deriv (φ z.1) z.2 ∂μ.prod volume) = 0 := by
  rw [setIntegral_prod _ hi.integrableOn]
  simp only [setIntegral_univ, integral_compact_derivative_zero (hf _) (hc _), integral_zero]

/-- Uniqueness forces the actual conditional L2 projection to vanish if its
coarse-set integrals vanish. This lemma is used only after deriving those integrals. -/
theorem conditionalProjection_eq_zero_of_integrals {α : Type*}
    {m m0 : MeasurableSpace α} {μ : @Measure α m0} (hm : m ≤ m0)
    (f : Lp ℝ 2 μ)
    (hz : ∀ s : Set α, MeasurableSet[m] s → μ s < ⊤ → ∫ x in s, f x ∂μ = 0) :
    conditionalProjection hm f = 0 := by
  apply Lp.ext
  have h := Lp.ae_eq_zero_of_forall_setIntegral_eq_zero' ℝ hm
    (conditionalProjection hm f) two_ne_zero ENNReal.coe_ne_top
    (fun s _ hs => integrableOn_condExpL2_of_measure_ne_top hm hs.ne f)
    (fun s hs hμs => by
      change (∫ x in s, (condExpL2 ℝ ℝ hm f : α → ℝ) x ∂μ) = 0
      rw [integral_condExpL2_eq_of_fin_meas_real f hs hμs.ne]
      exact hz s hs hμs)
    (lpMeas.aestronglyMeasurable (condExpL2 ℝ ℝ hm f))
  exact h.trans (Lp.coeFn_zero ℝ 2 μ).symm

end HitAndRun.Markov
