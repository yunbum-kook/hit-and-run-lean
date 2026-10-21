module
public import HitAndRun.Sobolev.WeightedTestFunctional

/-! Domain-independent integral expressions for the genuine finite-test maps. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}
  {ι : Type*} [Fintype ι]

theorem vectorTestFunctional_eq_integral (h : Lp ℝ 2 (μ.restrict Ω))
    (b : ι → E) (φ : ι → testFunctions Ω) :
    vectorTestFunctional h b φ =
      -∑ i, ∫ x in Ω, h x * fderiv ℝ (φ i : E → ℝ) x (b i) ∂μ := by
  simp only [vectorTestFunctional, LinearMap.neg_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, ContinuousLinearMap.coe_coe,
    innerSL_apply_apply, partialL_testGraphₗ]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_partialCls (μ := μ) (φ i) (b i)] with x hx
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]

theorem coeFn_vectorTestCoefficient (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (b : ι → E) (φ : ι → testFunctions Ω) :
    (vectorTestCoefficient (μ := μ) ho hc b φ : E → E) =ᵐ[μ.restrict Ω]
      fun x => ∑ i, boundaryTest (φ i) x • b i := by
  classical
  simp only [vectorTestCoefficient, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  have hs (s : Finset ι) :
      ((∑ i ∈ s, boundaryFieldLinear (μ := μ) ho hc (b i) (φ i) : Lp E 2 (μ.restrict Ω)) : E → E) =ᵐ[μ.restrict Ω]
        fun x => ∑ i ∈ s, boundaryTest (φ i) x • b i := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      filter_upwards [Lp.coeFn_zero E 2 (μ.restrict Ω)] with x hx
      exact hx
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (boundaryFieldLinear (μ := μ) ho hc (b i) (φ i))
        (∑ j ∈ s, boundaryFieldLinear (μ := μ) ho hc (b j) (φ j)),
        coeFn_boundaryFieldClass (μ := μ) ho hc (φ i) (b i), ih] with x ha hb hd
      change (boundaryFieldLinear (μ := μ) ho hc (b i) (φ i) : E → E) x = _ at hb
      rw [ha, Pi.add_apply, hb, hd]
  simpa using hs Finset.univ

theorem norm_sq_vectorTestCoefficient (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (b : ι → E) (φ : ι → testFunctions Ω) :
    ‖vectorTestCoefficient (μ := μ) ho hc b φ‖ ^ 2 =
      ∫ x in Ω, ‖∑ i, boundaryTest (φ i) x • b i‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_vectorTestCoefficient (μ := μ) ho hc b φ] with x hx
  rw [hx, real_inner_self_eq_norm_sq]
end HitAndRun.Sobolev
