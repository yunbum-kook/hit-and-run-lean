module
public import HitAndRun.Sobolev.SmoothWeightedTest
public import HitAndRun.Sobolev.VectorBoundaryLimit

/-! The sharp smooth estimate written entirely as ordinary integrals. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}
  {ι : Type*} [Fintype ι]

theorem smooth_vectorTestFunctional_eq_global
    (hb : Bornology.IsBounded Ω) (ho : IsOpen Ω)
    (h : E → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (b : ι → E) (φ : ι → testFunctions Ω) :
    vectorTestFunctional (fnL (smoothGraph (μ := μ) hb ho h hh)) b φ =
      -∑ i, ∫ x, h x * fderiv ℝ (φ i : E → ℝ) x (b i) ∂μ := by
  rw [vectorTestFunctional_eq_integral]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  trans ∫ x in Ω, h x * fderiv ℝ (φ i : E → ℝ) x (b i) ∂μ
  · apply integral_congr_ae
    filter_upwards [smoothGraph_fn (μ := μ) hb ho h hh] with x hx
    rw [hx]
  · apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hn : x ∉ tsupport (φ i : E → ℝ) := fun hm => hx ((φ i).2.2.2 hm)
    rw [fderiv_of_notMem_tsupport ℝ hn]
    simp

theorem smooth_vector_integral_sq_le
    (hb : Bornology.IsBounded Ω) (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (h : E → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (b : ι → E) (φ : ι → testFunctions Ω) {R : ℝ}
    (hR : ‖smoothWeightedGradient (μ := μ) hb h hh‖ ^ 2 ≤ R) :
    (∑ i, ∫ x, h x * fderiv ℝ (φ i : E → ℝ) x (b i) ∂μ) ^ 2 ≤
      R * ∫ x, ‖(interiorDistance Ω x)⁻¹ • vectorTestField b φ x‖ ^ 2 ∂μ := by
  have he := smooth_weighted_vector_bound (μ := μ) hb ho hc h hh b φ
  have hs := pow_le_pow_left₀ (abs_nonneg _) he 2
  rw [sq_abs, mul_pow] at hs
  rw [smooth_vectorTestFunctional_eq_global hb ho h hh b φ, neg_sq] at hs
  calc
    _ ≤ ‖smoothWeightedGradient (μ := μ) hb h hh‖ ^ 2 *
        ‖vectorTestCoefficient (μ := μ) ho hc b φ‖ ^ 2 := hs
    _ ≤ R * ‖vectorTestCoefficient (μ := μ) ho hc b φ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hR (sq_nonneg _)
    _ = _ := by rw [norm_sq_vectorTestCoefficient_global]
end HitAndRun.Sobolev
