module
public import HitAndRun.Sobolev.BoundaryTest
public import HitAndRun.Analysis.BoundedTestFunctional

/-! Genuine finite vector-test coefficient and distributional functional.
The analytic bound is an explicit premise here, not a claimed B.5 proof. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Analysis
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

theorem boundaryField_memLp (hΩ : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (φ : testFunctions Ω) (v : E) :
    MemLp (fun x => boundaryTest φ x • v) 2 (μ.restrict Ω) :=
  ((boundaryTest_continuous hΩ hc φ).smul continuous_const).memLp_of_hasCompactSupport
    (boundaryTest_compact φ).smul_right

def boundaryFieldClass (hΩ : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (φ : testFunctions Ω) (v : E) : Lp E 2 (μ.restrict Ω) :=
  (boundaryField_memLp hΩ hc φ v).toLp _

theorem coeFn_boundaryFieldClass (hΩ : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (φ : testFunctions Ω) (v : E) :
    (boundaryFieldClass (μ := μ) hΩ hc φ v : E → E) =ᵐ[μ.restrict Ω]
      fun x => boundaryTest φ x • v :=
  (boundaryField_memLp hΩ hc φ v).coeFn_toLp

def boundaryFieldLinear (hΩ : IsOpen Ω) (hc : Ωᶜ.Nonempty) (v : E) :
    testFunctions Ω →ₗ[ℝ] Lp E 2 (μ.restrict Ω) where
  toFun φ := boundaryFieldClass hΩ hc φ v
  map_add' φ ψ := by
    apply Lp.ext
    filter_upwards [coeFn_boundaryFieldClass (μ := μ) hΩ hc (φ + ψ) v,
      coeFn_boundaryFieldClass (μ := μ) hΩ hc φ v,
      coeFn_boundaryFieldClass (μ := μ) hΩ hc ψ v,
      Lp.coeFn_add (boundaryFieldClass (μ := μ) hΩ hc φ v)
        (boundaryFieldClass (μ := μ) hΩ hc ψ v)] with x ha hb hd he
    rw [ha, he, Pi.add_apply, hb, hd]
    simp [boundaryTest, add_div, add_smul]
  map_smul' c φ := by
    apply Lp.ext
    filter_upwards [coeFn_boundaryFieldClass (μ := μ) hΩ hc (c • φ) v,
      coeFn_boundaryFieldClass (μ := μ) hΩ hc φ v,
      Lp.coeFn_smul c (boundaryFieldClass (μ := μ) hΩ hc φ v)] with x ha hb hd
    simp only [RingHom.id_apply]
    rw [ha, hd, Pi.smul_apply, hb]
    simp [boundaryTest, mul_div_assoc, mul_smul]

variable {ι : Type*} [Fintype ι]

def vectorTestCoefficient (hΩ : IsOpen Ω) (hc : Ωᶜ.Nonempty) (b : ι → E) :
    (ι → testFunctions Ω) →ₗ[ℝ] Lp E 2 (μ.restrict Ω) :=
  ∑ i, (boundaryFieldLinear hΩ hc (b i)).comp (LinearMap.proj i)

def vectorTestFunctional (h : Lp ℝ 2 (μ.restrict Ω)) (b : ι → E) :
    (ι → testFunctions Ω) →ₗ[ℝ] ℝ :=
  -∑ i, (innerSL ℝ h).toLinearMap.comp
    (((partialL (b i)).toLinearMap.comp (testGraphₗ μ Ω)).comp (LinearMap.proj i))

/-- Once the actual finite vector-test bound is proved, Riesz produces a genuine
weighted distributional gradient with the same bound. -/
theorem exists_weighted_gradient_of_test_bound (hΩ : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (h : Lp ℝ 2 (μ.restrict Ω)) (b : ι → E) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ φ, |vectorTestFunctional h b φ| ≤ R * ‖vectorTestCoefficient (μ := μ) hΩ hc b φ‖) :
    ∃ q : Lp E 2 (μ.restrict Ω),
      (∀ φ, inner ℝ q (vectorTestCoefficient (μ := μ) hΩ hc b φ) = vectorTestFunctional h b φ) ∧
      ‖q‖ ≤ R :=
  exists_riesz_of_test_bound (vectorTestCoefficient (μ := μ) hΩ hc b)
    (vectorTestFunctional h b) hR hb
end HitAndRun.Sobolev
