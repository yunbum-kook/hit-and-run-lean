module
public import HitAndRun.Sobolev.WeightedTestFunctional
public import HitAndRun.Sobolev.WeightedGradientLocal

/-! The finite-test Riesz vector is a genuine weighted weak gradient.
The analytic test estimate remains an explicit premise. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

def boundaryFieldDirectionLinear (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (φ : testFunctions Ω) : E →ₗ[ℝ] Lp E 2 (μ.restrict Ω) where
  toFun v := boundaryFieldClass ho hc φ v
  map_add' v w := by
    apply Lp.ext
    filter_upwards [coeFn_boundaryFieldClass (μ := μ) ho hc φ (v+w),
      coeFn_boundaryFieldClass (μ := μ) ho hc φ v,
      coeFn_boundaryFieldClass (μ := μ) ho hc φ w,
      Lp.coeFn_add (boundaryFieldClass (μ := μ) ho hc φ v)
        (boundaryFieldClass (μ := μ) ho hc φ w)] with x ha hb hd he
    rw [ha, he, Pi.add_apply, hb, hd, smul_add]
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [coeFn_boundaryFieldClass (μ := μ) ho hc φ (c • v),
      coeFn_boundaryFieldClass (μ := μ) ho hc φ v,
      Lp.coeFn_smul c (boundaryFieldClass (μ := μ) ho hc φ v)] with x ha hb he
    simp only [RingHom.id_apply]
    rw [ha, he, Pi.smul_apply, hb, smul_comm]

def partialClsDirectionLinear (φ : testFunctions Ω) : E →ₗ[ℝ] Lp ℝ 2 (μ.restrict Ω) where
  toFun v := partialCls μ Ω φ v
  map_add' v w := by
    apply Lp.ext
    filter_upwards [coeFn_partialCls (μ := μ) φ (v+w),
      coeFn_partialCls (μ := μ) φ v, coeFn_partialCls (μ := μ) φ w,
      Lp.coeFn_add (partialCls μ Ω φ v) (partialCls μ Ω φ w)] with x ha hb hd he
    rw [ha, he, Pi.add_apply, hb, hd, map_add]
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [coeFn_partialCls (μ := μ) φ (c • v),
      coeFn_partialCls (μ := μ) φ v,
      Lp.coeFn_smul c (partialCls μ Ω φ v)] with x ha hb he
    simp only [RingHom.id_apply]
    rw [ha, he, Pi.smul_apply, hb, map_smul]

variable {ι : Type*} [Fintype ι]

theorem riesz_weighted_pairing_all_directions (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (h : Lp ℝ 2 (μ.restrict Ω)) (q : Lp E 2 (μ.restrict Ω)) (b : Module.Basis ι ℝ E)
    (hp : ∀ Φ, inner ℝ q (vectorTestCoefficient (μ := μ) ho hc b Φ) =
      vectorTestFunctional h b Φ) (φ : testFunctions Ω) (v : E) :
    inner ℝ q (boundaryFieldClass ho hc φ v) = -inner ℝ h (partialCls μ Ω φ v) := by
  classical
  let L : E →ₗ[ℝ] ℝ := (innerSL ℝ q).toLinearMap.comp (boundaryFieldDirectionLinear ho hc φ)
  let R : E →ₗ[ℝ] ℝ := -(innerSL ℝ h).toLinearMap.comp (partialClsDirectionLinear φ)
  have he : L = R := by
    apply b.ext
    intro i
    have hi := hp (Pi.single i φ)
    simp only [vectorTestCoefficient, vectorTestFunctional, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.neg_apply,
      ContinuousLinearMap.coe_coe, innerSL_apply_apply] at hi
    simp only [Pi.single_apply, apply_ite, map_zero, inner_zero_right,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hi
    simpa [partialL_testGraphₗ, L, R, boundaryFieldDirectionLinear,
      partialClsDirectionLinear, boundaryFieldLinear] using hi
  exact congrArg (fun f : E →ₗ[ℝ] ℝ => f v) he

theorem weighted_integral_pairing_of_riesz (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (h : Lp ℝ 2 (μ.restrict Ω)) (q : Lp E 2 (μ.restrict Ω)) (b : Module.Basis ι ℝ E)
    (hp : ∀ Φ, inner ℝ q (vectorTestCoefficient (μ := μ) ho hc b Φ) =
      vectorTestFunctional h b Φ) (φ : testFunctions Ω) (v : E) :
    (∫ x in Ω, h x * fderiv ℝ (φ : E → ℝ) x v ∂μ) =
      -∫ x in Ω, boundaryTest φ x * inner ℝ (q x) v ∂μ := by
  have he := riesz_weighted_pairing_all_directions ho hc h q b hp φ v
  have hleft : inner ℝ q (boundaryFieldClass ho hc φ v) =
      ∫ x in Ω, boundaryTest φ x * inner ℝ (q x) v ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_boundaryFieldClass (μ := μ) ho hc φ v] with x hx
    rw [hx, real_inner_smul_right]
  have hright : inner ℝ h (partialCls μ Ω φ v) =
      ∫ x in Ω, h x * fderiv ℝ (φ : E → ℝ) x v ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_partialCls (μ := μ) φ v] with x hx
    rw [hx]
    simp [RCLike.inner_apply, mul_comm]
  rw [hleft, hright] at he
  linarith

theorem hasWeakFDerivOn_of_riesz (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (h : Lp ℝ 2 (μ.restrict Ω)) (q : Lp E 2 (μ.restrict Ω)) (b : Module.Basis ι ℝ E)
    (hp : ∀ Φ, inner ℝ q (vectorTestCoefficient (μ := μ) ho hc b Φ) =
      vectorTestFunctional h b Φ) :
    HasWeakFDerivOn ⟨Ω, ho⟩ h
      (fun x => innerSL ℝ ((interiorDistance Ω x)⁻¹ • q x)) μ :=
  hasWeakFDerivOn_of_weighted_test_pairing ho hc (Lp.memLp h) (Lp.memLp q)
    (weighted_integral_pairing_of_riesz ho hc h q b hp)
theorem exists_weak_gradient_of_test_bound (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (h : Lp ℝ 2 (μ.restrict Ω)) (b : Module.Basis ι ℝ E) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ Φ, |vectorTestFunctional h b Φ| ≤
      R * ‖vectorTestCoefficient (μ := μ) ho hc b Φ‖) :
    ∃ q : Lp E 2 (μ.restrict Ω),
      HasWeakFDerivOn ⟨Ω, ho⟩ h
        (fun x => innerSL ℝ ((interiorDistance Ω x)⁻¹ • q x)) μ ∧ ‖q‖ ≤ R := by
  obtain ⟨q, hq, hnorm⟩ := exists_weighted_gradient_of_test_bound ho hc h b hR hb
  exact ⟨q, hasWeakFDerivOn_of_riesz ho hc h q b hq, hnorm⟩
end HitAndRun.Sobolev
