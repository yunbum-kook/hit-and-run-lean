module
public import HitAndRun.Sobolev.RoughVectorEnergy
public import HitAndRun.Sobolev.WeightedGradientRiesz

/-! Genuine weighted weak gradient from rough L2 skew distributional data.
The global L2 inputs can be the zero extensions of domain data. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry
open scoped BigOperators
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]

theorem exists_weighted_weak_gradient_global
    (hb : Bornology.IsBounded Ω) (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : MemLp h 2 μ)
    (G : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hG : ∀ i j, MemLp (G i j) 2 μ)
    (hskew : ∀ x i j, G i j x = -G j i x)
    (hrel : ∀ i, ∀ φ : testFunctions Ω,
      (∫ x, h x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) ∂μ) =
        ∑ j, ∫ x, G i j x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∂μ) :
    ∃ q : Lp (EuclideanSpace ℝ (Fin n)) 2 (μ.restrict Ω),
      HasWeakFDerivOn ⟨Ω, ho⟩ h
        (fun x => innerSL ℝ ((interiorDistance Ω x)⁻¹ • q x)) μ ∧
      ‖q‖ ^ 2 ≤ 4 * ∫ x, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂μ := by
  let energy := ∫ x, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂μ
  have he : 0 ≤ energy := integral_nonneg fun x => Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  let R := 2 * Real.sqrt energy
  have hR : 0 ≤ R := by positivity
  have hRsq : R ^ 2 = 4 * energy := by
    dsimp [R]
    nlinarith [Real.sq_sqrt he]
  let H : Lp ℝ 2 (μ.restrict Ω) := (hh.restrict Ω).toLp h
  have hHa : (H : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[μ.restrict Ω] h :=
    (hh.restrict Ω).coeFn_toLp
  have hbound (φ : Fin n → testFunctions Ω) :
      |vectorTestFunctional H (EuclideanSpace.basisFun (Fin n) ℝ).toBasis φ| ≤
        R * ‖vectorTestCoefficient (μ := μ) ho hc (EuclideanSpace.basisFun (Fin n) ℝ).toBasis φ‖ := by
    have hfi : vectorTestFunctional H (EuclideanSpace.basisFun (Fin n) ℝ).toBasis φ =
        -∑ i, ∫ x, h x * fderiv ℝ (φ i : EuclideanSpace ℝ (Fin n) → ℝ) x
          (EuclideanSpace.basisFun (Fin n) ℝ i) ∂μ := by
      rw [vectorTestFunctional_eq_integral]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      trans ∫ x in Ω, h x * fderiv ℝ (φ i : EuclideanSpace ℝ (Fin n) → ℝ) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) ∂μ
      · apply integral_congr_ae
        filter_upwards [hHa] with x hx
        rw [hx]
        rfl
      · apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        rw [fderiv_of_notMem_tsupport ℝ (fun hm => hx ((φ i).2.2.2 hm))]
        simp
    have ha := rough_vector_integral_sq_le hb ho hc h hh G hG hskew hrel φ
    have hcn := norm_sq_vectorTestCoefficient_global (μ := μ) ho hc
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis φ
    have hs : (vectorTestFunctional H (EuclideanSpace.basisFun (Fin n) ℝ).toBasis φ) ^ 2 ≤
        R ^ 2 * ‖vectorTestCoefficient (μ := μ) ho hc
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis φ‖ ^ 2 := by
      rw [hfi, neg_sq, hRsq, hcn]
      exact ha
    have hn : 0 ≤ R * ‖vectorTestCoefficient (μ := μ) ho hc
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis φ‖ := mul_nonneg hR (norm_nonneg _)
    nlinarith [sq_abs (vectorTestFunctional H (EuclideanSpace.basisFun (Fin n) ℝ).toBasis φ)]
  obtain ⟨q, hq, hqn⟩ := exists_weak_gradient_of_test_bound ho hc H
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis hR hbound
  refine ⟨q, hq.congr_ae hHa (Filter.EventuallyEq.rfl), ?_⟩
  have hs := pow_le_pow_left₀ (norm_nonneg q) hqn 2
  rwa [hRsq] at hs
end HitAndRun.Sobolev
