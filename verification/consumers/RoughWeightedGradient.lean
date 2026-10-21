import HitAndRun.Sobolev.RoughWeightedGradient
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry HitAndRun.Sobolev
open scoped BigOperators
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]
example
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
      ‖q‖ ^ 2 ≤ 4 * ∫ x, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂μ := exists_weighted_weak_gradient_global hb ho hc h hh G hG hskew hrel
#print axioms HitAndRun.Analysis.integral_sq_inv_smul_tendsto
#print axioms HitAndRun.Sobolev.vectorTestFunctional_eq_integral
#print axioms HitAndRun.Sobolev.coeFn_vectorTestCoefficient
#print axioms HitAndRun.Sobolev.norm_sq_vectorTestCoefficient
#print axioms HitAndRun.Sobolev.vectorTestField_continuous
#print axioms HitAndRun.Sobolev.vectorTestField_compact
#print axioms HitAndRun.Sobolev.vectorTestField_support
#print axioms HitAndRun.Sobolev.norm_sq_vectorTestCoefficient_global
#print axioms HitAndRun.Sobolev.vectorTest_inner_energy_tendsto
#print axioms HitAndRun.Sobolev.smooth_vectorTestFunctional_eq_global
#print axioms HitAndRun.Sobolev.smooth_vector_integral_sq_le
#print axioms HitAndRun.Sobolev.mollified_inner_weighted_energy_le
#print axioms HitAndRun.Sobolev.finite_test_support_distance_pos
#print axioms HitAndRun.Sobolev.rough_vector_integral_sq_le
#print axioms HitAndRun.Sobolev.exists_weighted_weak_gradient_global
