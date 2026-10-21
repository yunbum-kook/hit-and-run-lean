module
public import HitAndRun.Sobolev.RoughWeightedSource
@[expose] public section
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry HitAndRun.Sobolev
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
example
    (h : Lp ℝ 2 (K.ambient.restrict K.carrier))
    (G : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hG : ∀ i j, MemLp (G i j) 2 (K.ambient.restrict K.carrier))
    (hskew : ∀ᵐ x ∂K.ambient.restrict K.carrier, ∀ i j, G i j x = -G j i x)
    (hrel : ∀ i, ∀ φ : testFunctions K.carrier,
      (∫ x in K.carrier, h x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) ∂K.ambient) =
        ∑ j, ∫ x in K.carrier, G i j x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∂K.ambient) :
    ∃ q : Lp (EuclideanSpace ℝ (Fin n)) 2 (K.ambient.restrict K.carrier),
      HasWeakFDerivOn ⟨K.carrier, K.isOpen⟩ h
        (fun x => innerSL ℝ ((interiorDistance K.carrier x)⁻¹ • q x)) K.ambient ∧
      ‖q‖ ^ 2 ≤ 4 * ∫ x in K.carrier, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂K.ambient := K.rough_weighted_gradient h G hG hskew hrel

#print axioms HitAndRun.Sobolev.BoundedOpenDomain.rough_weighted_gradient
example
    (h : Lp ℝ 2 (K.ambient.restrict K.carrier))
    (G : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hG : ∀ i j, MemLp (G i j) 2 (K.ambient.restrict K.carrier))
    (hskew : ∀ᵐ x ∂K.ambient.restrict K.carrier, ∀ i j, G i j x = -G j i x)
    (hrel : ∀ i, ∀ φ : testFunctions K.carrier,
      (∫ x in K.carrier, h x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) ∂K.ambient) =
        ∑ j, ∫ x in K.carrier, G i j x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∂K.ambient) :
    ∃ q : Lp (EuclideanSpace ℝ (Fin n)) 2 (K.ambient.restrict K.carrier),
      HasWeakFDerivOn ⟨K.carrier, K.isOpen⟩ h
        (fun x => innerSL ℝ ((interiorDistance K.carrier x)⁻¹ • q x)) K.ambient ∧
      ‖q‖ ≤ 2 * Real.sqrt (∫ x in K.carrier, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂K.ambient) := K.rough_weighted_gradient_norm h G hG hskew hrel

#print axioms HitAndRun.Sobolev.BoundedOpenDomain.rough_weighted_gradient_norm
example (hC : K.improvedPoincareConstant < ⊤)
    (h : K.Target) (G : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hG : ∀ i j, MemLp (G i j) 2 (K.ambient.restrict K.carrier))
    (hskew : ∀ᵐ x ∂K.ambient.restrict K.carrier, ∀ i j, G i j x = -G j i x)
    (hrel : ∀ i, ∀ φ : testFunctions K.carrier,
      (∫ x in K.carrier, h.val x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) ∂K.ambient) =
        ∑ j, ∫ x in K.carrier, G i j x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∂K.ambient) :
    ‖h‖ ^ 2 ≤ 4 * K.improvedPoincareConstant.toReal *
      ∫ x in K.carrier, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂K.ambient := K.rough_weighted_poincare hC h G hG hskew hrel

#print axioms HitAndRun.Sobolev.BoundedOpenDomain.rough_weighted_poincare
