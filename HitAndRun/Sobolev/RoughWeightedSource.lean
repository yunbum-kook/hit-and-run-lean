module
public import HitAndRun.Sobolev.RoughWeightedGradient
public import HitAndRun.Sobolev.WeightedImprovedPoincare
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry Set
open scoped BigOperators
namespace BoundedOpenDomain
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

/-- Replace only a null exceptional set, keeping genuine pointwise skew symmetry. -/
def skewRepresentative (G : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if ∀ a b, G a b x = -G b a x then G i j x else 0

/-- Source B5 rough weighted-gradient assertion, with actual domain L2 data and
only a.e. skew symmetry. No global H1 or smoothness premise is imposed. -/
theorem rough_weighted_gradient
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
      ‖q‖ ^ 2 ≤ 4 * ∫ x in K.carrier, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂K.ambient := by
  let H := K.carrier.indicator (h : EuclideanSpace ℝ (Fin n) → ℝ)
  let A := skewRepresentative G
  let B := fun i j => K.carrier.indicator (A i j)
  have ha (i j) : A i j =ᵐ[K.ambient.restrict K.carrier] G i j := by
    filter_upwards [hskew] with x hx
    simp only [A, skewRepresentative, if_pos hx]
  have hHm : MemLp H 2 K.ambient :=
    (memLp_indicator_iff_restrict K.isOpen.measurableSet.nullMeasurableSet).2 (Lp.memLp h)
  have hBm (i j) : MemLp (B i j) 2 K.ambient :=
    (memLp_indicator_iff_restrict K.isOpen.measurableSet.nullMeasurableSet).2
      ((memLp_congr_ae (ha i j)).2 (hG i j))
  have hBs (x) (i j) : B i j x = -B j i x := by
    by_cases hx : x ∈ K.carrier
    · simp only [B, indicator_of_mem hx]
      by_cases hs : ∀ a b, G a b x = -G b a x
      · simpa only [A, skewRepresentative, if_pos hs] using hs i j
      · simp [A, skewRepresentative, hs]
    · simp [B, indicator_of_notMem hx]
  have hint (f g : EuclideanSpace ℝ (Fin n) → ℝ) :
      (∫ x, K.carrier.indicator f x * g x ∂K.ambient) =
        ∫ x in K.carrier, f x * g x ∂K.ambient := by
    rw [← integral_indicator K.isOpen.measurableSet]
    congr 1
    funext x
    by_cases hx : x ∈ K.carrier <;> simp [hx]
  have hBr (i) (φ : testFunctions K.carrier) :
      (∫ x, H x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) ∂K.ambient) =
        ∑ j, ∫ x, B i j x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∂K.ambient := by
    change (∫ x, K.carrier.indicator h x * _ ∂K.ambient) = _
    rw [hint, hrel i φ]
    apply Finset.sum_congr rfl
    intro j _
    change (∫ x in K.carrier, G i j x * _ ∂K.ambient) =
      ∫ x, K.carrier.indicator (A i j) x * _ ∂K.ambient
    rw [hint]
    apply integral_congr_ae
    filter_upwards [ha i j] with x hx
    rw [hx]
  have hc : K.carrierᶜ.Nonempty := by
    apply Set.nonempty_compl.mpr
    intro he
    exact NormedSpace.unbounded_univ ℝ (EuclideanSpace ℝ (Fin n)) (he ▸ K.isBounded)
  obtain ⟨q, hq, hn⟩ := exists_weighted_weak_gradient_global
    K.isBounded K.isOpen hc H hHm B hBm hBs hBr
  have hHa : H =ᵐ[K.ambient.restrict K.carrier] (h : EuclideanSpace ℝ (Fin n) → ℝ) := by
    filter_upwards [ae_restrict_mem K.isOpen.measurableSet] with x hx
    simp [H, hx]
  have he : (∫ x, ∑ i, ∑ j, if i < j then B i j x ^ 2 else 0 ∂K.ambient) =
      ∫ x in K.carrier, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂K.ambient := by
    have hs : (∫ x in K.carrier, ∑ i, ∑ j, if i < j then B i j x ^ 2 else 0 ∂K.ambient) =
        ∫ x, ∑ i, ∑ j, if i < j then B i j x ^ 2 else 0 ∂K.ambient := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      simp [B, indicator_of_notMem hx]
    rw [← hs]
    apply integral_congr_ae
    filter_upwards [hskew, ae_restrict_mem K.isOpen.measurableSet] with x hx hxm
    simp only [B, A, indicator_of_mem hxm, skewRepresentative, if_pos hx]
  refine ⟨q, hq.congr_ae hHa Filter.EventuallyEq.rfl, ?_⟩
  simpa only [he] using hn

/-- The literal factor-two norm form of the weighted-gradient estimate. -/
theorem rough_weighted_gradient_norm
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
      ‖q‖ ≤ 2 * Real.sqrt (∫ x in K.carrier, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂K.ambient) := by
  obtain ⟨q, hq, hn⟩ := K.rough_weighted_gradient h G hG hskew hrel
  refine ⟨q, hq, ?_⟩
  have he : 0 ≤ ∫ x in K.carrier, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂K.ambient :=
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs <;> positivity
  nlinarith [Real.sq_sqrt he, Real.sqrt_nonneg (∫ x in K.carrier, ∑ i, ∑ j,
    if i < j then G i j x ^ 2 else 0 ∂K.ambient), norm_nonneg q]

/-- Source B5 consequence using the actual finite optimal IPI constant, including
rough residuals that need not belong to global H1. -/
theorem rough_weighted_poincare (hC : K.improvedPoincareConstant < ⊤)
    (h : K.Target) (G : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hG : ∀ i j, MemLp (G i j) 2 (K.ambient.restrict K.carrier))
    (hskew : ∀ᵐ x ∂K.ambient.restrict K.carrier, ∀ i j, G i j x = -G j i x)
    (hrel : ∀ i, ∀ φ : testFunctions K.carrier,
      (∫ x in K.carrier, h.val x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) ∂K.ambient) =
        ∑ j, ∫ x in K.carrier, G i j x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∂K.ambient) :
    ‖h‖ ^ 2 ≤ 4 * K.improvedPoincareConstant.toReal *
      ∫ x in K.carrier, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂K.ambient := by
  obtain ⟨q, hq, hn⟩ := K.rough_weighted_gradient h.val G hG hskew hrel
  have hp := K.improvedPoincare_centered_of_weighted_weak_gradient hC h q hq
  have hm := mul_le_mul_of_nonneg_left hn (show 0 ≤ K.improvedPoincareConstant.toReal from ENNReal.toReal_nonneg)
  nlinarith
end BoundedOpenDomain
end HitAndRun.Sobolev
