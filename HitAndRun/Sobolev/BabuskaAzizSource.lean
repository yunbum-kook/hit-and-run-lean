module
public import HitAndRun.Sobolev.RoughWeightedSource
public import HitAndRun.Sobolev.BabuskaAzizComparison
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open scoped BigOperators
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

/-- Actual B5 applied to the Riesz residual; no residual estimate is assumed. -/
theorem constant_le_of_finite_improvedPoincare (hC : K.improvedPoincareConstant < ⊤) :
    K.constant ≤ ENNReal.ofReal (1 + 4 * K.improvedPoincareConstant.toReal) := by
  apply K.constant_le_of_residual_bound _ ENNReal.toReal_nonneg
  intro f
  let u := K.rieszField f
  let h : K.Target := ⟨divergenceResidual f u, divergenceResidual_mean_zero f u⟩
  let G := fun i j x => weakPartial u i j x - weakPartial u j i x
  have hG (i j) : MemLp (G i j) 2 (K.ambient.restrict K.carrier) :=
    (Lp.memLp (weakPartial u i j)).sub (Lp.memLp (weakPartial u j i))
  have hs : ∀ᵐ x ∂K.ambient.restrict K.carrier, ∀ i j, G i j x = -G j i x :=
    Filter.Eventually.of_forall fun x i j => by dsimp [G]; ring
  have hr (i) (φ : testFunctions K.carrier) :
      (∫ x in K.carrier, h.val x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) ∂K.ambient) =
        ∑ j, ∫ x in K.carrier, G i j x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∂K.ambient := by
    have hi := (K.residual_identities f).2.1 φ i
    change (∫ x in K.carrier, h.val x * _ ∂K.ambient) =
      ∑ j, ∫ x in K.carrier, (weakPartial u i j - weakPartial u j i) x * _ ∂K.ambient at hi
    rw [hi]
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (weakPartial u i j) (weakPartial u j i)] with x hx
    rw [hx]
    rfl
  have he (i j) : (∫ x in K.carrier, G i j x ^ 2 ∂K.ambient) =
      ‖weakPartial u i j - weakPartial u j i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (weakPartial u i j) (weakPartial u j i)] with x hx
    rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    rw [hx]
    rfl
  have hInt (i j) : Integrable (fun x => if i < j then G i j x ^ 2 else 0)
      (K.ambient.restrict K.carrier) := by
    split_ifs
    · exact (hG i j).integrable_sq
    · exact integrable_zero _ _ _
  have henergy : (∫ x in K.carrier, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂K.ambient) =
      ∑ i, ∑ j, if i < j then ‖weakPartial u i j - weakPartial u j i‖ ^ 2 else 0 := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hInt i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hInt i j)]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · exact he i j
    · simp
  have hp := K.rough_weighted_poincare hC h G hG hs hr
  rw [henergy] at hp
  exact hp

/-- Source Theorem 1.4, for literal extended optimal constants. Infinite IPI is
handled by the genuine extended inequality, not by replacing infinity with zero. -/
theorem babuskaAziz_le_one_add_four_improvedPoincare :
    K.constant ≤ 1 + 4 * K.improvedPoincareConstant := by
  by_cases hC : K.improvedPoincareConstant < ⊤
  · have h := K.constant_le_of_finite_improvedPoincare hC
    have he : ENNReal.ofReal (1 + 4 * K.improvedPoincareConstant.toReal) =
        1 + 4 * K.improvedPoincareConstant := by
      rw [ENNReal.ofReal_add (by norm_num) (by positivity),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hC.ne]
      norm_num
    simpa only [he] using h
  · have ht : K.improvedPoincareConstant = ⊤ := le_antisymm le_top (le_of_not_gt hC)
    simp [ht]
end HitAndRun.Sobolev.BoundedOpenDomain
