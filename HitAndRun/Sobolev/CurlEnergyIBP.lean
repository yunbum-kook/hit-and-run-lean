module

public import HitAndRun.Sobolev.ZeroMean
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Mixed-gradient integration by parts on the genuine H01 graph

The cross-derivative identity is proved on compact smooth functions and then
extended twice through the defining H01 closure. It is not an input hypothesis.
-/

@[expose] public section
noncomputable section

namespace HitAndRun.Sobolev

open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

/-- Differentiating a compact smooth test function stays in the same test space. -/
def derivativeTest (φ : testFunctions Ω) (v : E) : testFunctions Ω :=
  ⟨fun x => fderiv ℝ (φ : E → ℝ) x v,
    ⟨(φ.2.1.fderiv_right (by simp)).clm_apply contDiff_const,
      hasCompactSupport_fderiv_apply_of_mem φ.2 v,
      (tsupport_fderiv_apply_subset ℝ v).trans φ.2.2.2⟩⟩

/-- The mixed directional derivatives commute for a smooth test function. -/
theorem derivativeTest_comm (φ : testFunctions Ω) (a b x : E) :
    fderiv ℝ (derivativeTest φ b : E → ℝ) x a =
      fderiv ℝ (derivativeTest φ a : E → ℝ) x b := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (φ : E → ℝ)) x :=
    (φ.2.1.fderiv_right (m := 1) (by simp)).differentiable (by norm_num) x
  change fderiv ℝ (fun y => fderiv ℝ (φ : E → ℝ) y b) x a =
    fderiv ℝ (fun y => fderiv ℝ (φ : E → ℝ) y a) x b
  rw [fderiv_clm_apply hd (differentiableAt_const b),
    fderiv_clm_apply hd (differentiableAt_const a)]
  simpa using (φ.2.1.contDiffAt (x := x)).isSymmSndFDerivAt (by simp) a b


/-- Twice integrating by parts exchanges the derivative directions. -/
theorem integral_test_cross (φ ψ : testFunctions Ω) (a b : E) :
    (∫ x, fderiv ℝ (φ : E → ℝ) x a * fderiv ℝ (ψ : E → ℝ) x b ∂μ) =
      ∫ x, fderiv ℝ (φ : E → ℝ) x b * fderiv ℝ (ψ : E → ℝ) x a ∂μ := by
  have ha := integral_fderiv_mul_eq_neg (μ := μ) (derivativeTest ψ b) φ a
  have hb := integral_fderiv_mul_eq_neg (μ := μ) (derivativeTest ψ a) φ b
  change (∫ x, fderiv ℝ (φ : E → ℝ) x a * fderiv ℝ (ψ : E → ℝ) x b ∂μ) = _ at ha
  change (∫ x, fderiv ℝ (φ : E → ℝ) x b * fderiv ℝ (ψ : E → ℝ) x a ∂μ) = _ at hb
  rw [ha, hb]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by dsimp only; rw [derivativeTest_comm])

/-- Actual L2 derivative inner products of test graphs satisfy the exchange identity. -/
theorem testGraph_cross (φ ψ : testFunctions Ω) (a b : E) :
    inner ℝ (partialL a (testGraphₗ μ Ω φ)) (partialL b (testGraphₗ μ Ω ψ)) =
      inner ℝ (partialL b (testGraphₗ μ Ω φ)) (partialL a (testGraphₗ μ Ω ψ)) := by
  simp only [partialL_testGraphₗ, partialCls, inner_toLp_toLp, RCLike.inner_apply,
    conj_trivial]
  have he (v w : E) :
      (∫ x in Ω, fderiv ℝ (ψ : E → ℝ) x w * fderiv ℝ (φ : E → ℝ) x v ∂μ) =
      ∫ x, fderiv ℝ (ψ : E → ℝ) x w * fderiv ℝ (φ : E → ℝ) x v ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (φ.2.2.2 h))]
    simp
  rw [he a b, he b a]
  exact integral_test_cross ψ φ b a

/-- Mixed weak-gradient inner products exchange directions on actual H01. -/
theorem h01_cross (u v : H01 μ Ω) (a b : E) :
    inner ℝ (partialL a (u : H1Graph μ Ω)) (partialL b (v : H1Graph μ Ω)) =
      inner ℝ (partialL b (u : H1Graph μ Ω)) (partialL a (v : H1Graph μ Ω)) := by
  apply H01_subset_of_isClosed
    (isClosed_eq ((partialL a).continuous.inner continuous_const)
      ((partialL b).continuous.inner continuous_const)) (fun φ => ?_) u.property
  change inner ℝ (partialL a (testGraphₗ μ Ω φ)) (partialL b (v : H1Graph μ Ω)) =
    inner ℝ (partialL b (testGraphₗ μ Ω φ)) (partialL a (v : H1Graph μ Ω))
  apply H01_subset_of_isClosed
    (isClosed_eq (continuous_const.inner (partialL b).continuous)
      (continuous_const.inner (partialL a).continuous)) (fun ψ => ?_) v.property
  exact testGraph_cross φ ψ a b

end HitAndRun.Sobolev
