module

public import HitAndRun.Sobolev.Divergence

/-!
# Zero mean of genuine zero-trace derivatives

Compact-smooth integration by parts is extended through the defining H01
closure. No zero-mean assumption is imposed on the divergence.
-/

@[expose] public section

noncomputable section

namespace HitAndRun.Sobolev

open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open scoped BigOperators RealInnerProductSpace

section Scalar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] (Ω : Set E) [IsFiniteMeasure (μ.restrict Ω)]

/-- Integration on L2 for the actual finite restricted measure. -/
def meanCLM : Lp ℝ 2 (μ.restrict Ω) →L[ℝ] ℝ :=
  innerSL ℝ ((memLp_const (1 : ℝ)).toLp (fun _ : E => (1 : ℝ)))

variable {μ Ω}

theorem meanCLM_eq_integral (f : Lp ℝ 2 (μ.restrict Ω)) :
    meanCLM μ Ω f = ∫ x in Ω, f x ∂μ := by
  change inner ℝ ((memLp_const (1 : ℝ)).toLp (fun _ : E => (1 : ℝ))) f = _
  rw [inner_toLp_left]
  simp


omit [Nontrivial E] [IsFiniteMeasure (μ.restrict Ω)] in
/-- The integral of every compactly supported smooth directional derivative is zero. -/
theorem integral_test_partial_zero (φ : testFunctions Ω) (v : E) :
    (∫ x in Ω, fderiv ℝ (φ : E → ℝ) x v ∂μ) = 0 := by
  have h := ((hasWeakFDerivOn_fderiv (Ω := ⊤) (μ := μ)
    (u := fun _ : E => (1 : ℝ)) contDiffOn_const) v).integral_eq
    (contDiff_of_mem φ.2) φ.2.2.1 (by simp)
  have hz : (∫ x, fderiv ℝ (φ : E → ℝ) x v ∂μ) = 0 := by simpa using h
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hz
  · intro x hx
    exact by rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (φ.2.2.2 h))]; simp

/-- Closure transfers the zero integral to every genuine zero-trace weak derivative. -/
theorem h01_partial_mean_zero (u : H01 μ Ω) (v : E) :
    meanCLM μ Ω (partialL v (u : H1Graph μ Ω)) = 0 := by
  apply H01_subset_of_isClosed
    (isClosed_eq ((meanCLM μ Ω).continuous.comp (partialL v).continuous) continuous_const)
    (fun φ => ?_) u.property
  change meanCLM μ Ω (partialL v (testGraphₗ μ Ω φ)) = 0
  rw [meanCLM_eq_integral, partialL_testGraphₗ]
  rw [integral_congr_ae (coeFn_partialCls φ v)]
  exact integral_test_partial_zero φ v

/-- Any gradient-range element inherits the actual zero integral in every direction. -/
theorem gradient_partial_mean_zero (w : gradientSpace μ Ω) (v : E) :
    meanCLM μ Ω ((innerSL ℝ v).compLpL 2 (μ.restrict Ω) (w : Lp E 2 (μ.restrict Ω))) = 0 := by
  rcases w.property with ⟨u, hu⟩
  rw [← hu]
  exact h01_partial_mean_zero u v

end Scalar

section Vector
variable {n : ℕ} [NeZero n]
variable {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure] {Ω : Set (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure (μ.restrict Ω)]

/-- The actual divergence has zero mean; this is proved, not part of its input. -/
theorem divergence_mean_zero (u : VectorField μ Ω) :
    meanCLM μ Ω (divergence μ Ω u) = 0 := by
  simp only [divergence, sum_apply, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact gradient_partial_mean_zero (u i) (EuclideanSpace.basisFun (Fin n) ℝ i)

/-- Centered L2 is the closed kernel of integration for the actual measure. -/
def centeredL2 : Submodule ℝ (Lp ℝ 2 (μ.restrict Ω)) := (meanCLM μ Ω).ker

/-- The genuine divergence with its proved centered codomain. -/
def centeredDivergence : VectorField μ Ω →L[ℝ] centeredL2 (μ := μ) (Ω := Ω) :=
  (divergence μ Ω).codRestrict _ (fun u => divergence_mean_zero u)

end Vector
end HitAndRun.Sobolev
