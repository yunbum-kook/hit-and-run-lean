module

public import HitAndRun.Sobolev.CurlEnergyResidual

/-! Distributional part of source Lemma B.4 on actual weak gradients. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open scoped BigOperators RealInnerProductSpace
variable {n : ℕ} [NeZero n]
variable {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]
  {Ω : Set (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure (μ.restrict Ω)]

/-- Coordinate polarization of the genuine L2 vector-field inner product. -/
theorem lp_coordinate_inner
    (g h : Lp (EuclideanSpace ℝ (Fin n)) 2 (μ.restrict Ω)) :
    (∑ j : Fin n, inner ℝ
      ((innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).compLpL 2 (μ.restrict Ω) g)
      ((innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).compLpL 2 (μ.restrict Ω) h)) =
      inner ℝ g h := by
  have ha := lp_coordinate_energy (g + h)
  simp only [map_add, norm_add_sq_real, Finset.sum_add_distrib, ← Finset.mul_sum] at ha
  rw [lp_coordinate_energy g, lp_coordinate_energy h] at ha
  linarith

/-- The actual gradient of a compact smooth test function belongs to the gradient range. -/
def testGradient (φ : testFunctions Ω) : gradientSpace μ Ω :=
  ⟨gradCls μ Ω φ, ⟨⟨testGraphₗ μ Ω φ, testGraphₗ_mem_H01 φ⟩, rfl⟩⟩

/-- Test vector with only coordinate i nonzero. -/
def testVector (φ : testFunctions Ω) (i : Fin n) : VectorField μ Ω :=
  PiLp.single 2 i (testGradient φ)

theorem divergence_testVector (φ : testFunctions Ω) (i : Fin n) :
    divergence μ Ω (testVector φ i) = partialCls μ Ω φ (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  simp only [divergence, sum_apply]
  rw [Finset.sum_eq_single i]
  · simpa [diagonalDerivative, testVector, testGradient, partialL] using
      (partialL_testGraphₗ (μ := μ) (EuclideanSpace.basisFun (Fin n) ℝ i) φ)
  · intro j _ hji
    simp [diagonalDerivative, testVector, hji]
  · simp

theorem inner_testVector (u : VectorField μ Ω) (φ : testFunctions Ω) (i : Fin n) :
    inner ℝ u (testVector φ i) =
      ∑ j : Fin n, inner ℝ (weakPartial u i j)
        (partialCls μ Ω φ (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  have hi : inner ℝ u (testVector φ i) =
      inner ℝ ((u i : gradientSpace μ Ω) : Lp (EuclideanSpace ℝ (Fin n)) 2 (μ.restrict Ω))
        (gradCls μ Ω φ) := by
    simp only [testVector, PiLp.inner_apply]
    rw [Finset.sum_eq_single i]
    · rw [PiLp.single_eq_same]
      rfl
    · intro j _ hji
      simp [hji]
    · simp
  rw [hi]
  have h := (lp_coordinate_inner
    ((u i : gradientSpace μ Ω) : Lp (EuclideanSpace ℝ (Fin n)) 2 (μ.restrict Ω))
    (gradCls μ Ω φ)).symm
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact (partialL_testGraphₗ (EuclideanSpace.basisFun (Fin n) ℝ j) φ).symm

/-- Mixed-gradient integration by parts with an actual compact smooth test. -/
theorem weakPartial_test_cross (u : VectorField μ Ω) (φ : testFunctions Ω) (i j : Fin n) :
    inner ℝ (weakPartial u j j) (partialCls μ Ω φ (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      inner ℝ (weakPartial u j i) (partialCls μ Ω φ (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  rcases (u j).property with ⟨v, hv⟩
  have h := h01_cross v ⟨testGraphₗ μ Ω φ, testGraphₗ_mem_H01 φ⟩
    (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i)
  simp only [partialL_testGraphₗ] at h
  unfold weakPartial
  rw [← hv]
  exact h

/-- Source B.4(ii): the weak identity ∂i h = Σj ∂j Gij, with
Gij = ∂j ui - ∂i uj. Both distributional derivatives contribute a minus sign. -/
theorem divergenceResidual_distribution (f : centeredL2 (μ := μ) (Ω := Ω))
    (u : VectorField μ Ω)
    (hu : ∀ v : VectorField μ Ω, inner ℝ f (centeredDivergence v) = inner ℝ u v)
    (φ : testFunctions Ω) (i : Fin n) :
    inner ℝ (divergenceResidual f u)
      (partialCls μ Ω φ (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      ∑ j : Fin n, inner ℝ (weakPartial u i j - weakPartial u j i)
        (partialCls μ Ω φ (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  have hr := hu (testVector φ i)
  change inner ℝ (f : Lp ℝ 2 (μ.restrict Ω)) (divergence μ Ω (testVector φ i)) = _ at hr
  rw [divergence_testVector, inner_testVector] at hr
  rw [divergenceResidual, inner_sub_left, hr]
  have hd : divergence μ Ω u = ∑ j : Fin n, weakPartial u j j := by
    simp only [divergence, sum_apply]
    rfl
  rw [hd, sum_inner]
  simp_rw [weakPartial_test_cross u φ i, inner_sub_left]
  simp only [Finset.sum_sub_distrib]
/-- L2 pairing with a test derivative is its actual distributional test integral. -/
theorem inner_partialCls_integral (g : Lp ℝ 2 (μ.restrict Ω))
    (φ : testFunctions Ω) (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ g (partialCls μ Ω φ v) =
      ∫ x in Ω, g x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x v ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_partialCls (μ := μ) φ v] with x hx
  simp [hx, mul_comm]

/-- Explicit integral formulation of ∇h=divG, without a classical derivative premise. -/
theorem divergenceResidual_distribution_integral (f : centeredL2 (μ := μ) (Ω := Ω))
    (u : VectorField μ Ω)
    (hu : ∀ v : VectorField μ Ω, inner ℝ f (centeredDivergence v) = inner ℝ u v)
    (φ : testFunctions Ω) (i : Fin n) :
    (∫ x in Ω, divergenceResidual f u x *
      fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x (EuclideanSpace.basisFun (Fin n) ℝ i) ∂μ) =
      ∑ j : Fin n, ∫ x in Ω, (weakPartial u i j - weakPartial u j i) x *
        fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x (EuclideanSpace.basisFun (Fin n) ℝ j) ∂μ := by
  simpa only [inner_partialCls_integral] using divergenceResidual_distribution f u hu φ i
end HitAndRun.Sobolev
