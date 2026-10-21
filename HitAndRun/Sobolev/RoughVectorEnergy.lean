module
public import HitAndRun.Sobolev.MollifiedInnerEnergy
public import HitAndRun.Sobolev.InnerTestFamily
public import HitAndRun.Sobolev.MollifiedTestPairing

/-! The rough finite-vector distributional estimate, obtained from genuine
mollification and inner-domain exhaustion without assuming a weak gradient. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph EllipticPdes.Embedding HitAndRun.Geometry
open Filter Topology
open scoped BigOperators Convolution
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]

theorem rough_vector_integral_sq_le (hb : Bornology.IsBounded Ω)
    (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : MemLp h 2 μ)
    (G : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hG : ∀ i j, MemLp (G i j) 2 μ)
    (hskew : ∀ x i j, G i j x = -G j i x)
    (hrel : ∀ i, ∀ φ : testFunctions Ω,
      (∫ x, h x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) ∂μ) =
        ∑ j, ∫ x, G i j x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∂μ)
    (φ : Fin n → testFunctions Ω) :
    (∑ i, ∫ x, h x * fderiv ℝ (φ i : EuclideanSpace ℝ (Fin n) → ℝ) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) ∂μ) ^ 2 ≤
      (4 * ∫ x, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂μ) *
      ∫ x, ‖(interiorDistance Ω x)⁻¹ •
        vectorTestField (EuclideanSpace.basisFun (Fin n) ℝ) φ x‖ ^ 2 ∂μ := by
  obtain ⟨e, he, hm⟩ := finite_test_support_distance_pos ho hc φ
  let rho (k : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := mollifier (half_pos he) k
  let r (k : ℕ) := (rho k).rOut
  have hr (k) : 0 ≤ r k := (rho k).rOut_pos.le
  have hrb (k) : r k ≤ e / 2 := rOut_mollifier_le (half_pos he) k
  have ht : Tendsto r atTop (𝓝 0) := tendsto_rOut_mollifier (half_pos he)
  have hs (k i) (x) (hx : x ∈ tsupport (φ i : EuclideanSpace ℝ (Fin n) → ℝ)) :
      r k < interiorDistance Ω x := (hrb k).trans_lt ((half_lt_self he).trans_le (hm i x hx))
  let Φ (k i) := innerTest (φ i) (hs k i)
  have hpair := (tendsto_mollified_finite_test_pairing (μ := μ) rho ht hh φ
    (EuclideanSpace.basisFun (Fin n) ℝ)).pow 2
  have hcoeff := (vectorTest_inner_energy_tendsto (μ := μ) hc
    (EuclideanSpace.basisFun (Fin n) ℝ) φ he hm hr hrb ht).const_mul
    (4 * ∫ x, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂μ)
  apply le_of_tendsto_of_tendsto' hpair hcoeff
  intro k
  have hci : (innerDomain Ω (r k))ᶜ.Nonempty := hc.mono
    (Set.compl_subset_compl.mpr (innerDomain_subset Ω (hr k)))
  have hk := smooth_vector_integral_sq_le (μ := μ)
    (innerDomain_bounded hb (hr k)) (innerDomain_open Ω (r k)) hci
    (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (rho k).normed μ)
    (contDiff_convolution_normed (rho k) (hh.locallyIntegrable (by norm_num)))
    (EuclideanSpace.basisFun (Fin n) ℝ) (Φ k)
    (mollified_inner_weighted_energy_le hb (rho k) (hr k) le_rfl h hh G hG hskew hrel)
  exact hk
end HitAndRun.Sobolev
