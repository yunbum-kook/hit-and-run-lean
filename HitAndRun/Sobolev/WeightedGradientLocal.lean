module
public import HitAndRun.Sobolev.BoundaryTest
public import HitAndRun.External.EllipticPDE.Sobolev.WeakDeriv
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! A genuine local weak gradient from the actual weighted test pairing.
Only local integrability of the unweighted gradient is asserted. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

theorem continuousOn_inv_interiorDistance (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty) :
    ContinuousOn (fun x => (interiorDistance Ω x)⁻¹) Ω := by
  apply (interiorDistance_lipschitz Ω).continuous.continuousOn.inv₀
  intro x hx
  exact ((ho.isClosed_compl.notMem_iff_infDist_pos hc).mp (by simpa using hx)).ne'

theorem locallyIntegrableOn_unweightedGradient (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    {q : E → E} (hq : MemLp q 2 (μ.restrict Ω)) :
    LocallyIntegrableOn (fun x => (interiorDistance Ω x)⁻¹ • q x) Ω μ := by
  apply LocallyIntegrableOn.continuousOn_smul ho.isLocallyClosed
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hq.locallyIntegrable (by norm_num)))
  exact continuousOn_inv_interiorDistance ho hc

/-- The actual test identity determines a weak gradient on every compact interior set.
The unweighted gradient need not belong to global L2. -/
theorem hasWeakFDerivOn_of_weighted_test_pairing (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    {h : E → ℝ} {q : E → E} (hh : MemLp h 2 (μ.restrict Ω))
    (hq : MemLp q 2 (μ.restrict Ω))
    (hp : ∀ φ : testFunctions Ω, ∀ v : E,
      (∫ x in Ω, h x * fderiv ℝ (φ : E → ℝ) x v ∂μ) =
        -∫ x in Ω, boundaryTest φ x * inner ℝ (q x) v ∂μ) :
    HasWeakFDerivOn ⟨Ω, ho⟩ h
      (fun x => innerSL ℝ ((interiorDistance Ω x)⁻¹ • q x)) μ := by
  intro v
  apply hasWeakLineDerivOn_iff.mpr
  refine ⟨locallyIntegrableOn_of_locallyIntegrable_restrict
    (hh.locallyIntegrable (by norm_num)), ?_, ?_⟩
  · have hi := (innerSL ℝ v).locallyIntegrableOn_comp
      (locallyIntegrableOn_unweightedGradient ho hc hq)
    change LocallyIntegrableOn
      (fun x => inner ℝ v ((interiorDistance Ω x)⁻¹ • q x)) Ω μ at hi
    convert hi using 1
    ext x
    exact real_inner_comm _ _
  · intro φ hφ hcompact hs
    let ψ : testFunctions Ω := ⟨φ, hφ, hcompact, hs⟩
    have he := hp ψ v
    have hl : (∫ x in Ω, h x * fderiv ℝ φ x v ∂μ) =
        ∫ x, h x * fderiv ℝ φ x v ∂μ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [fderiv_of_notMem_tsupport ℝ (fun ht => hx (hs ht))]
      simp
    have hr : (∫ x in Ω, boundaryTest ψ x * inner ℝ (q x) v ∂μ) =
        ∫ x, boundaryTest ψ x * inner ℝ (q x) v ∂μ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))
      simp [boundaryTest, ψ, hz]
    change (∫ x in Ω, h x * fderiv ℝ φ x v ∂μ) = _ at he
    rw [hl, hr] at he
    simpa only [smul_eq_mul, innerSL_apply_apply, real_inner_smul_left,
      boundaryTest, ψ, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using he
end HitAndRun.Sobolev
