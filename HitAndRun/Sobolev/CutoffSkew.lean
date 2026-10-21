module
public import HitAndRun.Sobolev.CurlEnergyIBP
public import HitAndRun.Analysis.SkewEnergy

/-! Compact smooth cutoff tests for the weighted estimate. These lemmas do not
replace the source's nonsmooth distance function by a smoothness assumption. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Set E}

/-- The genuine compactly supported test eta² times a directional derivative. -/
def cutoffDerivativeTest (eta : testFunctions Ω) (h : E → ℝ)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (v : E) : testFunctions Ω :=
  ⟨fun x => (eta : E → ℝ) x * (eta : E → ℝ) x * fderiv ℝ h x v,
    ⟨(eta.2.1.mul eta.2.1).mul ((hh.fderiv_right (by simp)).clm_apply contDiff_const),
      eta.2.2.1.mul_right.mul_right,
      tsupport_mul_subset_left.trans (tsupport_mul_subset_left.trans eta.2.2.2)⟩⟩

/-- Exact differentiated cutoff test, including the Hessian term. -/
theorem fderiv_cutoffDerivativeTest (eta : testFunctions Ω) (h : E → ℝ)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (v w x : E) :
    fderiv ℝ (cutoffDerivativeTest eta h hh v : E → ℝ) x w =
      2 * (eta : E → ℝ) x * fderiv ℝ (eta : E → ℝ) x w * fderiv ℝ h x v +
        ((eta : E → ℝ) x) ^ 2 * fderiv ℝ (fun y => fderiv ℝ h y v) x w := by
  have he := eta.2.1.differentiable (by simp) x
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ h y v) x :=
    (((hh.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const).differentiable
      (by norm_num)) x
  change fderiv ℝ (((eta : E → ℝ) * (eta : E → ℝ)) *
    (fun y => fderiv ℝ h y v)) x w = _
  rw [fderiv_mul (he.mul he) hd, fderiv_mul he he]
  simp only [add_apply, smul_apply, smul_eq_mul, Pi.mul_apply]
  ring

/-- Testing a genuine distributional divergence relation with the compact cutoff.
The Hessian cancellation and distance-cutoff limit are separate later steps. -/
theorem cutoff_weak_identity {ι : Type*} [Fintype ι]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    (eta : testFunctions Ω) (h : E → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (v : E) (b : ι → E) (G : ι → E → ℝ)
    (hrel : ∀ φ : testFunctions Ω,
      (∫ x, h x * fderiv ℝ (φ : E → ℝ) x v ∂μ) =
        ∑ j, ∫ x, G j x * fderiv ℝ (φ : E → ℝ) x (b j) ∂μ) :
    (∫ x, ((eta : E → ℝ) x) ^ 2 * (fderiv ℝ h x v) ^ 2 ∂μ) =
      -∑ j, ∫ x, G j x *
        (2 * (eta : E → ℝ) x * fderiv ℝ (eta : E → ℝ) x (b j) * fderiv ℝ h x v +
          ((eta : E → ℝ) x) ^ 2 * fderiv ℝ (fun y => fderiv ℝ h y v) x (b j)) ∂μ := by
  let φ := cutoffDerivativeTest eta h hh v
  have hw := (hasWeakFDerivOn_fderiv (μ := μ) (Ω := ⊤)
    (hh.of_le (by simp)).contDiffOn v).integral_eq
      φ.2.1 φ.2.2.1 (Set.subset_univ _)
  have hr := hrel φ
  have he : (∫ x, (φ : E → ℝ) x * fderiv ℝ h x v ∂μ) =
      -∑ j, ∫ x, G j x * fderiv ℝ (φ : E → ℝ) x (b j) ∂μ := by
    simp only [smul_eq_mul, mul_comm] at hw
    linarith
  calc
    _ = ∫ x, (φ : E → ℝ) x * fderiv ℝ h x v ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by dsimp [φ, cutoffDerivativeTest]; ring)
    _ = _ := by
      rw [he]
      simp only [φ, fderiv_cutoffDerivativeTest]
end HitAndRun.Sobolev
