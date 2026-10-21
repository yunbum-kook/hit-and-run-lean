module
public import HitAndRun.Sobolev.ResidualIdentities
public import HitAndRun.Analysis.BabuskaAzizAlgebra
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory HitAndRun.Analysis
open scoped RealInnerProductSpace
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

/-- The last exact algebra/duality step, conditional on the analytic B5 residual
estimate. The premise is explicit until the rough weighted estimate is supplied. -/
theorem constant_le_of_residual_bound (C : ℝ) (hC : 0 ≤ C)
    (hres : ∀ f : K.Target,
      ‖divergenceResidual f (K.rieszField f)‖ ^ 2 ≤ 4 * C *
        ∑ i, ∑ j, if i < j then
          ‖weakPartial (K.rieszField f) i j - weakPartial (K.rieszField f) j i‖ ^ 2 else 0) :
    K.constant ≤ ENNReal.ofReal (1 + 4 * C) := by
  apply energyConstant_le_of_right_inverse_bound K.div (by positivity)
  apply right_inverse_bound_of_adjoint_lower_bound K.div (by positivity)
  intro f
  let u := K.rieszField f
  let h := divergenceResidual f u
  let d := divergence K.ambient K.carrier u
  let G : ℝ := ∑ i, ∑ j, if i < j then ‖weakPartial u i j - weakPartial u j i‖ ^ 2 else 0
  have hG : 0 ≤ G := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs <;> positivity
  have hpair : inner ℝ h d = G := (K.residual_identities f).2.2
  have hcs0 : G ≤ ‖h‖ * ‖d‖ := by rw [← hpair]; exact real_inner_le_norm _ _
  have hcs : G ^ 2 ≤ ‖h‖ ^ 2 * ‖d‖ ^ 2 := by
    have hs := mul_self_le_mul_self hG hcs0
    nlinarith
  have hw : ‖h‖ ^ 2 ≤ 4 * C * G := hres f
  have ha := babuskaAziz_energy_algebra (sq_nonneg ‖d‖) hG hC hw hcs
  have he : ‖u‖ ^ 2 = ‖d‖ ^ 2 + G := divergence_curl_energy u
  have hsum : h + d = (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) := by
    simp [h, d, divergenceResidual]
  have hn : ‖f‖ ^ 2 = ‖h‖ ^ 2 + ‖d‖ ^ 2 + 2 * G := by
    have hh := norm_add_sq_real h d
    rw [hsum, hpair] at hh
    simp only [Submodule.norm_coe] at hh
    linarith
  change ‖f‖ ^ 2 ≤ (1 + 4 * C) * ‖u‖ ^ 2
  rw [hn, he]
  exact ha
end HitAndRun.Sobolev.BoundedOpenDomain
