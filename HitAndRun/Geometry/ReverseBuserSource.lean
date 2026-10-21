module
/-
Project-written bridge composing actual hit-and-run definitions and proved
source endpoints. External CvxBody provenance: chewisinho/cvx_body_lean,
commit 41678c03373f8d3ac9d95bab31bcc17022d85bec (private repository).
This staging file does not grant public redistribution permission.
-/
public import HitAndRun.Geometry.ReverseBuserCheegerL1
public import CvxBody.Analysis.MilmanPoincare
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
variable {n : ℕ} [NeZero n]

/-- The source's genuine log-concavity predicate holds for the actual normalized
Lebesgue indicator density of this convex body. -/
theorem uniformDensity_sinho_logConcave (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) :
    OAI.LeanBlast.KLS.IsLogConcaveFunction K.uniformDensity :=
  ⟨K.uniformDensity_nonnegative, K.uniformDensity_log_concave hc⟩

/-- Guide concentration from the actual optimal CPI feeds the proved guided-needle
existence theorem; this is not a concentration or needle-decomposition assumption. -/
theorem uniform_cheeger_from_actual_poincare (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hA : MeasurableSet A) :
    ENNReal.ofReal (1 / (256 * Real.sqrt K.poincareConstant.toReal)) *
      min (uniformMeasure K.carrier A) (1 - uniformMeasure K.carrier A) ≤
        CvxBody.minkowskiContent (uniformMeasure K.carrier) A := by
  letI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  letI := K.uniformDensity_probability
  obtain ⟨hs, hconc⟩ := K.uniform_guide_concentration hc
  by_cases h0 : uniformMeasure K.carrier A = 0
  · simp [h0]
  by_cases h1 : uniformMeasure K.carrier A = 1
  · simp [h1]
  have hmoment : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖)
      (volume.withDensity fun x => ENNReal.ofReal (K.uniformDensity x)) := by
    rw [K.uniformDensity_withDensity]
    exact K.uniform_integrable_lipschitz _ lipschitzWith_one_norm
  have hN : ∃ u, CvxBody.NeedleDecomposition (uniformMeasure K.carrier) A u := by
    rw [← K.uniformDensity_withDensity]
    apply CvxBody.needle_decomposition_exists (K.uniformDensity_sinho_logConcave hc)
      K.uniformDensity_measurable hmoment hA
    · rw [K.uniformDensity_withDensity]
      exact pos_iff_ne_zero.2 h0
    · rw [K.uniformDensity_withDensity]
      exact lt_of_le_of_ne prob_le_one h1
  obtain ⟨u, hD⟩ := hN
  obtain ⟨hu, hR⟩ := hconc u hD.1
  exact CvxBody.cheeger_of_needle_decomposition (uniformMeasure K.carrier) hA hD hs hu hR

/-- Ordinary ambient-C1 L1 reverse Buser with exact coefficient256 and the actual
optimal weak-Sobolev CPI. The median split counts the derivative only once. -/
theorem ordinaryL1ReverseBuserInput_256 (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) : K.OrdinaryL1ReverseBuserInput 256 := by
  letI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  have hs : 0 < Real.sqrt K.poincareConstant.toReal := (K.uniform_guide_concentration hc).1
  have hac : uniformMeasure K.carrier ≪ volume := by
    rw [← K.uniformDensity_withDensity]
    exact withDensity_absolutelyContinuous _ _
  intro f hf
  apply K.uniform_c1_l1_of_bounded_lipschitz (C := 256 * Real.sqrt K.poincareConstant.toReal)
    (fun g L M hg hM => ?_) f hf
  obtain ⟨m, hm⟩ := Geometry.cheeger_l1_median_bounded (uniformMeasure K.carrier) hac
    (h := 1 / (256 * Real.sqrt K.poincareConstant.toReal)) (by positivity)
    (K.uniform_cheeger_from_actual_poincare hc) hg hM
  exact ⟨m, by simpa only [one_div, inv_inv] using hm⟩
end HitAndRun.Sobolev.BoundedOpenDomain

namespace HitAndRun.Geometry
/-- Uniform across dimensions and all bounded nonempty open convex domains, with
no extra analytic premise and no replacement of the actual CPI or C1 test class. -/
theorem universalOrdinaryL1ReverseBuser_256 : UniversalOrdinaryL1ReverseBuser 256 := by
  intro n _ K hc _
  exact K.ordinaryL1ReverseBuserInput_256 hc
end HitAndRun.Geometry
