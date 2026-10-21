module
/-
Project-written bridge composing actual hit-and-run definitions and proved
source endpoints. External CvxBody provenance: chewisinho/cvx_body_lean,
commit 41678c03373f8d3ac9d95bab31bcc17022d85bec (private repository).
This staging file does not grant public redistribution permission.
-/
public import HitAndRun.Geometry.ReverseBuserSource
public import HitAndRun.Geometry.WeightedPoincareBodySourceExact
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set HitAndRun.Sobolev
open scoped ENNReal Topology
variable {n : ℕ} [NeZero n]

/-- Unconditional S07 on the actual open convex domain, with arbitrary inner-ball center. -/
theorem reverseBuser_arbitrary_center_1036 (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) {r : ℝ} (hr : 0 < r)
    {a : EuclideanSpace ℝ (Fin n)} (hball : Metric.ball a r ⊆ K.carrier)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f) :
    ∃ z : ℝ, (∫ x in K.carrier, |f x-z| ∂K.ambient) ≤
      (1036 * (n : ℝ) * Real.sqrt K.poincareConstant.toReal / r) *
        ∫ x in K.carrier, K.boundaryDistance x * ‖gradient f x‖ ∂K.ambient := by
  simpa only [show (12 + 4 * (256 : ℝ)) = 1036 by norm_num] using
    conditional_reverseBuser_arbitrary_center K hc (K.poincareConstant_lt_top_convex hc)
      (b := 256) (by norm_num) hr hball universalOrdinaryL1ReverseBuser_256 f hf

/-- Unconditional actual improved-PI bound; the coefficient is 4·1036². -/
theorem reverseBuser_arbitrary_center_IPI_4293184 (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) {r : ℝ} (hr : 0 < r)
    {a : EuclideanSpace ℝ (Fin n)} (hball : Metric.ball a r ⊆ K.carrier) :
    K.improvedPoincareConstant ≤ ENNReal.ofReal
      (4293184 * (n : ℝ)^2 * K.poincareConstant.toReal / r^2) := by
  have h := conditional_reverseBuser_arbitrary_center_IPI K hc
    (K.poincareConstant_lt_top_convex hc) (b := 256) (by norm_num) hr hball
    universalOrdinaryL1ReverseBuser_256
  convert h using 1
  congr 1
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  ring

/-- Literal Lebesgue/body S07, with any inner-ball center and ambient locally
Lipschitz functions. No supplied reverse-Buser or finiteness premise remains. -/
theorem reverseBuser_body_1036
    {K : Set (EuclideanSpace ℝ (Fin n))} (hbK : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) (hc : Convex ℝ K)
    {r : ℝ} (hr : 0 < r) {a : EuclideanSpace ℝ (Fin n)}
    (hball : Metric.ball a r ⊆ K)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f) :
    ∃ z : ℝ, (∫ x in K, |f x-z|) ≤
      (1036 * (n : ℝ) * Real.sqrt (bodyInteriorDomain K hbK hi).poincareConstant.toReal / r) *
        ∫ x in K, Metric.infDist x (frontier K) * ‖gradient f x‖ := by
  simpa only [show (12 + 4 * (256 : ℝ)) = 1036 by norm_num] using
    conditional_reverseBuser_body hbK hi hc (b := 256) (by norm_num) hr hball
      universalOrdinaryL1ReverseBuser_256 f hf

/-- Literal S07 infimum form on the whole convex body, not only its interior. -/
theorem reverseBuser_body_infimum_1036
    {K : Set (EuclideanSpace ℝ (Fin n))} (hbK : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) (hc : Convex ℝ K)
    {r : ℝ} (hr : 0 < r) {a : EuclideanSpace ℝ (Fin n)}
    (hball : Metric.ball a r ⊆ K)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f) :
    (⨅ z : ℝ, ∫ x in K, |f x-z|) ≤
      (1036 * (n : ℝ) * Real.sqrt (bodyInteriorDomain K hbK hi).poincareConstant.toReal / r) *
        ∫ x in K, Metric.infDist x (frontier K) * ‖gradient f x‖ := by
  simpa only [show (12 + 4 * (256 : ℝ)) = 1036 by norm_num] using
    conditional_reverseBuser_body_infimum hbK hi hc (b := 256) (by norm_num) hr hball
      universalOrdinaryL1ReverseBuser_256 f hf

/-- Literal S08 with the maximum inscribed radius. Its positive radius and a
maximizing center are constructed by the body theorem, not imposed as premises. -/
theorem reverseBuser_body_maximum_IPI_4293184
    {K : Set (EuclideanSpace ℝ (Fin n))} (hbK : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) (hc : Convex ℝ K) :
    let Ω := bodyInteriorDomain K hbK hi
    let r := sSup {r : ℝ | 0 < r ∧ ∃ c, Metric.ball c r ⊆ K}
    Ω.improvedPoincareConstant ≤ ENNReal.ofReal
      (4293184 * (n : ℝ)^2 * Ω.poincareConstant.toReal / r^2) := by
  have h := conditional_reverseBuser_body_maximum_IPI hbK hi hc (b := 256)
    (by norm_num) universalOrdinaryL1ReverseBuser_256
  dsimp only at h ⊢
  convert h using 1
  congr 1
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  ring
end HitAndRun.Geometry
