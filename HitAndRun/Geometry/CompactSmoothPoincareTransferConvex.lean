module
public import HitAndRun.Geometry.CompactSmoothPoincareTransfer
public import HitAndRun.Geometry.CovarianceAffineTransportSmoothPI
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n : ℕ} [NeZero n]

/-- An explicitly supplied compact ambient C∞ PI inequality extends to every
actual W12 graph on any bounded open convex domain, without a centroid condition. -/
theorem CompactSmoothPoincareBound.isPoincareConstant
    {K : BoundedOpenDomain n} {C : ℝ} (h : K.CompactSmoothPoincareBound C)
    (hC : 0 ≤ C) (hc : Convex ℝ K.carrier) :
    K.IsPoincareConstant (ENNReal.ofReal C) :=
  K.isPoincareConstant_of_smooth_bound_convex hc hC h.smooth_bound

/-- The least actual Sobolev PI constant is bounded by the supplied compact-test bound. -/
theorem CompactSmoothPoincareBound.poincareConstant_le
    {K : BoundedOpenDomain n} {C : ℝ} (h : K.CompactSmoothPoincareBound C)
    (hC : 0 ≤ C) (hc : Convex ℝ K.carrier) :
    K.poincareConstant ≤ ENNReal.ofReal C :=
  K.poincareConstant_le (h.isPoincareConstant hC hc)

/-- Real-valued CPI comparison after the actual ENNReal least-constant comparison. -/
theorem CompactSmoothPoincareBound.poincareConstant_toReal_le
    {K : BoundedOpenDomain n} {C : ℝ} (h : K.CompactSmoothPoincareBound C)
    (hC : 0 ≤ C) (hc : Convex ℝ K.carrier) :
    K.poincareConstant.toReal ≤ C := by
  have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h.poincareConstant_le hC hc)
  simpa only [ENNReal.toReal_ofReal hC] using he

end HitAndRun.Sobolev.BoundedOpenDomain
