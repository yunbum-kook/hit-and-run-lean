module
public import HitAndRun.Geometry.WeightedPoincareRadial
public import HitAndRun.Geometry.WeightedPoincareRadialTransport
@[expose] public section
open MeasureTheory Set Filter HitAndRun.Geometry
open scoped Pointwise Topology
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (x : E) {a : ℝ} (ha : a ≤ 1) :
    ‖f x - f (a • x)‖ ≤ ∫ t in a..1, ‖x‖ * ‖fderiv ℝ f (t • x)‖ :=
  radial_norm_sub_le_integral f hf x ha
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [SFinite μ]
    {K : Set E} (hc : Convex ℝ K) (ho : IsOpen K) (hzero : (0 : E) ∈ K)
    {h : E → ℝ} (hh : IntegrableOn h K μ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (∫ t in Ioo a 1, ∫ y in t • K, h y ∂μ) =
      ∫ y in K, h y * (1 - max a (gauge K y)) ∂μ :=
  integral_dilated_body_residence μ hc ho hzero hh ha0 ha1
#print axioms HitAndRun.Geometry.radial_norm_sub_le_integral
#print axioms HitAndRun.Geometry.integral_radial_residence_length
#print axioms HitAndRun.Geometry.integral_radial_residence
#print axioms HitAndRun.Geometry.integral_dilated_body_residence

#print axioms HitAndRun.Geometry.radial_homothety_integral_le
#print axioms HitAndRun.Geometry.radial_residence_weight_le
#print axioms HitAndRun.Geometry.integral_radial_residence_le_boundary
