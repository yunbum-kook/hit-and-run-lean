module
import HitAndRun.Sobolev.DistanceCutoffEstimate
import HitAndRun.Analysis.FatouBound
open HitAndRun.Geometry HitAndRun.Analysis HitAndRun.Sobolev
#print axioms norm_normed_convolution_sub_le
#print axioms smoothDistanceCutoff_support_domain
#print axioms distanceCutoffSequence_tendsto
#print axioms distanceCutoffSequence_gradient_energy
#print axioms distanceCutoffTest_energy
#print axioms lintegral_bound_of_nonnegative_approximation
#print axioms integral_bound_of_nonnegative_approximation
example {d : ℕ} {μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))} [μ.IsAddHaarMeasure]
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    Filter.Tendsto (fun n => distanceCutoffSequence (μ := μ) Ω n x) Filter.atTop
      (nhds (interiorDistance Ω x)) := distanceCutoffSequence_tendsto Ω x
