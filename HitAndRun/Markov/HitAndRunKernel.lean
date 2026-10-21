module
public import HitAndRun.Markov.BodyChordKernel
public import HitAndRun.Geometry.UniformSphere
public import Mathlib.Probability.Kernel.Composition.Prod
@[expose] public section

namespace HitAndRun.Markov
open Set MeasureTheory ProbabilityTheory HitAndRun.Geometry
open scoped ProbabilityTheory
variable {n : ℕ} [NeZero n]

/-- Given a body point and a unit direction, perform the actual uniform chord step. -/
noncomputable def randomDirectionKernel (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : MeasurableSet K) : Kernel (K × UnitDirection n) K :=
  (bodyChordKernel K hK).comap
    (fun p => (⟨(p.1.val, p.2.val), p.1.property,
      by simpa only [Metric.mem_sphere, dist_zero_right] using p.2.property⟩ : ChordParameter K))
    ((measurable_fst.subtype_val.prodMk measurable_snd.subtype_val).subtype_mk)

theorem randomDirectionKernel_markov {K : Set (EuclideanSpace ℝ (Fin n))}
    (ho : IsOpen K) (hb : Bornology.IsBounded K) :
    IsMarkovKernel (randomDirectionKernel K ho.measurableSet) := by
  letI := bodyChordKernel_markov ho hb
  unfold randomDirectionKernel
  infer_instance

/-- Hit-and-Run: sample an independent uniform spherical direction, then its uniform chord.
This is a definition of the actual Markov algorithm, not a spectral-gap assumption. -/
noncomputable def hitAndRun (K : Set (EuclideanSpace ℝ (Fin n)))
    (ho : IsOpen K) (hb : Bornology.IsBounded K) : Kernel K K :=
  letI := uniformSphere_probability n
  letI := randomDirectionKernel_markov ho hb
  randomDirectionKernel K ho.measurableSet ∘ₖ
    (Kernel.id ×ₖ Kernel.const K (uniformSphere n))

theorem hitAndRun_markov {K : Set (EuclideanSpace ℝ (Fin n))}
    (ho : IsOpen K) (hb : Bornology.IsBounded K) : IsMarkovKernel (hitAndRun K ho hb) := by
  letI := uniformSphere_probability n
  letI := randomDirectionKernel_markov ho hb
  unfold hitAndRun
  infer_instance
end HitAndRun.Markov
