module
public import HitAndRun.Markov.DirectionalAnnihilationCertificate
public import HitAndRun.Analysis.IntegralCertificate
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
@[expose] public section
noncomputable section
namespace HitAndRun.Markov
open MeasureTheory HitAndRun.Geometry HitAndRun.Sobolev HitAndRun.Analysis
open scoped RealInnerProductSpace
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

def directionalResidual (f : Lp ℝ 2 (K.ambient.restrict K.carrier))
    (θ : UnitDirection n) : Lp ℝ 2 (K.ambient.restrict K.carrier) :=
  f - conditionalProjection (directionalSigma_le θ) f

theorem sphereCertificate_continuous (u : K.Field) : Continuous (sphereCertificate u) := by
  unfold sphereCertificate sphereHilbertQuadratic
  fun_prop

theorem sphereCertificate_memLp (u : K.Field) : MemLp (sphereCertificate u) 2 (uniformSphere n) := by
  letI := uniformSphere_probability n
  letI : CompactSpace (UnitDirection n) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  exact (sphereCertificate_continuous K u).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The analytic HAR comparison for the actual directional projections. The
remaining measurability premise must be supplied by the actual chord-kernel
identification before this becomes a source spectral-gap endpoint. -/
theorem directional_energy_comparison (hC : K.constant < ⊤) (f : K.Target)
    (hr : MemLp (directionalResidual K f) 2 (uniformSphere n)) :
    ‖f‖ ^ 2 ≤ ((n : ℝ) / (n + 2) * (2 + K.constant.toReal)) *
      ∫ θ, ‖directionalResidual K f θ‖ ^ 2 ∂uniformSphere n := by
  obtain ⟨u, hu, he⟩ := K.attained_solver hC f
  have hd : divergence K.ambient K.carrier u = (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :=
    congrArg Subtype.val hu
  have hg := sphereCertificate_memLp K u
  have hmean : (∫ θ, sphereCertificate u θ ∂uniformSphere n) =
      (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) := (sphereCertificate_mean u).trans hd
  have hp : (∫ θ, inner ℝ (directionalResidual K f θ) (sphereCertificate u θ)
      ∂uniformSphere n) = ‖f‖ ^ 2 := by
    have hpoint (θ : UnitDirection n) :
        inner ℝ (directionalResidual K f θ) (sphereCertificate u θ) =
          inner ℝ (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) (sphereCertificate u θ) := by
      simp only [directionalResidual, inner_sub_left, conditionalProjection_symmetric,
        sphereCertificate_directional_projection, inner_zero_right, sub_zero]
    simp_rw [hpoint]
    letI := uniformSphere_probability n
    rw [integral_inner (memLp_one_iff_integrable.mp (hg.mono_exponent (by norm_num))),
      hmean, real_inner_self_eq_norm_sq, Submodule.norm_coe]
  have hb : (∫ θ, ‖sphereCertificate u θ‖ ^ 2 ∂uniformSphere n) ≤
      ((n : ℝ) / (n + 2) * (2 + K.constant.toReal)) * ‖f‖ ^ 2 := by
    rw [sphereCertificate_energy, hd, Submodule.norm_coe]
    have hn : 0 ≤ (n : ℝ) / (n + 2) := by positivity
    have h := mul_le_mul_of_nonneg_left he hn
    nlinarith
  exact integral_certificate_energy _ _ hr hg _ _ (sq_nonneg _) (by positivity) hp hb
end HitAndRun.Markov
