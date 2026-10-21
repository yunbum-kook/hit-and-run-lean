module
public import HitAndRun.Geometry.SphereMomentsHilbert
public import HitAndRun.Sobolev.CurlEnergy
@[expose] public section

/-! Actual weak-derivative sphere certificates. These moments do not yet identify
conditional chord operators or prove the source spectral-gap proposition. -/
noncomputable section
namespace HitAndRun.Markov
open MeasureTheory HitAndRun.Geometry HitAndRun.Sobolev
open scoped RealInnerProductSpace
variable {n : ℕ} [NeZero n]
variable {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]
  {Ω : Set (EuclideanSpace ℝ (Fin n))}

def sphereCertificate (u : VectorField μ Ω) (θ : UnitDirection n) :
    Lp ℝ 2 (μ.restrict Ω) := (n : ℝ) • sphereHilbertQuadratic (weakPartial u) θ

theorem weakPartial_diagonal (u : VectorField μ Ω) :
    (∑ i, weakPartial u i i) = divergence μ Ω u := by
  simp only [divergence, sum_apply]
  rfl

theorem weakPartial_cross_sum (u : VectorField μ Ω) :
    (∑ i, ∑ j, inner ℝ (weakPartial u i j) (weakPartial u j i)) =
      ‖divergence μ Ω u‖ ^ 2 := by
  rw [← weakPartial_diagonal, ← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (weakPartial_cross u i j).symm.trans (real_inner_comm _ _)

theorem sphereCertificate_mean (u : VectorField μ Ω) :
    (∫ θ, sphereCertificate u θ ∂uniformSphere n) = divergence μ Ω u := by
  simp only [sphereCertificate, integral_smul, uniformSphere_integral_hilbert_quadratic,
    smul_smul]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [mul_one_div_cancel hn, one_smul, weakPartial_diagonal]

theorem sphereCertificate_energy (u : VectorField μ Ω) :
    (∫ θ, ‖sphereCertificate u θ‖ ^ 2 ∂uniformSphere n) =
      (n : ℝ) / (n + 2) * (2 * ‖divergence μ Ω u‖ ^ 2 + ‖u‖ ^ 2) := by
  simp only [sphereCertificate, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul, uniformSphere_integral_hilbert_quadratic_sq,
    weakPartial_diagonal, ← vectorField_energy, weakPartial_cross_sum]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  <;> ring

end HitAndRun.Markov
