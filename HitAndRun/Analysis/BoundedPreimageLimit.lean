module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.LinearAlgebra.Isomorphisms

/-! Pointwise bounded preimages from an adjoint functional estimate. This is a
Riesz/Hahn–Banach substitute for introducing a separate weak topology. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Analysis
open scoped RealInnerProductSpace
variable {V Q : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]

theorem exists_bounded_preimage_of_adjoint_pairing
    (T : V →L[ℝ] Q) (y : Q) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ z : Q, |inner ℝ y z| ≤ R * ‖T.adjoint z‖) :
    ∃ x : V, T x = y ∧ ‖x‖ ≤ R := by
  let A := T.adjoint.toLinearMap
  let f := A.rangeRestrict
  let g := (innerSL ℝ y).toLinearMap
  have hk : LinearMap.ker f ≤ LinearMap.ker g := by
    intro z hz
    have hz' : T.adjoint z = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hz)
    have h := hb z
    rw [hz', norm_zero, mul_zero] at h
    exact LinearMap.mem_ker.mpr (abs_nonpos_iff.mp h)
  let l := f.liftOfSurjective A.surjective_rangeRestrict ⟨g, hk⟩
  have hl (z : Q) : l (f z) = inner ℝ y z :=
    LinearMap.equivOfSurjective_apply _ _
  have hn (v : LinearMap.range A) : ‖l v‖ ≤ R * ‖v‖ := by
    obtain ⟨z, rfl⟩ := A.surjective_rangeRestrict v
    rw [hl]
    exact hb z
  let L := l.mkContinuous R hn
  obtain ⟨F, hF, hFn⟩ := exists_extension_norm_eq (LinearMap.range A) L
  let x := (InnerProductSpace.toDual ℝ V).symm F
  refine ⟨x, ?_, ?_⟩
  · apply ext_inner_right ℝ
    intro z
    calc
      inner ℝ (T x) z = inner ℝ x (T.adjoint z) := (T.adjoint_inner_right x z).symm
      _ = F (T.adjoint z) := InnerProductSpace.toDual_symm_apply
      _ = L (f z) := hF (f z)
      _ = inner ℝ y z := hl z
  · calc
      ‖x‖ = ‖F‖ := (InnerProductSpace.toDual ℝ V).symm.norm_map F
      _ = ‖L‖ := hFn
      _ ≤ R := l.mkContinuous_norm_le hR hn

/-- Norm limits of images with uniformly bounded preimages still have a preimage
with the same bound, without assuming that the whole operator range is closed. -/
theorem exists_bounded_preimage_of_tendsto
    (T : V →L[ℝ] Q) (u : ℕ → V) (y : Q) {R : ℝ} (hR : 0 ≤ R)
    (hu : ∀ k, ‖u k‖ ≤ R)
    (hy : Filter.Tendsto (fun k => T (u k)) Filter.atTop (nhds y)) :
    ∃ x : V, T x = y ∧ ‖x‖ ≤ R := by
  apply exists_bounded_preimage_of_adjoint_pairing T y hR
  intro z
  apply le_of_tendsto ((hy.inner tendsto_const_nhds).abs)
  exact Filter.Eventually.of_forall fun k => by
    rw [← T.adjoint_inner_right]
    exact (abs_real_inner_le_norm (u k) (T.adjoint z)).trans
      (mul_le_mul_of_nonneg_right (hu k) (norm_nonneg _))
end HitAndRun.Analysis
