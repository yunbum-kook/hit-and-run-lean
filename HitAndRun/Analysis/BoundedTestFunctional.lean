module
public import HitAndRun.Analysis.BoundedPreimageLimit

/-! Riesz representation for a genuinely bounded functional on a space of tests.
The test carrier need not be normed, and no injectivity of its coefficient map
is assumed: the bound itself proves consistency on its kernel. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Analysis
variable {V X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [AddCommGroup X] [Module ℝ X]

theorem exists_riesz_of_test_bound (A : X →ₗ[ℝ] V) (g : X →ₗ[ℝ] ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hb : ∀ z, |g z| ≤ R * ‖A z‖) :
    ∃ v : V, (∀ z, inner ℝ v (A z) = g z) ∧ ‖v‖ ≤ R := by
  let f := A.rangeRestrict
  have hk : LinearMap.ker f ≤ LinearMap.ker g := by
    intro z hz
    have hz' : A z = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hz)
    have h := hb z
    rw [hz', norm_zero, mul_zero] at h
    exact LinearMap.mem_ker.mpr (abs_nonpos_iff.mp h)
  let l := f.liftOfSurjective A.surjective_rangeRestrict ⟨g, hk⟩
  have hl (z : X) : l (f z) = g z := LinearMap.equivOfSurjective_apply _ _
  have hn (w : LinearMap.range A) : ‖l w‖ ≤ R * ‖w‖ := by
    obtain ⟨z, rfl⟩ := A.surjective_rangeRestrict w
    rw [hl]
    exact hb z
  let L := l.mkContinuous R hn
  obtain ⟨F, hF, hFn⟩ := exists_extension_norm_eq (LinearMap.range A) L
  let v := (InnerProductSpace.toDual ℝ V).symm F
  refine ⟨v, ?_, ?_⟩
  · intro z
    calc
      inner ℝ v (A z) = F (A z) := InnerProductSpace.toDual_symm_apply
      _ = L (f z) := hF (f z)
      _ = g z := hl z
  · calc
      ‖v‖ = ‖F‖ := (InnerProductSpace.toDual ℝ V).symm.norm_map F
      _ = ‖L‖ := hFn
      _ ≤ R := l.mkContinuous_norm_le hR hn
end HitAndRun.Analysis
