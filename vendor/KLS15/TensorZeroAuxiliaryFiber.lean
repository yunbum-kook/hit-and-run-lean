module
public import TensorMaximalHodgeCoercivity

@[expose] public section

/- KLS15 pinned compatibility: file-local cosmetic diagnostics only.
   See COSMETIC-LINTER-POLICY.json; kernel and other warning checks remain enabled. -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false


/-! The auxiliary-rank-zero endpoint has no one-form projection defect:
the actual fully symmetric one-form fiber is the whole vector space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {φ : Space n → ℝ}

lemma tensorOneFormSymmetricFiber_zero :
    tensorOneFormSymmetricFiber n 0 = ⊤ := by
  apply top_unique
  intro w _
  rw [mem_tensorOneFormSymmetricFiber_iff]
  intro a b hp
  have he : a.2 = b.2 := by simpa using hp
  have hi : a.1 = b.1 := Subsingleton.elim _ _
  exact congrArg w (Prod.ext hi he)

@[simp] theorem tensorOneFormProjection_zero :
    tensorOneFormProjection n 0 = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro w
  exact Submodule.starProjection_eq_self_iff.mpr (by rw [tensorOneFormSymmetricFiber_zero]; trivial)

@[simp] theorem tensorTwoFormWeightedAdjoint_zero_projection
    (f : TensorTwoFormIndex n 0 → Space n → ℝ) (x : Space n) :
    tensorOneFormProjection n 0 (tensorTwoFormWeightedAdjoint φ f x) =
      tensorTwoFormWeightedAdjoint φ f x := by
  rw [tensorOneFormProjection_zero, ContinuousLinearMap.id_apply]

lemma tensorTwoFormCompatible_zero_iff (f : TensorTwoFormIndex n 0 → ℝ) :
    TensorTwoFormCompatible f ↔ ∀ I i j, f (I, i, j) = -f (I, j, i) := by
  constructor
  · exact fun h => h.2.1
  · intro hs
    refine ⟨?_, hs, ?_⟩
    · intro I J _ i j
      exact congrArg (fun K => f (K, i, j)) (Subsingleton.elim I J)
    · intro I i j k
      simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul]

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorOneFormProjection_zero
#print axioms KLS.DeterministicBridgeIntegration.tensorTwoFormCompatible_zero_iff
