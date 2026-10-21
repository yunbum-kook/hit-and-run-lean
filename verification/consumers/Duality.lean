import HitAndRun.Analysis.Duality
import HitAndRun.Analysis.MinimumEnergy
open HitAndRun.Analysis
variable {V Q : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
example (D : V →L[ℝ] Q) {C : ℝ} (hC : 0 < C) :
    (∀ f : Q, ∃ v : V, D v = f ∧ ‖v‖ ^ 2 ≤ C * ‖f‖ ^ 2) ↔
      (∀ f : Q, ‖f‖ ^ 2 ≤ C * ‖D.adjoint f‖ ^ 2) :=
  right_inverse_bound_iff_adjoint_lower_bound D hC
example [Nontrivial V] (D : V →L[ℝ] Q) {C : ℝ} (hC : 0 < C) :
    (∀ f : Q, ∃ v : V, D v = f ∧ ‖v‖ ^ 2 ≤ C * ‖f‖ ^ 2) ↔
      (∀ f : Q, ‖f‖ ^ 2 ≤ C * (sSup (divergenceDualQuotients D f)) ^ 2) :=
  right_inverse_bound_iff_dual_sup D hC
example (D : V →L[ℝ] Q) (f : Q) :
    minimumEnergy D f < ⊤ ↔ ∃ v : V, D v = f := minimumEnergy_lt_top_iff D f
example (D : V →L[ℝ] Q) {C : ℝ} (hC : 0 ≤ C) :
    rightInverseEnergyConstant D ≤ ENNReal.ofReal C ↔
      (∀ f : Q, ∃ v : V, D v = f ∧ ‖v‖ ^ 2 ≤ C * ‖f‖ ^ 2) :=
  energyConstant_le_iff_right_inverse_bound D hC
example (D : V →L[ℝ] Q) (h : rightInverseEnergyConstant D < ⊤) :
    ∀ f : Q, ∃ v : V, D v = f ∧
      ‖v‖ ^ 2 ≤ (rightInverseEnergyConstant D).toReal * ‖f‖ ^ 2 :=
  right_inverse_bound_at_energyConstant D h
#print axioms adjoint_lower_bound_of_right_inverse_bound
#print axioms right_inverse_bound_of_adjoint_lower_bound
#print axioms right_inverse_bound_iff_adjoint_lower_bound
#print axioms right_inverse_bound_iff_dual_sup
#print axioms minimumEnergy_lt_top_iff
#print axioms minimumEnergy_attained
#print axioms surjective_of_energyConstant_lt_top
#print axioms right_inverse_bound_of_energyConstant_le
#print axioms energyConstant_le_of_right_inverse_bound
#print axioms energyConstant_le_iff_right_inverse_bound
#print axioms right_inverse_bound_at_energyConstant
