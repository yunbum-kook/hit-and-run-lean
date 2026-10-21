import HitAndRun.Analysis.AdjointRiesz
import HitAndRun.Analysis.MinimumNormPreimage

open HitAndRun.Analysis

variable {V Q : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]

example (D : V →L[ℝ] Q) (f : Q) :
    ∃! u : V, ∀ v : V, inner ℝ f (D v) = inner ℝ u v :=
  existsUnique_riesz_field D f

example [Nontrivial V] (D : V →L[ℝ] Q) (f : Q) :
    ‖D.adjoint f‖ = sSup {r : ℝ | ∃ v : V, v ≠ 0 ∧ r = inner ℝ f (D v) / ‖v‖} :=
  adjoint_norm_eq_sSup D f

example (D : V →L[ℝ] Q) (f : Q) (hf : ∃ v : V, D v = f) :
    ∃ u : V, D u = f ∧ ∀ v : V, D v = f → ‖u‖ ≤ ‖v‖ :=
  exists_minimum_norm_preimage D f hf

example (D : V →L[ℝ] Q) (f : Q) (hf : ∃ v : V, D v = f) :
    ∃ u : V, D u = f ∧ ∀ v : V, D v = f → ‖u‖ ^ 2 ≤ ‖v‖ ^ 2 :=
  exists_minimum_energy_preimage D f hf

#print axioms HitAndRun.Analysis.existsUnique_riesz_field
#print axioms HitAndRun.Analysis.adjoint_norm_isLUB
#print axioms HitAndRun.Analysis.adjoint_norm_eq_sSup
#print axioms HitAndRun.Analysis.exists_minimum_norm_preimage
#print axioms HitAndRun.Analysis.exists_minimum_energy_preimage
