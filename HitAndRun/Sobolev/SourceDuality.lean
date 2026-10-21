module
public import HitAndRun.Sobolev.ZeroMean
public import HitAndRun.Analysis.Duality
public import HitAndRun.Analysis.MinimumEnergy
@[expose] public section

/-! Concrete Sobolev instances of the source's Hilbert duality and energy constant.
The measure is an arbitrary additive Haar measure, restricted to a bounded domain.
Uniform probability normalization and source correspondence are recorded separately. -/
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Analysis
open scoped ENNReal BigOperators InnerProduct
variable {n : ℕ} [NeZero n]
variable {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure] {Ω : Set (EuclideanSpace ℝ (Fin n))}
  [IsFiniteMeasure (μ.restrict Ω)]

/-- The actual Babuška–Aziz extended constant of zero-trace weak divergence. -/
def babuskaAzizConstant : ℝ≥0∞ :=
  rightInverseEnergyConstant (centeredDivergence (μ := μ) (Ω := Ω))

/-- Move a fixed nonzero target denominator through the fiber infimum.
This remains valid for an empty fiber, whose infimum is infinity. -/
theorem babuskaAzizConstant_eq_source :
    babuskaAzizConstant (μ := μ) (Ω := Ω) =
      ⨆ f : {f : centeredL2 (μ := μ) (Ω := Ω) // f ≠ 0},
        ⨅ u : {u : VectorField μ Ω // centeredDivergence u = f.val},
          ENNReal.ofReal (‖u.val‖ ^ 2) / ENNReal.ofReal (‖f.val‖ ^ 2) := by
  unfold babuskaAzizConstant rightInverseEnergyConstant
  congr 1
  funext f
  exact ENNReal.iInf_div_of_ne
    (ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr f.property))))
    ENNReal.ofReal_ne_top

/-- Vector-field Hilbert norm is exactly the sum of actual weak gradient energies. -/
theorem vectorField_norm_sq (u : VectorField μ Ω) :
    ‖u‖ ^ 2 = ∑ i : Fin n, ‖((u i : gradientSpace μ Ω) : Lp (EuclideanSpace ℝ (Fin n)) 2 (μ.restrict Ω))‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ u

/-- The exact norm bridge for the underlying H01 vector-field graphs. -/
theorem vectorField_graph_energy (hb : Bornology.IsBounded Ω)
    (u : Fin n → H01 μ Ω) :
    ‖WithLp.toLp 2 (fun i => gradientEquiv (μ := μ) hb (u i))‖ ^ 2 =
      ∑ i : Fin n, ‖gradL (u i : H1Graph μ Ω)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

instance centeredL2_complete : CompleteSpace (centeredL2 (μ := μ) (Ω := Ω)) :=
  (meanCLM μ Ω).isClosed_ker.isComplete.completeSpace_coe

/-- Actual zero-trace divergence attains the finite optimal constant, without epsilon loss. -/
theorem divergence_solver_at_babuskaAziz (hb : Bornology.IsBounded Ω)
    (h : babuskaAzizConstant (μ := μ) (Ω := Ω) < ⊤) :
    ∀ f : centeredL2 (μ := μ) (Ω := Ω), ∃ u : VectorField μ Ω,
      centeredDivergence u = f ∧
      ‖u‖ ^ 2 ≤ (babuskaAzizConstant (μ := μ) (Ω := Ω)).toReal * ‖f‖ ^ 2 :=
  by
    letI := gradientSpace_complete (μ := μ) hb
    exact right_inverse_bound_at_energyConstant centeredDivergence h

/-- Riesz representation for the genuine centered weak divergence. -/
theorem existsUnique_divergence_riesz (hb : Bornology.IsBounded Ω) (f : centeredL2 (μ := μ) (Ω := Ω)) :
    ∃! u : VectorField μ Ω, ∀ v : VectorField μ Ω,
      inner ℝ f (centeredDivergence v) = inner ℝ u v :=
  by
    letI := gradientSpace_complete (μ := μ) hb
    exact existsUnique_riesz_field centeredDivergence f

/-- Exact squared-C duality for the genuine weak divergence. -/
theorem divergence_duality [CompleteSpace (gradientSpace μ Ω)] {C : ℝ} (hC : 0 < C) :
    (∀ f : centeredL2 (μ := μ) (Ω := Ω), ∃ u : VectorField μ Ω,
      centeredDivergence u = f ∧ ‖u‖ ^ 2 ≤ C * ‖f‖ ^ 2) ↔
    (∀ f : centeredL2 (μ := μ) (Ω := Ω),
      ‖f‖ ^ 2 ≤ C * ‖ContinuousLinearMap.adjoint centeredDivergence f‖ ^ 2) :=
  right_inverse_bound_iff_adjoint_lower_bound centeredDivergence hC

/-- Source signed nonzero-vector supremum form, when the test carrier is nontrivial. -/
theorem divergence_duality_sup (hb : Bornology.IsBounded Ω) [Nontrivial (VectorField μ Ω)] {C : ℝ} (hC : 0 < C) :
    (∀ f : centeredL2 (μ := μ) (Ω := Ω), ∃ u : VectorField μ Ω,
      centeredDivergence u = f ∧ ‖u‖ ^ 2 ≤ C * ‖f‖ ^ 2) ↔
    (∀ f : centeredL2 (μ := μ) (Ω := Ω), ‖f‖ ^ 2 ≤
      C * (sSup (divergenceDualQuotients centeredDivergence f)) ^ 2) :=
  by
    letI := gradientSpace_complete (μ := μ) hb
    exact right_inverse_bound_iff_dual_sup centeredDivergence hC
/-- Exact Riesz norm as the signed source supremum for actual weak divergence. -/
theorem divergence_riesz_norm [CompleteSpace (gradientSpace μ Ω)] [Nontrivial (VectorField μ Ω)]
    (f : centeredL2 (μ := μ) (Ω := Ω)) :
    ‖ContinuousLinearMap.adjoint centeredDivergence f‖ =
      sSup (divergenceDualQuotients centeredDivergence f) :=
  adjoint_norm_eq_sSup centeredDivergence f
end HitAndRun.Sobolev
