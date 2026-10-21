module
public import HitAndRun.Sobolev.UniformSource
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Topology.MetricSpace.HausdorffDistance
@[expose] public section

/-! Literal least constants for the source Poincare inequalities on actual H1 graphs.
The order-theoretic lemmas below assert attainment only when an admissible
constant exists and the energy is finite. They prove no analytic Poincare inequality. -/
namespace HitAndRun.Sobolev
open MeasureTheory ProbabilityTheory EllipticPdes EllipticPdes.H1Graph Set
open scoped ENNReal NNReal
noncomputable section
namespace BoundedOpenDomain
variable {n : ℕ} [NeZero n]

abbrev H1 (K : BoundedOpenDomain n) := W12 K.ambient K.carrier

def boundaryDistance (K : BoundedOpenDomain n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Metric.infDist x (frontier K.carrier)

def varianceEnergy (K : BoundedOpenDomain n) (u : K.H1) : ℝ≥0∞ :=
  evariance (fnL (u : H1Graph K.ambient K.carrier)) (K.ambient.restrict K.carrier)

def gradientEnergy (K : BoundedOpenDomain n) (u : K.H1) : ℝ≥0∞ :=
  ENNReal.ofReal (‖gradL (u : H1Graph K.ambient K.carrier)‖ ^ 2)

def weightedGradientEnergy (K : BoundedOpenDomain n) (u : K.H1) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (K.boundaryDistance x ^ 2) *
    ‖gradL (u : H1Graph K.ambient K.carrier) x‖ₑ ^ 2 ∂K.ambient.restrict K.carrier

/-- The exact source PI property, not an assumed analytic theorem. -/
def IsPoincareConstant (K : BoundedOpenDomain n) (C : ℝ≥0∞) : Prop :=
  ∀ u : K.H1, K.varianceEnergy u ≤ C * K.gradientEnergy u

/-- The exact source IPI property with actual distance-to-frontier weight. -/
def IsImprovedPoincareConstant (K : BoundedOpenDomain n) (C : ℝ≥0∞) : Prop :=
  ∀ u : K.H1, K.varianceEnergy u ≤ C * K.weightedGradientEnergy u

def poincareConstant (K : BoundedOpenDomain n) : ℝ≥0∞ :=
  sInf {C | K.IsPoincareConstant C}

def improvedPoincareConstant (K : BoundedOpenDomain n) : ℝ≥0∞ :=
  sInf {C | K.IsImprovedPoincareConstant C}

/-- The variance is taken against the source uniform probability measure. -/
theorem varianceEnergy_eq_uniform (K : BoundedOpenDomain n) (u : K.H1) :
    K.varianceEnergy u =
      evariance (fnL (u : H1Graph K.ambient K.carrier)) (uniformMeasure K.carrier) := by
  exact congrArg (evariance (fnL (u : H1Graph K.ambient K.carrier))) K.measure_eq_uniform

/-- The norm-based ordinary energy is exactly the source integral. -/
theorem gradientEnergy_eq_lintegral (K : BoundedOpenDomain n) (u : K.H1) :
    K.gradientEnergy u =
      ∫⁻ x, ‖gradL (u : H1Graph K.ambient K.carrier) x‖ₑ ^ 2
        ∂K.ambient.restrict K.carrier := by
  rw [gradientEnergy, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, Lp.enorm_def]
  simpa using eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    (Lp.aestronglyMeasurable (gradL (u : H1Graph K.ambient K.carrier)))

/-- The actual H1 variance is finite. -/
theorem varianceEnergy_ne_top (K : BoundedOpenDomain n) (u : K.H1) :
    K.varianceEnergy u ≠ ⊤ :=
  evariance_ne_top (Lp.memLp _)

/-- The ordinary weak-gradient energy is finite by its L2 construction. -/
theorem gradientEnergy_ne_top (K : BoundedOpenDomain n) (u : K.H1) :
    K.gradientEnergy u ≠ ⊤ := ENNReal.ofReal_ne_top

/-- Boundedness of the domain bounds the actual distance weight. -/
theorem boundaryDistance_bounded (K : BoundedOpenDomain n) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ K.carrier, K.boundaryDistance x ≤ R := by
  obtain ⟨R, hR, hxR⟩ := K.isBounded.exists_pos_norm_le
  refine ⟨Metric.infDist 0 (frontier K.carrier) + R,
    add_nonneg Metric.infDist_nonneg hR.le, ?_⟩
  intro x hx
  exact (Metric.infDist_le_infDist_add_dist (y := 0)).trans
    (add_le_add le_rfl (by simpa using hxR x hx))

/-- The actual distance-weighted weak-gradient energy is finite on a bounded domain. -/
theorem weightedGradientEnergy_ne_top (K : BoundedOpenDomain n) (u : K.H1) :
    K.weightedGradientEnergy u ≠ ⊤ := by
  obtain ⟨R, hR, hbound⟩ := K.boundaryDistance_bounded
  let g := gradL (u : H1Graph K.ambient K.carrier)
  have hg : (∫⁻ x, ‖g x‖ₑ ^ (2 : ℕ) ∂K.ambient.restrict K.carrier) < ⊤ := by
    rw [← K.gradientEnergy_eq_lintegral u]
    exact lt_top_iff_ne_top.mpr (K.gradientEnergy_ne_top u)
  apply ne_top_of_le_ne_top (b := ENNReal.ofReal (R ^ 2) *
    ∫⁻ x, ‖g x‖ₑ ^ (2 : ℕ) ∂K.ambient.restrict K.carrier)
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.ne
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem K.isOpen.measurableSet] with x hx
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ Metric.infDist_nonneg (hbound x hx) 2)) _

/-- Infima preserve these inequalities for finite energies and a nonempty feasible set.
The nonemptiness requirement matters: infinity times zero is zero in ENNReal. -/
theorem energy_bound_sInf {ι : Type*} (V E : ι → ℝ≥0∞)
    (hE : ∀ u, E u ≠ ⊤)
    (h : ∃ C : ℝ≥0∞, ∀ u, V u ≤ C * E u) :
    ∀ u, V u ≤ sInf {C : ℝ≥0∞ | ∀ v, V v ≤ C * E v} * E u := by
  let S : Set ℝ≥0∞ := {C | ∀ v, V v ≤ C * E v}
  haveI : Nonempty S := ⟨⟨h.choose, h.choose_spec⟩⟩
  intro u
  change V u ≤ sInf S * E u
  rw [sInf_eq_iInf', ENNReal.iInf_mul (by simp [hE u])]
  exact le_iInf fun C => C.property u

/-- The least PI constant is admissible whenever any PI constant is admissible. -/
theorem poincareConstant_admissible (K : BoundedOpenDomain n)
    (h : ∃ C, K.IsPoincareConstant C) : K.IsPoincareConstant K.poincareConstant :=
  energy_bound_sInf K.varianceEnergy K.gradientEnergy K.gradientEnergy_ne_top h

theorem IsPoincareConstant.mono (K : BoundedOpenDomain n) {C D : ℝ≥0∞}
    (h : K.IsPoincareConstant C) (hCD : C ≤ D) : K.IsPoincareConstant D := by
  intro u
  exact (h u).trans (mul_le_mul_left hCD _)

theorem IsImprovedPoincareConstant.mono (K : BoundedOpenDomain n) {C D : ℝ≥0∞}
    (h : K.IsImprovedPoincareConstant C) (hCD : C ≤ D) :
    K.IsImprovedPoincareConstant D := by
  intro u
  exact (h u).trans (mul_le_mul_left hCD _)

/-- Every admissible PI constant bounds the least one. -/
theorem poincareConstant_le (K : BoundedOpenDomain n) {C : ℝ≥0∞}
    (h : K.IsPoincareConstant C) : K.poincareConstant ≤ C := sInf_le h

/-- Every admissible IPI constant bounds the least one. -/
theorem improvedPoincareConstant_le (K : BoundedOpenDomain n) {C : ℝ≥0∞}
    (h : K.IsImprovedPoincareConstant C) : K.improvedPoincareConstant ≤ C := sInf_le h

/-- Finite optimal PI constant ensures a nonempty feasible set and hence attainment. -/
theorem poincareConstant_admissible_of_lt_top (K : BoundedOpenDomain n)
    (h : K.poincareConstant < ⊤) : K.IsPoincareConstant K.poincareConstant := by
  apply K.poincareConstant_admissible
  by_contra hn
  have hempty : {C | K.IsPoincareConstant C} = ∅ := by
    ext C
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact fun hc => hn ⟨C, hc⟩
  simp [poincareConstant, hempty] at h

/-- IPI attainment from actual finite weighted energies and a nonempty feasible set. -/
theorem improvedPoincareConstant_admissible_of_finite_energy (K : BoundedOpenDomain n)
    (hE : ∀ u : K.H1, K.weightedGradientEnergy u ≠ ⊤)
    (h : ∃ C, K.IsImprovedPoincareConstant C) :
    K.IsImprovedPoincareConstant K.improvedPoincareConstant :=
  energy_bound_sInf K.varianceEnergy K.weightedGradientEnergy hE h

/-- The least IPI constant is admissible whenever any IPI constant is admissible. -/
theorem improvedPoincareConstant_admissible (K : BoundedOpenDomain n)
    (h : ∃ C, K.IsImprovedPoincareConstant C) :
    K.IsImprovedPoincareConstant K.improvedPoincareConstant :=
  K.improvedPoincareConstant_admissible_of_finite_energy K.weightedGradientEnergy_ne_top h

/-- Finite optimal IPI constant ensures attainment, without proving it is finite. -/
theorem improvedPoincareConstant_admissible_of_lt_top (K : BoundedOpenDomain n)
    (h : K.improvedPoincareConstant < ⊤) :
    K.IsImprovedPoincareConstant K.improvedPoincareConstant := by
  apply K.improvedPoincareConstant_admissible
  by_contra hn
  have hempty : {C | K.IsImprovedPoincareConstant C} = ∅ := by
    ext C
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact fun hc => hn ⟨C, hc⟩
  simp [improvedPoincareConstant, hempty] at h

end BoundedOpenDomain
end
end HitAndRun.Sobolev
