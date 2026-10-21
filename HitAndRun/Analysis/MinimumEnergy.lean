module
public import HitAndRun.Analysis.MinimumNormPreimage
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.ENNReal.Inv
@[expose] public section

/-! Extended-valued fiber energy: empty fibers have energy infinity. -/
namespace HitAndRun.Analysis
open scoped ENNReal
variable {V Q : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup Q] [NormedSpace ℝ Q]

noncomputable def minimumEnergy (D : V →L[ℝ] Q) (f : Q) : ℝ≥0∞ :=
  ⨅ v : {v : V // D v = f}, ENNReal.ofReal (‖(v : V)‖ ^ 2)

/-- A finite extended infimum cannot conceal an empty fiber. -/
theorem minimumEnergy_lt_top_iff (D : V →L[ℝ] Q) (f : Q) :
    minimumEnergy D f < ⊤ ↔ ∃ v : V, D v = f := by
  classical
  constructor
  · intro h
    by_contra he
    have : IsEmpty {v : V // D v = f} := ⟨fun v => he ⟨v.val, v.property⟩⟩
    simp [minimumEnergy] at h
  · rintro ⟨v, hv⟩
    exact lt_of_le_of_lt (iInf_le _ (⟨v, hv⟩ : {v : V // D v = f}))
      ENNReal.ofReal_lt_top

/-- The extended energy is attained whenever finite. -/
theorem minimumEnergy_attained (D : V →L[ℝ] Q) (f : Q)
    (hf : minimumEnergy D f < ⊤) :
    ∃ v : V, D v = f ∧ minimumEnergy D f = ENNReal.ofReal (‖v‖ ^ 2) := by
  obtain ⟨v, hv, hmin⟩ := exists_minimum_energy_preimage D f
    ((minimumEnergy_lt_top_iff D f).mp hf)
  refine ⟨v, hv, le_antisymm (iInf_le _ (⟨v, hv⟩ : {v : V // D v = f})) ?_⟩
  apply le_iInf
  intro w
  exact ENNReal.ofReal_le_ofReal (hmin w.val w.property)

/-- The energy/norm-squared supremum excludes zero targets, exactly as in the paper. -/
noncomputable def rightInverseEnergyConstant (D : V →L[ℝ] Q) : ℝ≥0∞ :=
  ⨆ f : {f : Q // f ≠ 0}, minimumEnergy D f / ENNReal.ofReal (‖(f : Q)‖ ^ 2)

/-- Finiteness of the normalized supremum forces every fiber to be nonempty. -/
theorem surjective_of_energyConstant_lt_top (D : V →L[ℝ] Q)
    (h : rightInverseEnergyConstant D < ⊤) : Function.Surjective D := by
  intro f
  by_cases hf : f = 0
  · exact ⟨0, by simp [hf]⟩
  apply (minimumEnergy_lt_top_iff D f).mp
  have hb : minimumEnergy D f / ENNReal.ofReal (‖f‖ ^ 2) < ⊤ :=
    lt_of_le_of_lt (le_iSup (fun g : {g : Q // g ≠ 0} => minimumEnergy D g.val / ENNReal.ofReal (‖g.val‖ ^ 2)) (⟨f, hf⟩ : {f : Q // f ≠ 0})) h
  by_contra he
  have ht : minimumEnergy D f = ⊤ := top_le_iff.mp (not_lt.mp he)
  have hd : minimumEnergy D f / ENNReal.ofReal (‖f‖ ^ 2) = ⊤ :=
    ENNReal.div_eq_top.mpr (Or.inr ⟨ht, ENNReal.ofReal_ne_top⟩)
  exact (ne_of_lt hb) hd
/-- A finite real bound on the normalized constant gives attained witnesses,
with that very constant rather than an arbitrary larger approximation. -/
theorem right_inverse_bound_of_energyConstant_le (D : V →L[ℝ] Q) {C : ℝ}
    (hC : 0 ≤ C) (h : rightInverseEnergyConstant D ≤ ENNReal.ofReal C) :
    ∀ f : Q, ∃ v : V, D v = f ∧ ‖v‖ ^ 2 ≤ C * ‖f‖ ^ 2 := by
  intro f
  by_cases hf : f = 0
  · exact ⟨0, by simp [hf], by simp [hf]⟩
  have hfin : rightInverseEnergyConstant D < ⊤ :=
    lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have he := (minimumEnergy_lt_top_iff D f).mpr
    (surjective_of_energyConstant_lt_top D hfin f)
  obtain ⟨v, hv, hval⟩ := minimumEnergy_attained D f he
  refine ⟨v, hv, ?_⟩
  have hn : ENNReal.ofReal (‖f‖ ^ 2) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hf)))
  have hb : minimumEnergy D f / ENNReal.ofReal (‖f‖ ^ 2) ≤ ENNReal.ofReal C :=
    (le_iSup (fun g : {g : Q // g ≠ 0} => minimumEnergy D g.val / ENNReal.ofReal (‖g.val‖ ^ 2)) (⟨f, hf⟩ : {f : Q // f ≠ 0})).trans h
  have hh := (ENNReal.div_le_iff hn ENNReal.ofReal_ne_top).mp hb
  rw [hval, ← ENNReal.ofReal_mul hC] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (sq_nonneg _))).mp hh

/-- Conversely, actual witnesses bound the normalized extended supremum. -/
theorem energyConstant_le_of_right_inverse_bound (D : V →L[ℝ] Q) {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ f : Q, ∃ v : V, D v = f ∧ ‖v‖ ^ 2 ≤ C * ‖f‖ ^ 2) :
    rightInverseEnergyConstant D ≤ ENNReal.ofReal C := by
  apply iSup_le
  intro f
  obtain ⟨v, hv, hb⟩ := h f.val
  have hn : ENNReal.ofReal (‖f.val‖ ^ 2) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr f.property)))
  apply (ENNReal.div_le_iff hn ENNReal.ofReal_ne_top).mpr
  calc
    minimumEnergy D f.val ≤ ENNReal.ofReal (‖v‖ ^ 2) :=
      iInf_le _ (⟨v, hv⟩ : {v : V // D v = f.val})
    _ ≤ ENNReal.ofReal (C * ‖f.val‖ ^ 2) := ENNReal.ofReal_le_ofReal hb
    _ = _ := ENNReal.ofReal_mul hC

/-- Exact extended-infimum/supremum and witness equivalence. -/
theorem energyConstant_le_iff_right_inverse_bound (D : V →L[ℝ] Q) {C : ℝ}
    (hC : 0 ≤ C) :
    rightInverseEnergyConstant D ≤ ENNReal.ofReal C ↔
      (∀ f : Q, ∃ v : V, D v = f ∧ ‖v‖ ^ 2 ≤ C * ‖f‖ ^ 2) :=
  ⟨right_inverse_bound_of_energyConstant_le D hC,
    energyConstant_le_of_right_inverse_bound D hC⟩

/-- At finite optimal constant, the original constant itself is attained
pointwise; there is no epsilon loss. -/
theorem right_inverse_bound_at_energyConstant (D : V →L[ℝ] Q)
    (h : rightInverseEnergyConstant D < ⊤) :
    ∀ f : Q, ∃ v : V, D v = f ∧
      ‖v‖ ^ 2 ≤ (rightInverseEnergyConstant D).toReal * ‖f‖ ^ 2 := by
  apply right_inverse_bound_of_energyConstant_le D ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_toReal (ne_of_lt h)]

end HitAndRun.Analysis
