module
public import HitAndRun.Sobolev.UniformSource
public import HitAndRun.Sobolev.CurlEnergy
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
@[expose] public section

/-! Literal Rayleigh infimum on the actual centered L2 carrier.
Nonemptiness is proved from a nonzero genuine Sobolev gradient, not assumed. -/
namespace HitAndRun.Markov
open MeasureTheory HitAndRun.Sobolev
open scoped BigOperators RealInnerProductSpace
variable {n : ℕ} [NeZero n]

/-- An actual bounded nonempty open body has nontrivial centered L2. -/
theorem target_nontrivial (K : BoundedOpenDomain n) : Nontrivial K.Target := by
  letI := gradientSpace_nontrivial (μ := K.ambient) K.isOpen K.nonempty K.isBounded
  obtain ⟨w, hw⟩ := exists_ne (0 : gradientSpace K.ambient K.carrier)
  let d (i : Fin n) : Lp ℝ 2 (K.ambient.restrict K.carrier) :=
    (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).compLpL 2
      (K.ambient.restrict K.carrier) (w : Lp (EuclideanSpace ℝ (Fin n)) 2
        (K.ambient.restrict K.carrier))
  have hex : ∃ i, d i ≠ 0 := by
    by_contra h
    push_neg at h
    have he := lp_coordinate_energy (w : Lp (EuclideanSpace ℝ (Fin n)) 2
      (K.ambient.restrict K.carrier))
    change (∑ i, ‖d i‖ ^ 2) = _ at he
    simp only [h, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] at he
    have hz : (w : Lp (EuclideanSpace ℝ (Fin n)) 2 (K.ambient.restrict K.carrier)) = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp he.symm)
    exact hw (Subtype.ext hz)
  obtain ⟨i, hi⟩ := hex
  let f : K.Target := ⟨d i, gradient_partial_mean_zero w
    (EuclideanSpace.basisFun (Fin n) ℝ i)⟩
  exact ⟨⟨f, 0, fun h => hi (congrArg Subtype.val h)⟩⟩

noncomputable def rayleighValues (K : BoundedOpenDomain n)
    (P : Lp ℝ 2 (K.ambient.restrict K.carrier) → Lp ℝ 2 (K.ambient.restrict K.carrier)) : Set ℝ :=
  {r | ∃ f : K.Target, f ≠ 0 ∧ r =
    inner ℝ (f : Lp ℝ 2 (K.ambient.restrict K.carrier))
      ((f : Lp ℝ 2 (K.ambient.restrict K.carrier)) - P f) / ‖f‖ ^ 2}

/-- Exactly the manuscript's infimum over nonzero centered L2 functions. -/
noncomputable def spectralGap (K : BoundedOpenDomain n)
    (P : Lp ℝ 2 (K.ambient.restrict K.carrier) → Lp ℝ 2 (K.ambient.restrict K.carrier)) : ℝ :=
  sInf (rayleighValues K P)

theorem rayleighValues_nonempty (K : BoundedOpenDomain n)
    (P : Lp ℝ 2 (K.ambient.restrict K.carrier) → Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    (rayleighValues K P).Nonempty := by
  letI := target_nontrivial K
  obtain ⟨f, hf⟩ := exists_ne (0 : K.Target)
  exact ⟨_, f, hf, rfl⟩

/-- Lower boundedness is explicit, so the real infimum is not used outside
its conditionally-complete-lattice domain. -/
theorem rayleighValues_bddBelow (K : BoundedOpenDomain n)
    (P : Lp ℝ 2 (K.ambient.restrict K.carrier) → Lp ℝ 2 (K.ambient.restrict K.carrier))
    (c : ℝ) (h : ∀ f : K.Target, f ≠ 0 → c ≤
      inner ℝ (f : Lp ℝ 2 (K.ambient.restrict K.carrier))
        ((f : Lp ℝ 2 (K.ambient.restrict K.carrier)) - P f) / ‖f‖ ^ 2) :
    BddBelow (rayleighValues K P) := by
  refine ⟨c, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  exact h f hf

/-- A true pointwise Rayleigh lower bound controls the literal nonempty infimum. -/
theorem le_spectralGap (K : BoundedOpenDomain n)
    (P : Lp ℝ 2 (K.ambient.restrict K.carrier) → Lp ℝ 2 (K.ambient.restrict K.carrier))
    (c : ℝ) (h : ∀ f : K.Target, f ≠ 0 → c ≤
      inner ℝ (f : Lp ℝ 2 (K.ambient.restrict K.carrier))
        ((f : Lp ℝ 2 (K.ambient.restrict K.carrier)) - P f) / ‖f‖ ^ 2) :
    c ≤ spectralGap K P := by
  apply le_csInf (rayleighValues_nonempty K P)
  rintro r ⟨f, hf, rfl⟩
  exact h f hf

end HitAndRun.Markov
