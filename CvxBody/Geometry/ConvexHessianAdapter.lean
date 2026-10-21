module
public import CvxBody.External.TauCeti.Analysis.Convex.Alexandrov
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

@[expose] public section


/-!
# Alexandrov's theorem for a finite convex function: adapter

`TauCeti.Analysis.Convex.Alexandrov` is stated for convex `f : E → EReal` with real representative
`x ↦ (f x).toReal`.  For a finite convex function `G : E → ℝ` (`ConvexOn ℝ univ G`) this file proves,
by applying it to `f = (↑G : E → EReal)`:

* `convex_epigraph_coe`: the extended-valued epigraph hypothesis of the port holds;
* `ConvexOn.ae_exists_isPositive_hasFDerivWithinAt_gradient`: for Haar-a.e. `x` there is a positive
  operator `A` such that `G` has the second-order expansion with Hessian `A` at `x`, and for every set
  `t` on which `G` is differentiable, `gradient G` has derivative `A` within `t` at `x`;
* `ConvexOn.exists_measurable_hessian`: the same with `A = Hs x` for a *measurable* function
  `Hs : E → (E →L[ℝ] E)` (built from symmetric second differences of `G`, a limsup of continuous
  functions), which equals the Alexandrov Hessian almost everywhere.
-/

namespace CvxBody.Geometry

open Filter Set Metric Asymptotics MeasureTheory MeasureTheory.Measure
open scoped Topology InnerProductSpace

theorem convex_epigraph_coe {E : Type*} [AddCommGroup E] [Module ℝ E] {G : E → ℝ}
    (hG : ConvexOn ℝ univ G) :
    Convex ℝ {p : E × ℝ | ((G p.1 : ℝ) : EReal) ≤ p.2} := by
  have : {p : E × ℝ | ((G p.1 : ℝ) : EReal) ≤ p.2} = {p : E × ℝ | p.1 ∈ univ ∧ G p.1 ≤ p.2} := by
    ext p; simp [EReal.coe_le_coe_iff]
  rw [this]; exact hG.convex_epigraph

section SecondDifference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Symmetric second difference quotient `k² (G (x + v/k) + G (x - v/k) - 2 G x)`. -/
noncomputable def secondDiff (G : E → ℝ) (k : ℕ) (v x : E) : ℝ :=
  (k : ℝ) ^ 2 * (G (x + (k : ℝ)⁻¹ • v) + G (x - (k : ℝ)⁻¹ • v) - 2 * G x)

theorem tendsto_remainder_scaled {r : E → ℝ} {x : E}
    (hr : r =o[𝓝 x] (fun x' => ‖x' - x‖ ^ 2)) (v : E) :
    Tendsto (fun k : ℕ => (k : ℝ) ^ 2 * r (x + (k : ℝ)⁻¹ • v)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun k : ℕ => x + (k : ℝ)⁻¹ • v) atTop (𝓝 x) := by
    have h0 : Tendsto (fun k : ℕ => (k : ℝ)⁻¹ • v) atTop (𝓝 ((0:ℝ) • v)) :=
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).smul_const v
    simpa using (tendsto_const_nhds.add h0 : Tendsto (fun k : ℕ => x + (k : ℝ)⁻¹ • v) atTop
      (𝓝 (x + (0:ℝ) • v)))
  have h1 := hr.comp_tendsto hlim
  have h2 := (isBigO_refl (fun k : ℕ => (k : ℝ) ^ 2) atTop).mul_isLittleO h1
  have h3 : (fun k : ℕ => (k : ℝ) ^ 2 * ‖(fun k : ℕ => x + (k : ℝ)⁻¹ • v) k - x‖ ^ 2)
      =ᶠ[atTop] fun _ => ‖v‖ ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk' : (k : ℝ) ≠ 0 := by positivity
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
    field_simp
  have h4 := (h2.congr' EventuallyEq.rfl h3).trans_isBigO
    (isBigO_const_const (‖v‖ ^ 2) (one_ne_zero : (1:ℝ) ≠ 0) atTop)
  exact (isLittleO_one_iff ℝ).mp h4

end SecondDifference

section Alexandrov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsAddHaarMeasure μ]

omit [MeasurableSpace E] [BorelSpace E] [IsAddHaarMeasure μ] in
/-- At a point with a second-order expansion with Hessian `A`, the symmetric second differences
converge to `⟪A v, v⟫`. -/
theorem tendsto_secondDiff {G : E → ℝ} {x : E} {A : E →L[ℝ] E}
    (hr : (fun x' => G x' - G x - ⟪gradient G x, x' - x⟫_ℝ - ⟪A (x' - x), x' - x⟫_ℝ / 2)
        =o[𝓝 x] (fun x' => ‖x' - x‖ ^ 2)) (v : E) :
    Tendsto (fun k : ℕ => secondDiff G k v x) atTop (𝓝 ⟪A v, v⟫_ℝ) := by
  have h1 := tendsto_remainder_scaled hr v
  have h2 := tendsto_remainder_scaled hr (-v)
  have h3 := (h1.add h2).add_const ⟪A v, v⟫_ℝ
  rw [zero_add, zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk' : (k : ℝ) ≠ 0 := by positivity
  simp only [secondDiff, add_sub_cancel_left, smul_neg, inner_neg_right, map_neg, inner_neg_left,
    ← sub_eq_add_neg, map_smul, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, add_sub_cancel_left, sub_sub_cancel_left]
  field_simp
  ring

theorem _root_.ConvexOn.ae_exists_isPositive_hasFDerivWithinAt_gradient {G : E → ℝ}
    (hG : ConvexOn ℝ univ G) :
    ∀ᵐ x ∂μ, ∃ A : E →L[ℝ] E, A.IsPositive ∧
      (fun x' => G x' - G x - ⟪gradient G x, x' - x⟫_ℝ - ⟪A (x' - x), x' - x⟫_ℝ / 2)
        =o[𝓝 x] (fun x' => ‖x' - x‖ ^ 2) ∧
      ∀ t : Set E, (∀ x' ∈ t, DifferentiableAt ℝ G x') →
        HasFDerivWithinAt (gradient G) A t x := by
  set f : E → EReal := fun x => (G x : EReal) with hf
  have hfc : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2} := convex_epigraph_coe hG
  have hbot : ∀ x, f x ≠ ⊥ := fun x => EReal.coe_ne_bot _
  have hfG : (fun x' => (f x').toReal) = G := funext fun _ => EReal.toReal_coe _
  filter_upwards [TauCeti.ae_existsUnique_isPositive_forall_mem_subdifferential_norm_sub_le
    (μ := μ) hfc hbot] with x h
  obtain ⟨A, ⟨hA, hexp⟩, -⟩ := h (EReal.coe_ne_top _)
  have hne := TauCeti.eventually_nonempty_subdifferential hfc hbot
    (Filter.Eventually.of_forall fun x' => EReal.coe_ne_top _) (x := x)
  refine ⟨A, hA, ?_, fun t ht => ?_⟩
  · have := TauCeti.isLittleO_of_forall_mem_subdifferential_norm_sub_le hne hexp
    simpa [hf, hfG] using this
  · have := TauCeti.hasFDerivWithinAt_gradient_toReal_of_forall_mem_subdifferential_norm_sub_le
      (f := f) (t := t) (x := x) (A := A) (fun x' hx' => by
        exact TauCeti.gradient_toReal_mem_subdifferential hfc hbot (EReal.coe_ne_top _)
          (by rw [hfG]; exact ht x' hx')) hexp
    rwa [hfG] at this


theorem _root_.ConvexOn.exists_measurable_hessian {G : E → ℝ} (hG : ConvexOn ℝ univ G) :
    ∃ Hs : E → (E →L[ℝ] E), Measurable Hs ∧ ∀ᵐ x ∂μ, (Hs x).IsPositive ∧
      (fun x' => G x' - G x - ⟪gradient G x, x' - x⟫_ℝ - ⟪Hs x (x' - x), x' - x⟫_ℝ / 2)
        =o[𝓝 x] (fun x' => ‖x' - x‖ ^ 2) ∧
      ∀ t : Set E, (∀ x' ∈ t, DifferentiableAt ℝ G x') →
        HasFDerivWithinAt (gradient G) (Hs x) t x := by
  classical
  have hcont : Continuous G := continuousOn_univ.mp (hG.continuousOn isOpen_univ)
  set b := stdOrthonormalBasis ℝ E with hb
  set P : ℕ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ :=
    fun k i j x => (secondDiff G k (b i + b j) x - secondDiff G k (b i) x
      - secondDiff G k (b j) x) / 2 with hP
  set a : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ :=
    fun i j x => limsup (fun k => P k i j x) atTop with ha
  set R : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E →L[ℝ] E :=
    fun i j => (innerSL ℝ (b j)).smulRight (b i) with hR
  set Hs : E → E →L[ℝ] E := fun x => ∑ i, ∑ j, a i j x • R i j with hHs
  refine ⟨Hs, ?_, ?_⟩
  · refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    refine Measurable.smul_const ?_ _
    refine Measurable.limsup fun k => ?_
    refine Continuous.measurable ?_
    simp only [hP, secondDiff]
    fun_prop
  · filter_upwards [ConvexOn.ae_exists_isPositive_hasFDerivWithinAt_gradient (μ := μ) hG] with x
      ⟨A, hA, hexp, hder⟩
    have hlim : ∀ i j, Tendsto (fun k => P k i j x) atTop (𝓝 ⟪A (b j), b i⟫_ℝ) := by
      intro i j
      have := (((tendsto_secondDiff hexp (b i + b j)).sub (tendsto_secondDiff hexp (b i))).sub
        (tendsto_secondDiff hexp (b j))).div_const 2
      convert this using 2
      have h1 : ⟪A (b i), b j⟫_ℝ = ⟪A (b j), b i⟫_ℝ := by
        have s := hA.isSymmetric (b i) (b j)
        change ⟪A (b i), b j⟫_ℝ = ⟪b i, A (b j)⟫_ℝ at s
        rw [s, real_inner_comm]
      simp only [map_add, inner_add_left, inner_add_right, h1]
      ring
    have haij : ∀ i j, a i j x = ⟪A (b j), b i⟫_ℝ := fun i j => (hlim i j).limsup_eq
    have hH : Hs x = A := by
      apply ContinuousLinearMap.coe_injective
      apply b.toBasis.ext
      intro l
      have e1 : ∀ i j, (a i j x • R i j) (b l) = if j = l then a i l x • b i else 0 := by
        intro i j
        simp only [hR, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
          innerSL_apply_apply, b.inner_eq_ite]
        by_cases h : j = l <;> simp [h]
      simp only [OrthonormalBasis.coe_toBasis, hHs, ContinuousLinearMap.coe_coe,
        _root_.sum_apply, e1]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, haij]
      refine Eq.trans ?_ (b.sum_repr' (A (b l)))
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_comm]
    rw [hH]
    exact ⟨hA, hexp, hder⟩
end Alexandrov
end CvxBody.Geometry
