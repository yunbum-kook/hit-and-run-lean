module
public import HitAndRun.Sobolev.WeightedCutoffApproximation
public import HitAndRun.Sobolev.ImprovedPoincareLimit
public import HitAndRun.Sobolev.WeightedGradientEnergyIdentity
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory ProbabilityTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry Set Filter
open scoped Topology
namespace BoundedOpenDomain
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

theorem exists_weightedH1_approximants
    (h : Lp ℝ 2 (K.ambient.restrict K.carrier))
    (q : Lp (EuclideanSpace ℝ (Fin n)) 2 (K.ambient.restrict K.carrier))
    (hw : HasWeakFDerivOn ⟨K.carrier, K.isOpen⟩ h
      (fun x => innerSL ℝ ((interiorDistance K.carrier x)⁻¹ • q x)) K.ambient) :
    ∃ u : ℕ → K.H1,
      Tendsto (fun k => fnL (u k : H1Graph K.ambient K.carrier)) atTop (𝓝 h) ∧
      Tendsto (fun k => (K.weightedGradientEnergy (u k)).toReal) atTop (𝓝 (‖q‖ ^ 2)) := by
  have hne : K.carrier ≠ Set.univ := by
    intro he
    exact NormedSpace.unbounded_univ ℝ (EuclideanSpace ℝ (Fin n)) (he ▸ K.isBounded)
  have hc : K.carrierᶜ.Nonempty := Set.nonempty_compl.mpr hne
  obtain ⟨u, w, huf, hwlim, huw⟩ := exists_weightedCutoff_approximants
    K.isBounded K.isOpen hc h q hw
  refine ⟨u, huf, ?_⟩
  have he (k : ℕ) : (K.weightedGradientEnergy (u k)).toReal = ‖w k‖ ^ 2 := by
    apply K.weightedGradientEnergy_toReal_eq_norm_sq_of_ae
    filter_upwards [huw k, ae_restrict_mem K.isOpen.measurableSet] with x hx hxm
    have hd := interiorDistance_eq_frontier K.isOpen hne hxm
    simpa only [boundaryDistance, hd] using hx
  simp_rw [he]
  exact hwlim.norm.pow 2

/-- The IPI extends to genuine locally weak gradients with only weighted L2 control.
The original function is not assumed to belong to global or domain W12. -/
theorem improvedPoincare_of_weighted_weak_gradient (hC : K.improvedPoincareConstant < ⊤)
    (h : Lp ℝ 2 (K.ambient.restrict K.carrier))
    (q : Lp (EuclideanSpace ℝ (Fin n)) 2 (K.ambient.restrict K.carrier))
    (hw : HasWeakFDerivOn ⟨K.carrier, K.isOpen⟩ h
      (fun x => innerSL ℝ ((interiorDistance K.carrier x)⁻¹ • q x)) K.ambient) :
    variance h (K.ambient.restrict K.carrier) ≤ K.improvedPoincareConstant.toReal * ‖q‖ ^ 2 := by
  obtain ⟨u, hu, he⟩ := K.exists_weightedH1_approximants h q hw
  exact K.improvedPoincare_limit hC u h (‖q‖ ^ 2) hu he

theorem improvedPoincare_centered_of_weighted_weak_gradient
    (hC : K.improvedPoincareConstant < ⊤) (h : K.Target)
    (q : Lp (EuclideanSpace ℝ (Fin n)) 2 (K.ambient.restrict K.carrier))
    (hw : HasWeakFDerivOn ⟨K.carrier, K.isOpen⟩ h.val
      (fun x => innerSL ℝ ((interiorDistance K.carrier x)⁻¹ • q x)) K.ambient) :
    ‖h‖ ^ 2 ≤ K.improvedPoincareConstant.toReal * ‖q‖ ^ 2 := by
  obtain ⟨u, hu, he⟩ := K.exists_weightedH1_approximants h.val q hw
  exact K.improvedPoincare_centered_limit hC u h (‖q‖ ^ 2) hu he
end BoundedOpenDomain
end HitAndRun.Sobolev
