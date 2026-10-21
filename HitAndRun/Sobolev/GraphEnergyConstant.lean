module

public import HitAndRun.Sobolev.UniformSource

/-! Exact source CBA definition on the original H01 graph carrier. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Analysis
open scoped ENNReal BigOperators
variable {n : ℕ} [NeZero n]

/-- The constant is literally the source supremum of infima over actual H01
vector graphs, with the quotient inside the infimum and full gradient energy. -/
theorem constant_eq_graph_source (K : BoundedOpenDomain n) :
    K.constant =
      ⨆ f : {f : K.Target // f ≠ 0},
        ⨅ u : {u : Fin n → H01 K.ambient K.carrier //
          K.div (vectorFieldOfGraph K.isBounded u) = f.val},
          ENNReal.ofReal (∑ i : Fin n,
            ‖gradL (u.val i : H1Graph K.ambient K.carrier)‖ ^ 2) /
              ENNReal.ofReal (‖f.val‖ ^ 2) := by
  unfold constant
  rw [babuskaAzizConstant_eq_source]
  congr 1
  funext f
  apply le_antisymm
  · apply le_iInf
    intro u
    apply iInf_le_of_le ⟨vectorFieldOfGraph K.isBounded u.val, u.property⟩
    have he := vectorField_graph_energy (μ := K.ambient) K.isBounded u.val
    change ‖vectorFieldOfGraph K.isBounded u.val‖ ^ 2 = _ at he
    exact le_of_eq (by rw [he])
  · apply le_iInf
    intro v
    have hv : K.div (vectorFieldOfGraph K.isBounded
        (graphOfVectorField K.isBounded v.val)) = f.val := by
      simpa only [vectorFieldOfGraph_graphOfVectorField] using v.property
    apply iInf_le_of_le ⟨graphOfVectorField K.isBounded v.val, hv⟩
    exact le_of_eq (by rw [graphOfVectorField_energy])
end HitAndRun.Sobolev.BoundedOpenDomain
