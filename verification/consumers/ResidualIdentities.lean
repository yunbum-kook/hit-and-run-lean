import HitAndRun.Sobolev.ResidualIdentities
import HitAndRun.Sobolev.GraphEnergyConstant
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Analysis HitAndRun.Sobolev
open scoped ENNReal BigOperators InnerProduct
namespace HitAndRun.Sobolev.BoundedOpenDomain
variable {n : ℕ} [NeZero n]
example (K : BoundedOpenDomain n) (f : K.Target) :
    meanCLM K.ambient K.carrier (divergenceResidual f (K.rieszField f)) = 0 ∧
    (∀ (φ : testFunctions K.carrier) (i : Fin n),
      (∫ x in K.carrier, divergenceResidual f (K.rieszField f) x *
        fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x (EuclideanSpace.basisFun (Fin n) ℝ i)
          ∂K.ambient) =
        ∑ j : Fin n, ∫ x in K.carrier,
          (weakPartial (K.rieszField f) i j - weakPartial (K.rieszField f) j i) x *
          fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x (EuclideanSpace.basisFun (Fin n) ℝ j)
            ∂K.ambient) ∧
    inner ℝ (divergenceResidual f (K.rieszField f)) (divergence K.ambient K.carrier (K.rieszField f)) =
      ∑ i, ∑ j, if i < j then
        ‖weakPartial (K.rieszField f) i j - weakPartial (K.rieszField f) j i‖ ^ 2 else 0 := K.residual_identities f
example (K : BoundedOpenDomain n) :
    K.constant =
      ⨆ f : {f : K.Target // f ≠ 0},
        ⨅ u : {u : Fin n → H01 K.ambient K.carrier //
          K.div (vectorFieldOfGraph K.isBounded u) = f.val},
          ENNReal.ofReal (∑ i : Fin n,
            ‖gradL (u.val i : H1Graph K.ambient K.carrier)‖ ^ 2) /
              ENNReal.ofReal (‖f.val‖ ^ 2) := K.constant_eq_graph_source
end HitAndRun.Sobolev.BoundedOpenDomain
#print axioms HitAndRun.Sobolev.lp_coordinate_inner
#print axioms HitAndRun.Sobolev.divergence_testVector
#print axioms HitAndRun.Sobolev.inner_testVector
#print axioms HitAndRun.Sobolev.weakPartial_test_cross
#print axioms HitAndRun.Sobolev.divergenceResidual_distribution
#print axioms HitAndRun.Sobolev.inner_partialCls_integral
#print axioms HitAndRun.Sobolev.divergenceResidual_distribution_integral
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.rieszField_equation
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.residual_identities
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.constant_eq_graph_source
