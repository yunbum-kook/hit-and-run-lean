module
public import HitAndRun.Sobolev.CurlEnergyResidual
public import HitAndRun.Sobolev.UniformSource
@[expose] public section

/-! Lemma B.3 for the actual uniform-domain zero-trace Sobolev carrier. -/
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open scoped BigOperators RealInnerProductSpace
variable {n : ℕ} [NeZero n]

/-- Exact divergence/curl identity, with the manuscript's upper-triangle convention. -/
theorem curl_energy (K : BoundedOpenDomain n) (u : K.Field) :
    ‖u‖ ^ 2 = ‖K.div u‖ ^ 2 +
      ∑ i, ∑ j, if i < j then ‖weakPartial u i j - weakPartial u j i‖ ^ 2 else 0 :=
  divergence_curl_energy u

/-- The same statement for a literal vector of zero-trace weak Sobolev functions. -/
theorem graph_curl_energy (K : BoundedOpenDomain n)
    (u : Fin n → H01 K.ambient K.carrier) :
    (∑ i, ‖gradL (u i : H1Graph K.ambient K.carrier)‖ ^ 2) =
      ‖K.div (vectorFieldOfGraph K.isBounded u)‖ ^ 2 +
      ∑ i, ∑ j, if i < j then
        ‖weakPartial (vectorFieldOfGraph K.isBounded u) i j -
          weakPartial (vectorFieldOfGraph K.isBounded u) j i‖ ^ 2 else 0 := by
  rw [← vectorField_graph_energy K.isBounded u]
  exact K.curl_energy _
end HitAndRun.Sobolev.BoundedOpenDomain
