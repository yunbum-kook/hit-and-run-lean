# Quantitative duality (B.1 infrastructure)

## Discovery and chosen route
Pinned Mathlib has `IsCoercive.continuousLinearEquivOfBilin` in
`Mathlib.Analysis.InnerProductSpace.LaxMilgram`, which already proves the
closed-range and surjectivity steps. Reuse it for the bilinear form
B(f,g)=inner(D D* f,g). The lower bound norm(f)^2 <= C norm(D*f)^2,
with C>0, supplies coercivity constant 1/C. A solution g of D D* g=f gives
v=D*g. Cauchy–Schwarz and the same lower bound give norm(v)^2 <= C norm(f)^2,
without losing a constant. The converse follows by applying the witness
estimate and Cauchy–Schwarz. The previously compiled Riesz norm/supremum
identity converts this to the paper's exact nonzero-test-vector formulation.

Alternative APIs inspected: `ContinuousLinearMap.orthogonal_ker`,
`closed_range_of_antilipschitz`, `AntilipschitzWith.completeSpace_range_clm`.
Lax–Milgram is shorter and avoids recreating their closed-range proof.

## Status
Analysis/Duality.lean compiled successfully. Both directions and exact signed-supremum equivalence are independently consumed with full statement types.
This is generic real-Hilbert infrastructure, not completed source Lemma B.1:
the actual Sobolev carrier, its gradient inner product and bounded divergence
still require construction. The norm-adjoint version permits trivial spaces;
the signed quotient supremum uses Nontrivial V so its test set is nonempty.

## Queued extended-energy work
Use ENNReal fiber infima, with empty fibers equal infinity. Prove finite
energy iff feasibility, attainment using the minimum-norm projection helper,
and the normalized supremum constant. Do not use empty real infima.

## Extended energy implementation draft
`Analysis/MinimumEnergy.lean` defines an ENNReal infimum over the actual fiber
and a supremum of normalized energies over nonzero targets. It proves
finiteness iff feasibility, attainment, finiteness of the supremum implies
surjectivity, exact equivalence of a real constant bound and witnesses, and
witnesses at the finite optimal constant itself. Compilation and imported-consumer check passed. All 11 public declarations audited with only propext, Classical.choice and Quot.sound. See verification/duality-energy.json.

## Actual Sobolev carrier discovery
The pinned `Analysis/Distribution/Sobolev` is Fourier/Bessel-potential Sobolev
on whole Euclidean space with complex codomain, not the bounded-domain
real H¹₀ carrier with gradient inner product. `FunctionalSpaces/SobolevInequality`
provides compact-supported C¹ inequalities, not that carrier. A candidate
construction is the closed graph of compact-smooth pairs in L²×L²-gradient,
followed by weak derivative uniqueness and Poincaré norm equivalence.
These bridges remain unproved; mere import of Mathlib's Sobolev module does
not complete them.

Update: the parallel EllipticPDE adaptation now supplies the actual H01 graph
and `External/EllipticPDE/GradientSpace.lean`: gradient range is closed using
bounded-domain Poincaré and identified linearly with H01, with exact gradient
norm. This satisfies the scalar real-Hilbert assumptions once its completeness
instance is installed. Vector fields need PiLp 2 over coordinates (not the
ordinary Pi supremum norm); centered L² codomain and divergence zero-mean proof
remain the next concrete bridge. Earlier Mathlib-only absence is not a blocker
for this adapted route.

## Concrete actual-divergence verification
SourceDuality, Nontrivial and UniformMeasure compiled successfully. The imported
consumer checks four full statements and all 16 public results use only
propext/Classical.choice/Quot.sound. The carrier is actual PiLp 2 of closed
zero-trace weak-gradient ranges; divergence is the actual sum of diagonal
weak partial derivatives, with zero mean proved separately. Source CBA's
sup-inf quotient equals the generic inf-then-divide expression by
ENNReal.iInf_div_of_ne, including empty fibers. The gradient norm identity is
literal sum of genuine gradient L2 energies.

A compact smooth interior bump proves H01 is nontrivial using continuous
functions' pointwise equality from ae equality on the open domain. Poincaré
injectivity transports this to gradientSpace and hence VectorField.
Normalized ambient Haar and its restriction are proved equal to the actual
uniform probability measure. No extra Nontrivial assumption is needed in the
final geometric wrapper. That wrapper is being completed separately before
any source-result completion is counted. Evidence: verification/source-duality.json.

The next source-facing wrapper uses a bounded open nonempty domain (a stronger
theorem than requiring convexity), normalized ambient Haar restricted to that
domain, and derives all completeness/nontriviality instances from geometry.
`VectorGraph` explicitly maps between H01 coordinate graphs and gradient fields
in both directions and transfers exact full gradient energy. `UniformSource`
then exposes the finite-optimal solver as an actual H01 graph, plus exact B.1
and B.2 statements without extra analytical premises. These two files are
currently drafts awaiting serial compilation and source review.
