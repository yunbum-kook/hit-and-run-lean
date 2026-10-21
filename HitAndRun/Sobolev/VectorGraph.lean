import HitAndRun.Sobolev.SourceDuality

/-! Explicit two-way correspondence between gradient-norm fields and H01 vector graphs. -/
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open scoped BigOperators
variable {n : ℕ} [NeZero n]
variable {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]
variable {Ω : Set (EuclideanSpace ℝ (Fin n))}
variable [IsFiniteMeasure (μ.restrict Ω)]

/-- Coordinatewise actual H01 graph underlying a gradient-norm vector field. -/
def graphOfVectorField (hb : Bornology.IsBounded Ω) (u : VectorField μ Ω) :
    Fin n → H01 μ Ω := fun i => (gradientEquiv (μ := μ) hb).symm (u i)

/-- Map an actual H01 vector graph into its genuine gradient-norm field. -/
def vectorFieldOfGraph (hb : Bornology.IsBounded Ω) (u : Fin n → H01 μ Ω) :
    VectorField μ Ω := WithLp.toLp 2 (fun i => gradientEquiv (μ := μ) hb (u i))

theorem vectorFieldOfGraph_graphOfVectorField (hb : Bornology.IsBounded Ω)
    (u : VectorField μ Ω) : vectorFieldOfGraph hb (graphOfVectorField hb u) = u := by
  apply PiLp.ext
  intro i
  exact (gradientEquiv (μ := μ) hb).apply_symm_apply (u i)

theorem graphOfVectorField_vectorFieldOfGraph (hb : Bornology.IsBounded Ω)
    (u : Fin n → H01 μ Ω) : graphOfVectorField hb (vectorFieldOfGraph hb u) = u := by
  funext i
  exact (gradientEquiv (μ := μ) hb).symm_apply_apply (u i)

/-- Every genuine field has exactly the full gradient energy of its H01 representative. -/
theorem graphOfVectorField_energy (hb : Bornology.IsBounded Ω) (u : VectorField μ Ω) :
    ∑ i : Fin n, ‖gradL (graphOfVectorField hb u i : H1Graph μ Ω)‖ ^ 2 = ‖u‖ ^ 2 := by
  have h := vectorField_graph_energy (μ := μ) hb (graphOfVectorField hb u)
  change ‖vectorFieldOfGraph hb (graphOfVectorField hb u)‖ ^ 2 = _ at h
  rw [vectorFieldOfGraph_graphOfVectorField] at h
  exact h.symm
end HitAndRun.Sobolev
