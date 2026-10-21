module
public import HitAndRun.Sobolev.BoundaryTestLimit
public import HitAndRun.Sobolev.WeightedTestIntegral
public import HitAndRun.Analysis.VectorQuotientLimit

/-! Exact finite-vector test energies converge under exhaustion by inner domains. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry Filter Topology
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}
  {ι : Type*} [Fintype ι]

def vectorTestField (b : ι → E) (φ : ι → testFunctions Ω) : E → E :=
  fun x => ∑ i, (φ i : E → ℝ) x • b i

theorem vectorTestField_continuous (b : ι → E) (φ : ι → testFunctions Ω) :
    Continuous (vectorTestField b φ) :=
  continuous_finset_sum _ (fun i _ => (φ i).2.1.continuous.smul continuous_const)

theorem vectorTestField_compact (b : ι → E) (φ : ι → testFunctions Ω) :
    HasCompactSupport (vectorTestField b φ) := by
  classical
  have hs (s : Finset ι) : HasCompactSupport (fun x => ∑ i ∈ s, (φ i : E → ℝ) x • b i) := by
    induction s using Finset.induction_on with
    | empty =>
      convert (HasCompactSupport.zero : HasCompactSupport (0 : E → E)) using 1
      ext x
      simp
    | @insert i s hi ih =>
      convert ((φ i).2.2.1.smul_right (f' := fun _ => b i)).add ih using 1
      ext x
      simp only [Finset.sum_insert hi, Pi.add_apply, Pi.smul_apply]
      rfl
  change HasCompactSupport (fun x => ∑ i, (φ i : E → ℝ) x • b i)
  simpa using hs Finset.univ

theorem vectorTestField_support (b : ι → E) (φ : ι → testFunctions Ω)
    {x : E} (hx : x ∈ Function.support (vectorTestField b φ)) :
    ∃ i, x ∈ Function.support (φ i : E → ℝ) := by
  classical
  by_contra hn
  push_neg at hn
  apply hx
  simp [vectorTestField, Function.notMem_support.mp (hn _)]

theorem norm_sq_vectorTestCoefficient_global (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (b : ι → E) (φ : ι → testFunctions Ω) :
    ‖vectorTestCoefficient (μ := μ) ho hc b φ‖ ^ 2 =
      ∫ x, ‖(interiorDistance Ω x)⁻¹ • vectorTestField b φ x‖ ^ 2 ∂μ := by
  rw [norm_sq_vectorTestCoefficient]
  have he (x : E) : (∑ i, boundaryTest (φ i) x • b i) =
      (interiorDistance Ω x)⁻¹ • vectorTestField b φ x := by
    simp only [vectorTestField, Finset.smul_sum, boundaryTest, div_eq_mul_inv, smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  simp_rw [he]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : vectorTestField b φ x = 0 := by
    by_contra hn
    obtain ⟨i, hi⟩ := vectorTestField_support b φ hn
    exact hx ((φ i).2.2.2 (subset_closure hi))
  simp [hz]

theorem vectorTest_inner_energy_tendsto (hc : Ωᶜ.Nonempty)
    (b : ι → E) (φ : ι → testFunctions Ω) {e : ℝ} (he : 0 < e)
    (hmargin : ∀ i x, x ∈ tsupport (φ i : E → ℝ) → e ≤ interiorDistance Ω x)
    {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) (hrb : ∀ k, r k ≤ e / 2)
    (ht : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x,
      ‖(interiorDistance (innerDomain Ω (r k)) x)⁻¹ • vectorTestField b φ x‖ ^ 2 ∂μ)
      atTop (𝓝 (∫ x, ‖(interiorDistance Ω x)⁻¹ • vectorTestField b φ x‖ ^ 2 ∂μ)) := by
  apply HitAndRun.Analysis.integral_sq_inv_smul_tendsto
    (vectorTestField_continuous b φ) (vectorTestField_compact b φ)
    (interiorDistance_lipschitz Ω).continuous
    (fun k => (interiorDistance_lipschitz (innerDomain Ω (r k))).continuous)
    (half_pos he)
  · intro x hx
    obtain ⟨i, hi⟩ := vectorTestField_support b φ hx
    have hm := hmargin i x (subset_closure hi)
    linarith
  · intro k x hx
    obtain ⟨i, hi⟩ := vectorTestField_support b φ hx
    have hm := hmargin i x (subset_closure hi)
    have hl := innerDomain_distance_lower hc (hr k) x
    linarith [hrb k]
  · exact innerDomain_distance_tendsto hc hr ht
end HitAndRun.Sobolev
