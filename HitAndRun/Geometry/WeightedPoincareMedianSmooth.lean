module
public import HitAndRun.Sobolev.WeakDerivativeMollifier
public import HitAndRun.Sobolev.SmoothGraph
public import HitAndRun.Geometry.InnerBall
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Sobolev Set
open scoped Convolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

lemma inner_mollification (rho : ContDiffBump (0 : E))
    {G : E → E} (hG : LocallyIntegrable G μ) (x v : E) :
    inner ℝ ((rho.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] G) x) v =
      ((fun y => inner ℝ (G y) v) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x := by
  have hi := ((rho.hasCompactSupport_normed (μ := μ)).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (rho.contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) (rho.normed μ)).continuous hG x).integrable_swap
  rw [convolution_eq_swap, convolution_def]
  have h := (innerSL ℝ v).integral_comp_comm hi
  simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, innerSL_apply_apply,
    inner_smul_right, real_inner_comm, mul_comm] using h.symm

/-- Actual vector gradient after interior mollification of a weak H1 identity. -/
theorem gradient_mollified_of_weak_gradient
    (rho : ContDiffBump (0 : E)) (x : E)
    (hs : Metric.closedBall x rho.rOut ⊆ Ω)
    (h : E → ℝ) (G : E → E) (hh : LocallyIntegrable h μ) (hG : LocallyIntegrable G μ)
    (hrel : ∀ (v : E) (φ : testFunctions Ω),
      (∫ y, h y * fderiv ℝ (φ : E → ℝ) y v ∂μ) =
        -(∫ y, inner ℝ (G y) v * (φ : E → ℝ) y ∂μ)) :
    gradient (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x =
      (rho.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] G) x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, inner_mollification rho hG]
  exact fderiv_mollified_of_weak_partial rho x hs h _ v hh (hrel v)

/-- The support required by mollification fits uniformly at every inward point. -/
theorem closedBall_subset_at_contraction {K : Set E} (hK : Convex ℝ K)
    {r a s : ℝ} (hball : Metric.ball (0 : E) r ⊆ K)
    {x : E} (hx : x ∈ K) (ha : 0 ≤ a) (ha1 : a < 1)
    (hs : s < (1 - a) * r) : Metric.closedBall (a • x) s ⊆ K :=
  (Metric.closedBall_subset_ball hs).trans (ball_subset_at_contraction hK hball hx ha ha1)
/-- Zero extension of the two actual W12 components preserves all interior
weak identities; no derivative is claimed across the boundary. -/
theorem weak_graph_zero_extension_identity (ho : IsOpen Ω) (U : W12 μ Ω)
    (v : E) (φ : testFunctions Ω) :
    (∫ y, Ω.indicator (fnL U.val) y * fderiv ℝ (φ : E → ℝ) y v ∂μ) =
      -(∫ y, inner ℝ (Ω.indicator (gradL U.val) y) v * (φ : E → ℝ) y ∂μ) := by
  have hw := ((mem_W12_iff_hasWeakFDerivOn ho U.val).mp U.property v).integral_eq
    φ.2.1 φ.2.2.1 φ.2.2.2
  have hleft : (fun y => Ω.indicator (fnL U.val) y * fderiv ℝ (φ : E → ℝ) y v) =
      (fun y => fderiv ℝ (φ : E → ℝ) y v • fnL U.val y) := by
    funext y
    by_cases hy : y ∈ Ω
    · simp [Set.indicator_of_mem hy, smul_eq_mul, mul_comm]
    · have hn : y ∉ tsupport (φ : E → ℝ) := fun h => hy (φ.2.2.2 h)
      simp [Set.indicator_of_notMem hy, fderiv_of_notMem_tsupport ℝ hn]
  have hright : (fun y => inner ℝ (Ω.indicator (gradL U.val) y) v * (φ : E → ℝ) y) =
      (fun y => (φ : E → ℝ) y • innerSL ℝ (gradL U.val y) v) := by
    funext y
    by_cases hy : y ∈ Ω
    · simp [Set.indicator_of_mem hy, smul_eq_mul, mul_comm]
    · have hz : (φ : E → ℝ) y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (φ.2.2.2 h))
      simp [Set.indicator_of_notMem hy, hz]
  rw [hleft, hright]
  exact hw
lemma gradient_comp_dilation (f : E → ℝ) (a : ℝ) (x : E)
    (hf : DifferentiableAt ℝ f (a • x)) :
    gradient (fun y => f (a • y)) x = a • gradient f (a • x) := by
  apply ext_inner_right ℝ
  intro v
  have hd := hf.hasFDerivAt.comp x (a • ContinuousLinearMap.id ℝ E).hasFDerivAt
  rw [inner_gradient_left]
  change (fderiv ℝ (f ∘ HSMul.hSMul a) x) v = _
  rw [hd.fderiv]
  simp [inner_smul_left, inner_gradient_left]
/-- Concrete gradient of an inward-smoothed actual W12 element. -/
theorem gradient_inward_mollified_W12 (ho : IsOpen Ω) (hc : Convex ℝ Ω)
    {r a : ℝ} (hball : Metric.ball (0 : E) r ⊆ Ω)
    (ha : 0 ≤ a) (ha1 : a < 1) (rho : ContDiffBump (0 : E))
    (hrho : rho.rOut < (1 - a) * r) (U : W12 μ Ω) {x : E} (hx : x ∈ Ω) :
    gradient (fun y =>
      (Ω.indicator (fnL U.val) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) (a • y)) x =
      a • (rho.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] Ω.indicator (gradL U.val)) (a • x) := by
  have hf : MemLp (Ω.indicator (fnL U.val)) 2 μ :=
    (memLp_indicator_iff_restrict ho.measurableSet.nullMeasurableSet).mpr (Lp.memLp _)
  have hg : MemLp (Ω.indicator (gradL U.val)) 2 μ :=
    (memLp_indicator_iff_restrict ho.measurableSet.nullMeasurableSet).mpr (Lp.memLp _)
  have hfl := hf.locallyIntegrable (by norm_num)
  have hgl := hg.locallyIntegrable (by norm_num)
  rw [gradient_comp_dilation _ a x
    ((EllipticPdes.Embedding.contDiff_convolution_normed rho hfl).differentiable (by simp) _)]
  congr 1
  exact gradient_mollified_of_weak_gradient rho (a • x)
    (closedBall_subset_at_contraction hc hball hx ha ha1 hrho) _ _ hfl hgl
    (weak_graph_zero_extension_identity ho U)
end HitAndRun.Geometry
