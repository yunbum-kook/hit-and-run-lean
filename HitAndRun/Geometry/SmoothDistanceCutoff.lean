module
public import HitAndRun.Geometry.DistanceCutoff
public import HitAndRun.Analysis.MollifierLipschitz
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! Actual smooth interior cutoff obtained from the truncated distance, preserving
Lipschitz constant1 and uniformly approximating the boundary distance. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Metric Set EllipticPdes Filter Topology
open scoped Convolution NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

def smoothDistanceCutoff (Ω : Set E) (epsilon : ℝ) (rho : ContDiffBump (0 : E)) : E → ℝ :=
  rho.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] truncatedDistance Ω epsilon

theorem smoothDistanceCutoff_smooth (Ω : Set E) (epsilon : ℝ) (rho : ContDiffBump (0 : E)) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothDistanceCutoff (μ := μ) Ω epsilon rho) :=
  contDiff_normed_convolution rho (truncatedDistance_lipschitz Ω epsilon).continuous.locallyIntegrable

theorem smoothDistanceCutoff_lipschitz (Ω : Set E) (epsilon : ℝ) (rho : ContDiffBump (0 : E)) :
    LipschitzWith 1 (smoothDistanceCutoff (μ := μ) Ω epsilon rho) :=
  HitAndRun.Analysis.lipschitz_normed_convolution rho (truncatedDistance_lipschitz Ω epsilon)

theorem smoothDistanceCutoff_fderiv_le (Ω : Set E) (epsilon : ℝ)
    (rho : ContDiffBump (0 : E)) (x : E) :
    ‖fderiv ℝ (smoothDistanceCutoff (μ := μ) Ω epsilon rho) x‖ ≤ 1 :=
  norm_fderiv_le_of_lipschitz ℝ (smoothDistanceCutoff_lipschitz Ω epsilon rho)

theorem smoothDistanceCutoff_compact {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {epsilon : ℝ} (he : 0 < epsilon) (rho : ContDiffBump (0 : E)) :
    HasCompactSupport (smoothDistanceCutoff (μ := μ) Ω epsilon rho) :=
  hasCompactSupport_normed_convolution rho (hasCompactSupport_truncatedDistance hb he)

theorem smoothDistanceCutoff_support_margin {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {epsilon : ℝ} (he : 0 < epsilon) (rho : ContDiffBump (0 : E)) (hr : rho.rOut ≤ epsilon) :
    tsupport (smoothDistanceCutoff (μ := μ) Ω epsilon rho) ⊆
      {x | epsilon ≤ interiorDistance Ω x} := by
  intro x hx
  have hc := hasCompactSupport_truncatedDistance hb he
  have ht := tsupport_normed_convolution_subset (μ := μ) rho hc hx
  rw [hc.cthickening_eq_biUnion_closedBall rho.rOut_pos.le] at ht
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp ht
  have hdy := tsupport_truncatedDistance_subset he hy
  change 2 * epsilon ≤ interiorDistance Ω y at hdy
  have hl := (interiorDistance_lipschitz Ω).dist_le_mul x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hl
  have hd := (abs_le.mp hl).1
  have hxy' : dist x y ≤ rho.rOut := hxy
  change epsilon ≤ interiorDistance Ω x
  linarith

theorem smoothDistanceCutoff_support_domain {Ω : Set E} (hb : Bornology.IsBounded Ω)
    {epsilon : ℝ} (he : 0 < epsilon) (rho : ContDiffBump (0 : E)) (hr : rho.rOut ≤ epsilon) :
    tsupport (smoothDistanceCutoff (μ := μ) Ω epsilon rho) ⊆ Ω := by
  intro x hx
  have hm := smoothDistanceCutoff_support_margin hb he rho hr hx
  change epsilon ≤ interiorDistance Ω x at hm
  by_contra hn
  rw [interiorDistance_zero_outside hn] at hm
  linarith

/-- Uniform approximation with explicit error, independent of boundary smoothness. -/
theorem smoothDistanceCutoff_error {Ω : Set E} {epsilon : ℝ} (he : 0 < epsilon)
    (rho : ContDiffBump (0 : E)) (hr : rho.rOut ≤ epsilon) (x : E) :
    ‖smoothDistanceCutoff (μ := μ) Ω epsilon rho x - interiorDistance Ω x‖ ≤ 3 * epsilon := by
  have hm := HitAndRun.Analysis.norm_normed_convolution_sub_le (μ := μ) rho
    (truncatedDistance_lipschitz Ω epsilon) x
  simp only [NNReal.coe_one, one_mul] at hm
  have ht : ‖truncatedDistance Ω epsilon x - interiorDistance Ω x‖ ≤ 2 * epsilon := by
    rw [Real.norm_eq_abs, abs_le]
    have hd : 0 ≤ interiorDistance Ω x := infDist_nonneg
    have hlo := le_max_left (interiorDistance Ω x - 2 * epsilon) 0
    have hup : truncatedDistance Ω epsilon x ≤ interiorDistance Ω x :=
      max_le (by linarith) hd
    constructor <;> dsimp [truncatedDistance] at * <;> linarith
  have hn := norm_sub_le_norm_sub_add_norm_sub (smoothDistanceCutoff (μ := μ) Ω epsilon rho x)
    (truncatedDistance Ω epsilon x) (interiorDistance Ω x)
  change ‖smoothDistanceCutoff (μ := μ) Ω epsilon rho x - truncatedDistance Ω epsilon x‖ ≤ _ at hm
  linarith

/-- An actual sequence of smooth, compact interior cutoffs, not an assumed family. -/
def distanceCutoffSequence (Ω : Set E) (n : ℕ) : E → ℝ :=
  let rho : ContDiffBump (0 : E) := mollifier (show (0 : ℝ) < 1 by norm_num) n
  smoothDistanceCutoff (μ := μ) Ω rho.rOut rho

theorem distanceCutoffSequence_smooth (Ω : Set E) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (distanceCutoffSequence (μ := μ) Ω n) :=
  smoothDistanceCutoff_smooth _ _ _

theorem distanceCutoffSequence_lipschitz (Ω : Set E) (n : ℕ) :
    LipschitzWith 1 (distanceCutoffSequence (μ := μ) Ω n) :=
  smoothDistanceCutoff_lipschitz _ _ _

theorem distanceCutoffSequence_compact {Ω : Set E} (hb : Bornology.IsBounded Ω) (n : ℕ) :
    HasCompactSupport (distanceCutoffSequence (μ := μ) Ω n) :=
  smoothDistanceCutoff_compact hb (ContDiffBump.rOut_pos _) _

theorem distanceCutoffSequence_support {Ω : Set E} (hb : Bornology.IsBounded Ω) (n : ℕ) :
    tsupport (distanceCutoffSequence (μ := μ) Ω n) ⊆ Ω := by
  exact smoothDistanceCutoff_support_domain hb (ContDiffBump.rOut_pos _) _ le_rfl

theorem distanceCutoffSequence_error (Ω : Set E) (n : ℕ) (x : E) :
    ‖distanceCutoffSequence (μ := μ) Ω n x - interiorDistance Ω x‖ ≤
      3 * (mollifier (show (0 : ℝ) < 1 by norm_num) n : ContDiffBump (0 : E)).rOut :=
  smoothDistanceCutoff_error (ContDiffBump.rOut_pos _) _ le_rfl x


theorem distanceCutoffSequence_tendsto (Ω : Set E) (x : E) :
    Tendsto (fun n => distanceCutoffSequence (μ := μ) Ω n x) atTop
      (𝓝 (interiorDistance Ω x)) := by
  have hz : Tendsto (fun n => distanceCutoffSequence (μ := μ) Ω n x - interiorDistance Ω x)
      atTop (𝓝 0) := squeeze_zero_norm (fun n => distanceCutoffSequence_error Ω n x)
    (by simpa using (tendsto_rOut_mollifier (E := E)
      (show (0 : ℝ) < 1 by norm_num)).const_mul 3)
  simpa only [sub_add_cancel, zero_add] using hz.add_const (interiorDistance Ω x)


/-- The operator norm bound gives the exact coordinate gradient energy bound. -/
theorem distanceCutoffSequence_gradient_energy
    {d : ℕ} {ν : Measure (EuclideanSpace ℝ (Fin d))} [ν.IsAddHaarMeasure]
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    (∑ i, (fderiv ℝ (distanceCutoffSequence (μ := ν) Ω n) x (b i)) ^ 2) ≤ 1 := by
  rw [← b.norm_dual]
  have hn : ‖fderiv ℝ (distanceCutoffSequence (μ := ν) Ω n) x‖ ≤ 1 :=
    norm_fderiv_le_of_lipschitz ℝ (distanceCutoffSequence_lipschitz Ω n)
  have hp := norm_nonneg (fderiv ℝ (distanceCutoffSequence (μ := ν) Ω n) x)
  nlinarith

end HitAndRun.Geometry
