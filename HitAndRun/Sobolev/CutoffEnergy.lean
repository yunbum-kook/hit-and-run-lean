module
public import HitAndRun.Sobolev.CutoffSkew

/-! Smooth compact-cutoff energy identity. The distance-cutoff and rough-data
limits required by Lemma B.5 are not assumed or claimed here. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Set E} {μ : Measure E} [μ.IsAddHaarMeasure]

theorem contDiff_directional {h : E → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ h x v) :=
  (hh.fderiv_right (by simp)).clm_apply contDiff_const

theorem smooth_mixed_comm {h : E → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (v w x : E) :
    fderiv ℝ (fun y => fderiv ℝ h y v) x w =
      fderiv ℝ (fun y => fderiv ℝ h y w) x v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ h) x :=
    (hh.fderiv_right (m := 1) (by simp)).differentiable (by norm_num) x
  rw [fderiv_clm_apply hd (differentiableAt_const v),
    fderiv_clm_apply hd (differentiableAt_const w)]
  simpa using (hh.contDiffAt (x := x)).isSymmSndFDerivAt (by simp) w v

theorem integrable_cutoff_mul (eta : testFunctions Ω) {f : E → ℝ} (hf : Continuous f) :
    Integrable (fun x => (eta : E → ℝ) x * f x) μ :=
  (eta.2.1.continuous.mul hf).integrable_of_hasCompactSupport eta.2.2.1.mul_right

/-- Actual double integration identity with compact cutoff, for a smooth residual
and continuous skew tensor satisfying the distributional relation. -/
theorem cutoff_energy_identity {n : ℕ}
    (eta : testFunctions Ω) (h : E → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (b : Fin n → E) (G : Fin n → Fin n → E → ℝ)
    (hGc : ∀ i j, Continuous (G i j))
    (hG : ∀ x i j, G i j x = -G j i x)
    (hrel : ∀ i, ∀ φ : testFunctions Ω,
      (∫ x, h x * fderiv ℝ (φ : E → ℝ) x (b i) ∂μ) =
        ∑ j, ∫ x, G i j x * fderiv ℝ (φ : E → ℝ) x (b j) ∂μ) :
    (∫ x, (eta : E → ℝ) x ^ 2 * ∑ i, (fderiv ℝ h x (b i)) ^ 2 ∂μ) =
      -2 * ∫ x, (eta : E → ℝ) x *
        ∑ i, ∑ j, fderiv ℝ (eta : E → ℝ) x (b j) * fderiv ℝ h x (b i) * G i j x ∂μ := by
  let A (i : Fin n) (x : E) := (eta : E → ℝ) x ^ 2 * (fderiv ℝ h x (b i)) ^ 2
  let F (i j : Fin n) (x : E) := (eta : E → ℝ) x *
    fderiv ℝ (eta : E → ℝ) x (b j) * fderiv ℝ h x (b i) * G i j x
  let T (i j : Fin n) (x : E) := (eta : E → ℝ) x ^ 2 *
    fderiv ℝ (fun y => fderiv ℝ h y (b i)) x (b j) * G i j x
  have iA (i) : Integrable (A i) μ := by
    convert integrable_cutoff_mul (μ := μ) eta
      (eta.2.1.continuous.mul ((contDiff_directional hh (b i)).continuous.pow 2)) using 1
    ext x; dsimp [A]; ring
  have iF (i j) : Integrable (F i j) μ := by
    convert integrable_cutoff_mul (μ := μ) eta
      (((contDiff_directional eta.2.1 (b j)).continuous.mul
        (contDiff_directional hh (b i)).continuous).mul (hGc i j)) using 1
    ext x; dsimp [F]; ring
  have iT (i j) : Integrable (T i j) μ := by
    convert integrable_cutoff_mul (μ := μ) eta
      ((eta.2.1.continuous.mul
        (contDiff_directional (contDiff_directional hh (b i)) (b j)).continuous).mul
          (hGc i j)) using 1
    ext x; dsimp [T]; ring
  have hi (i : Fin n) : (∫ x, A i x ∂μ) =
      -2 * (∑ j, ∫ x, F i j x ∂μ) - ∑ j, ∫ x, T i j x ∂μ := by
    have hi := cutoff_weak_identity (μ := μ) eta h hh (b i) b (G i) (hrel i)
    change (∫ x, A i x ∂μ) = _ at hi
    have he (j) : (∫ x, G i j x *
        (2 * (eta : E → ℝ) x * fderiv ℝ (eta : E → ℝ) x (b j) * fderiv ℝ h x (b i) +
          (eta : E → ℝ) x ^ 2 * fderiv ℝ (fun y => fderiv ℝ h y (b i)) x (b j)) ∂μ) =
        2 * (∫ x, F i j x ∂μ) + ∫ x, T i j x ∂μ := by
      rw [← integral_const_mul, ← integral_add ((iF i j).const_mul 2) (iT i j)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by dsimp [F, T]; ring)
    simp_rw [he] at hi
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, neg_add_rev] at hi
    linarith
  have hz : (∑ i, ∑ j, ∫ x, T i j x ∂μ) = 0 := by
    simp_rw [← integral_finsetSum Finset.univ (fun j _ => iT _ j)]
    rw [← integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum _ (fun j _ => iT i j))]
    have he : (fun x => ∑ i, ∑ j, T i j x) = fun _ => (0 : ℝ) := by
      funext x
      have hc := HitAndRun.Analysis.symmetric_skew_contraction
        (fun i j => fderiv ℝ (fun y => fderiv ℝ h y (b i)) x (b j))
        (fun i j => G i j x) (fun i j => smooth_mixed_comm hh (b i) (b j) x) (hG x)
      dsimp [T]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      rw [hc, mul_zero]
    rw [he, integral_zero]
  have hs := congrArg (fun f : Fin n → ℝ => ∑ i, f i) (funext hi)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hz, sub_zero] at hs
  have hA : (∫ x, (eta : E → ℝ) x ^ 2 * ∑ i, (fderiv ℝ h x (b i)) ^ 2 ∂μ) =
      ∑ i, ∫ x, A i x ∂μ := by
    rw [← integral_finsetSum Finset.univ (fun i _ => iA i)]
    congr 1; funext x; simp [A, Finset.mul_sum]
  have hF : (∫ x, (eta : E → ℝ) x *
        ∑ i, ∑ j, fderiv ℝ (eta : E → ℝ) x (b j) * fderiv ℝ h x (b i) * G i j x ∂μ) =
      ∑ i, ∑ j, ∫ x, F i j x ∂μ := by
    simp_rw [← integral_finsetSum Finset.univ (fun j _ => iF _ j)]
    rw [← integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum _ (fun j _ => iF i j))]
    congr 1; funext x; simp [F, Finset.mul_sum, mul_assoc]
  rw [hA, hF]
  exact hs
end HitAndRun.Sobolev
