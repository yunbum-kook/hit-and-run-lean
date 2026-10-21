module
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.Sequences
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import CvxBody.External.OAI.KLS.Model

@[expose] public section


/-!
# Existence of a Lipschitz maximizer (Klartag, Lemma 4.1)

For a probability measure `μ` on `ℝⁿ` with `∫ ‖x‖ dμ < ∞` and a measurable `f` with
`|f| ≤ 1` and `∫ f dμ = 0`, there is a 1-Lipschitz `u` with `u 0 = 0` maximizing
`v ↦ ∫ v f dμ` over all 1-Lipschitz `v`.

Proof.  A maximizing sequence `v_k` with `v_k 0 = 0` satisfies `|v_k x| ≤ ‖x‖`.  A countable
dense set `Q` and sequential compactness of a countable product of compact intervals give a
subsequence converging on `Q`; the 1-Lipschitz bound gives convergence everywhere, the limit is
1-Lipschitz, and dominated convergence (`|v_k f| ≤ ‖x‖`) passes to the limit.
-/

open MeasureTheory Filter Topology Set
open OAI.LeanBlast.KLS

namespace CvxBody

section General

variable {E : Type*} [NormedAddCommGroup E]

lemma abs_le_norm_of_lipschitz {v : E → ℝ} (hv : LipschitzWith 1 v) (h0 : v 0 = 0) (x : E) :
    |v x| ≤ ‖x‖ := by
  have := hv.dist_le_mul x 0
  simpa [Real.dist_eq, h0] using this

variable [SecondCountableTopology E] in
/-- Subsequence converging everywhere. -/
lemma exists_subseq_tendsto (v : ℕ → E → ℝ) (hv : ∀ k, LipschitzWith 1 (v k))
    (h0 : ∀ k, v k 0 = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : E → ℝ,
      ∀ x, Tendsto (fun k => v (φ k) x) atTop (𝓝 (u x)) := by
  obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense E
  have : Countable s := hs.to_subtype
  let K : Set (s → ℝ) := Set.pi univ (fun q : s => Icc (-‖(q : E)‖) ‖(q : E)‖)
  have hK : IsCompact K := isCompact_univ_pi (fun q => isCompact_Icc)
  have hmem : ∀ k, (fun q : s => v k (q : E)) ∈ K := by
    intro k q _
    have := abs_le_norm_of_lipschitz (hv k) (h0 k) (q : E)
    exact abs_le.mp this
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hq : ∀ q : s, Tendsto (fun k => v (φ k) (q : E)) atTop (𝓝 (a q)) := fun q =>
    tendsto_pi_nhds.mp hlim q
  have hcauchy : ∀ x, CauchySeq (fun k => v (φ k) x) := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨q, hqs, hxq⟩ := hd.exists_dist_lt x (by linarith : 0 < ε / 3)
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hq ⟨q, hqs⟩).cauchySeq (ε / 3) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 : dist (v (φ m) x) (v (φ m) q) ≤ dist x q := by
      simpa using (hv (φ m)).dist_le_mul x q
    have h2 : dist (v (φ n) q) (v (φ n) x) ≤ dist x q := by
      simpa [dist_comm] using (hv (φ n)).dist_le_mul x q
    have h3 := hN m hm n hn
    have := dist_triangle4 (v (φ m) x) (v (φ m) q) (v (φ n) q) (v (φ n) x)
    simp only at h3
    linarith
  choose u hu using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  exact ⟨φ, hφ, u, hu⟩

end General

section Main

variable {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E]
  [BorelSpace E]

omit [SecondCountableTopology E] in
lemma integrable_lipschitz_mul (μ : Measure E) (hμ : Integrable (fun x : E => ‖x‖) μ)
    {f : E → ℝ} (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ 1) {v : E → ℝ}
    (hv : LipschitzWith 1 v) (h0 : v 0 = 0) :
    Integrable (fun x => v x * f x) μ := by
  refine hμ.mono' ((hv.continuous.measurable.mul hfm).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |v x| * |f x| ≤ ‖x‖ * 1 :=
        mul_le_mul (abs_le_norm_of_lipschitz hv h0 x) (hfb x) (abs_nonneg _) (norm_nonneg _)
    _ = ‖x‖ := mul_one _

theorem exists_lipschitz_maximizer_general (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : E => ‖x‖) μ) {f : E → ℝ} (hfm : Measurable f)
    (hfb : ∀ x, |f x| ≤ 1) (hf0 : ∫ x, f x ∂μ = 0) :
    ∃ u : E → ℝ, LipschitzWith 1 u ∧ u 0 = 0 ∧
      ∀ v : E → ℝ, LipschitzWith 1 v → ∫ x, v x * f x ∂μ ≤ ∫ x, u x * f x ∂μ := by
  have hfi : Integrable f μ :=
    (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hfb x)
  set S : Set ℝ := {r | ∃ v : E → ℝ, LipschitzWith 1 v ∧ v 0 = 0 ∧ r = ∫ x, v x * f x ∂μ}
    with hS
  have hSne : S.Nonempty := ⟨0, fun _ => 0, (LipschitzWith.const 0).weaken zero_le_one, rfl, by simp⟩
  have hSbdd : BddAbove S := by
    refine ⟨∫ x, ‖x‖ ∂μ, ?_⟩
    rintro r ⟨v, hv, h0, rfl⟩
    refine integral_mono (integrable_lipschitz_mul μ hμ hfm hfb hv h0) hμ fun x => ?_
    have := abs_le_norm_of_lipschitz hv h0 x
    calc v x * f x ≤ |v x * f x| := le_abs_self _
      _ = |v x| * |f x| := abs_mul _ _
      _ ≤ ‖x‖ * 1 :=
        mul_le_mul this (hfb x) (abs_nonneg _) (norm_nonneg _)
      _ = ‖x‖ := mul_one _
  obtain ⟨r, -, hr, hrS⟩ := exists_seq_tendsto_sSup hSne hSbdd
  choose v hv h0 hvr using hrS
  obtain ⟨φ, hφ, u, hu⟩ := exists_subseq_tendsto v hv h0
  have hu_lip : LipschitzWith 1 u := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have : Tendsto (fun k => dist (v (φ k) x) (v (φ k) y)) atTop (𝓝 (dist (u x) (u y))) :=
      (hu x).dist (hu y)
    refine le_of_tendsto this (Eventually.of_forall fun k => ?_)
    simpa using (hv (φ k)).dist_le_mul x y
  have hu0 : u 0 = 0 := by
    have : Tendsto (fun k => v (φ k) 0) atTop (𝓝 (u 0)) := hu 0
    simp only [h0] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hdct : Tendsto (fun k => ∫ x, v (φ k) x * f x ∂μ) atTop
      (𝓝 (∫ x, u x * f x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖x‖)
      (fun k => (hv (φ k)).continuous.measurable.mul hfm |>.aestronglyMeasurable) hμ
      (fun k => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs, abs_mul]
      calc |v (φ k) x| * |f x| ≤ ‖x‖ * 1 :=
            mul_le_mul (abs_le_norm_of_lipschitz (hv _) (h0 _) x) (hfb x)
              (abs_nonneg _) (norm_nonneg _)
        _ = ‖x‖ := mul_one _
    · exact (hu x).mul_const (f x)
  have hlim : Tendsto (fun k => ∫ x, v (φ k) x * f x ∂μ) atTop (𝓝 (sSup S)) := by
    have h1 : Tendsto (fun k => r (φ k)) atTop (𝓝 (sSup S)) := hr.comp hφ.tendsto_atTop
    refine h1.congr fun k => ?_
    exact hvr (φ k)
  have heq : ∫ x, u x * f x ∂μ = sSup S := tendsto_nhds_unique hdct hlim
  refine ⟨u, hu_lip, hu0, fun w hw => ?_⟩
  have hw0 : LipschitzWith 1 (fun x => w x - w 0) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simpa [Real.dist_eq] using hw.dist_le_mul x y
  have hint : ∫ x, w x * f x ∂μ = ∫ x, (w x - w 0) * f x ∂μ := by
    have hi1 := integrable_lipschitz_mul μ hμ hfm hfb hw0 (by simp)
    have hi2 : Integrable (fun x => w 0 * f x) μ := hfi.const_mul _
    have : (fun x => w x * f x) = fun x => (w x - w 0) * f x + w 0 * f x := by
      ext x; ring
    rw [this, integral_add hi1 hi2, integral_const_mul, hf0]; ring
  rw [hint, heq]
  exact le_csSup hSbdd ⟨_, hw0, by simp, rfl⟩

end Main

end CvxBody

/-- **Klartag, Lemma 4.1** (existence of a maximizer). -/
theorem exists_lipschitz_maximizer {n : ℕ} (μ : MeasureTheory.Measure (Space n))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hμ : MeasureTheory.Integrable (fun x : Space n => ‖x‖) μ) {f : Space n → ℝ}
    (hfm : Measurable f) (hfb : ∀ x, |f x| ≤ 1) (hf0 : ∫ x, f x ∂μ = 0) :
    ∃ u : Space n → ℝ, LipschitzWith 1 u ∧ u 0 = 0 ∧
      ∀ v : Space n → ℝ, LipschitzWith 1 v → ∫ x, v x * f x ∂μ ≤ ∫ x, u x * f x ∂μ :=
  CvxBody.exists_lipschitz_maximizer_general μ hμ hfm hfb hf0
