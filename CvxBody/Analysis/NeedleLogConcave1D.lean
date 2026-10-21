module
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import CvxBody.External.OAI.KLS.Convexity.LogConcavity

@[expose] public section


open MeasureTheory Set Filter
open OAI.LeanBlast.KLS
open scoped ENNReal Topology

namespace CvxBody.NeedleLC

/-- `shiftSet s X = X + s`, written as the preimage under `t ↦ t - s`. -/
def shiftSet (s : ℝ) (X : Set ℝ) : Set ℝ := (fun t => t - s) ⁻¹' X

theorem measurableSet_shiftSet (s : ℝ) {X : Set ℝ} (hX : MeasurableSet X) :
    MeasurableSet (shiftSet s X) := hX.preimage (measurable_sub_const s)

theorem withDensity_shiftSet (f : ℝ → ℝ≥0∞) (s : ℝ) {X : Set ℝ} (hX : MeasurableSet X) :
    (volume.withDensity f) (shiftSet s X) = ∫⁻ t in X, f (t + s) := by
  rw [withDensity_apply' _ , ← lintegral_indicator (measurableSet_shiftSet s hX),
    ← lintegral_indicator hX]
  rw [← lintegral_sub_right_eq_self (μ := volume) (X.indicator fun t => f (t + s)) s]
  refine lintegral_congr fun τ => ?_
  by_cases h : τ - s ∈ X <;> simp [shiftSet, indicator, h]

theorem tonelli_shift_null (ν : Measure ℝ) [IsFiniteMeasure ν] {Z : Set ℝ} (hZ : MeasurableSet Z)
    (hZ0 : volume Z = 0) : ∀ᵐ s : ℝ, ν (shiftSet s Z) = 0 := by
  have hm : Measurable (fun p : ℝ × ℝ => Z.indicator (fun _ => (1 : ℝ≥0∞)) (p.2 - p.1)) :=
    (measurable_const.indicator hZ).comp (measurable_snd.sub measurable_fst)
  have e : ∀ s, ν (shiftSet s Z) = ∫⁻ t, Z.indicator (fun _ => (1 : ℝ≥0∞)) (t - s) ∂ν := by
    intro s
    rw [← lintegral_indicator_one (measurableSet_shiftSet s hZ)]
    refine lintegral_congr fun t => ?_
    by_cases h : t - s ∈ Z <;> simp [shiftSet, indicator, h]
  have hmeas : Measurable fun s => ν (shiftSet s Z) := by
    simp_rw [e]
    exact hm.lintegral_prod_right'
  have h0 : ∫⁻ s, ν (shiftSet s Z) = 0 := by
    simp_rw [e]
    rw [lintegral_lintegral_swap hm.aemeasurable]
    have : ∀ t : ℝ, ∫⁻ s, Z.indicator (fun _ => (1 : ℝ≥0∞)) (t - s) = 0 := by
      intro t
      rw [lintegral_sub_left_eq_self (μ := volume) (Z.indicator fun _ => (1 : ℝ≥0∞)) t,
        lintegral_indicator_const hZ, hZ0, mul_zero]
    simp [this]
  exact (lintegral_eq_zero_iff hmeas).1 h0


/-- The data of a one-dimensional "shift problem" on a ray: a finite measure `ν` on `ℝ` (the needle
measure), a function `ρ` (the density `ρ` restricted to the ray), an open set `D` where `ρ > 0`, an open
interval `J ⊆ D` carrying `ν`, and a countable family of windows `(α i, β i)` with scales `ε i` and
Jacobian functions `Jac i s t` for which the shift identity holds. -/
structure ShiftData (n : ℕ) (ν : Measure ℝ) (ρ : ℝ → ℝ) (D J : Set ℝ) (ι : Type) where
  ε : ι → ℝ
  α : ι → ℝ
  β : ι → ℝ
  Jac : ι → ℝ → ℝ → ℝ
  ε_pos : ∀ i, 0 < ε i
  α_lt : ∀ i, α i < β i
  jac_meas : ∀ i, Measurable (Function.uncurry (Jac i))
  cover : ∀ t ∈ J, ∃ i, α i < t ∧ t < β i
  shift : ∀ i, ∀ᵐ s ∂(volume : Measure ℝ), |s| < ε i → ∀ I : Set ℝ, MeasurableSet I →
    I ⊆ Icc (α i) (β i) →
      ν (shiftSet s (I ∩ D)) = ∫⁻ t in I ∩ D, ENNReal.ofReal (ρ (t + s) / ρ t * Jac i s t) ∂ν
  jac : ∀ i, ∀ᵐ t ∂ν, t ∈ Icc (α i) (β i) ∩ D → ∃ lam : Fin n → ℝ, (∀ j, |lam j| ≤ 1 / ε i) ∧
    ∀ s, |s| < ε i → Jac i s t = ∏ j, (1 + s * lam j)

section AbsolutelyContinuous

variable {n : ℕ} {ν : Measure ℝ} {ρ : ℝ → ℝ} {D J : Set ℝ} {ι : Type}

theorem ac_window (S : ShiftData n ν ρ D J ι) [IsFiniteMeasure ν] (hD : IsOpen D) (i : ι)
    {Z : Set ℝ} (hZ : MeasurableSet Z) (hZ0 : volume Z = 0) :
    ν (Z ∩ Ioo (S.α i) (S.β i) ∩ D) = 0 := by
  set ε := S.ε i with hε
  set α := S.α i with hα
  set β := S.β i with hβ
  have hε0 : 0 < ε := S.ε_pos i
  have h1 : ∀ᵐ s : ℝ, ν (shiftSet s Z) = 0 := tonelli_shift_null ν hZ hZ0
  have h2 : ∀ᵐ s : ℝ, |(-s)| < ε → ∀ I : Set ℝ, MeasurableSet I → I ⊆ Icc α β →
      ν (shiftSet (-s) (I ∩ D)) =
        ∫⁻ t in I ∩ D, ENNReal.ofReal (ρ (t + -s) / ρ t * S.Jac i (-s) t) ∂ν :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae (S.shift i)
  have h3 : ∀ᵐ s : ℝ, |s| < ε → ν {τ | τ ∈ Z ∧ τ + s ∈ Icc α β ∩ D} = 0 := by
    filter_upwards [h1, h2] with s hs1 hs2 hsε
    have hY : MeasurableSet (shiftSet s Z ∩ Icc α β) :=
      (measurableSet_shiftSet s hZ).inter measurableSet_Icc
    have := hs2 (by rwa [abs_neg]) _ hY inter_subset_right
    have hz : ν (shiftSet s Z ∩ Icc α β ∩ D) = 0 :=
      measure_mono_null (fun x hx => hx.1.1) hs1
    rw [setLIntegral_measure_zero _ _ hz] at this
    have e : {τ | τ ∈ Z ∧ τ + s ∈ Icc α β ∩ D} =
        shiftSet (-s) (shiftSet s Z ∩ Icc α β ∩ D) := by
      ext τ
      simp only [shiftSet, mem_ofPred_eq, mem_preimage, mem_inter_iff, sub_neg_eq_add,
        add_sub_cancel_right]
      tauto
    rw [e]; exact this
  have hMmeas : MeasurableSet {p : ℝ × ℝ | p.1 ∈ Z ∧ p.2 ∈ Ioo (-ε) ε ∧ p.1 + p.2 ∈ Icc α β ∩ D} :=
    (measurable_fst hZ).inter ((measurable_snd measurableSet_Ioo).inter
      ((measurable_fst.add measurable_snd) (measurableSet_Icc.inter hD.measurableSet)))
  classical
  set M : ℝ → ℝ → ℝ≥0∞ := fun τ s =>
    if τ ∈ Z ∧ s ∈ Ioo (-ε) ε ∧ τ + s ∈ Icc α β ∩ D then 1 else 0 with hM
  have hMm : Measurable (Function.uncurry M) :=
    Measurable.ite hMmeas measurable_const measurable_const
  have hs0 : ∫⁻ s, ∫⁻ τ, M τ s ∂ν = 0 := by
    rw [lintegral_congr_ae (g := fun _ => 0)]
    · simp
    filter_upwards [h3] with s hs
    by_cases hsε : |s| < ε
    · have hs' := hs hsε
      have hAm : MeasurableSet {τ | τ ∈ Z ∧ τ + s ∈ Icc α β ∩ D} :=
        hZ.inter ((measurableSet_Icc.inter hD.measurableSet).preimage (measurable_add_const s))
      have hsI : s ∈ Ioo (-ε) ε := ⟨by linarith [(abs_lt.1 hsε).1], (abs_lt.1 hsε).2⟩
      have e : ∀ τ, M τ s = {τ | τ ∈ Z ∧ τ + s ∈ Icc α β ∩ D}.indicator (fun _ => (1 : ℝ≥0∞)) τ := by
        intro τ
        by_cases hτ : τ ∈ Z ∧ τ + s ∈ Icc α β ∩ D
        · rw [indicator_of_mem (by exact hτ), hM]
          exact ite_eq_left ⟨hτ.1, hsI, hτ.2⟩
        · have : ¬ (τ ∈ Z ∧ s ∈ Ioo (-ε) ε ∧ τ + s ∈ Icc α β ∩ D) := fun h => hτ ⟨h.1, h.2.2⟩
          rw [indicator_of_notMem (by exact hτ), hM]
          exact ite_eq_right this
      simp_rw [e]
      rw [lintegral_indicator_const hAm, hs', mul_zero]
    · have : ∀ τ, M τ s = 0 := by
        intro τ
        have hsI : s ∉ Ioo (-ε) ε := fun h => hsε (abs_lt.2 ⟨h.1, h.2⟩)
        rw [hM]
        exact ite_eq_right (fun h => hsI h.2.1)
      simp [this]
  have hswap : ∫⁻ τ, ∫⁻ s, M τ s ∂volume ∂ν = 0 := by
    rw [← lintegral_lintegral_swap (μ := (volume : Measure ℝ)) (ν := ν) (f := fun s τ => M τ s)]
    · exact hs0
    · exact (hMm.comp measurable_swap).aemeasurable
  have hae : ∀ᵐ τ ∂ν, ∫⁻ s, M τ s = 0 :=
    (lintegral_eq_zero_iff hMm.lintegral_prod_right').1 hswap
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hae] with τ hτ hmem
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (isOpen_Ioo.inter hD) τ ⟨hmem.1.2, hmem.2⟩
  set δ' := min δ ε with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ hε0
  have hpos : (0 : ℝ≥0∞) < ∫⁻ s, M τ s := by
    calc (0 : ℝ≥0∞) < volume (Ioo (-δ') δ') := by
          rw [Real.volume_Ioo]; simpa using hδ'0
      _ = ∫⁻ s in Ioo (-δ') δ', (1 : ℝ≥0∞) := by simp
      _ = ∫⁻ s in Ioo (-δ') δ', M τ s := by
          refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
          have hsδ : |s| < δ' := abs_lt.2 ⟨hs.1, hs.2⟩
          have h1 : |s| < δ := hsδ.trans_le (min_le_left _ _)
          have h2 : |s| < ε := hsδ.trans_le (min_le_right _ _)
          have hmem' : τ + s ∈ Ioo α β ∩ D := hball (by
            rw [Metric.mem_ball, Real.dist_eq]; simpa using h1)
          have hsI : s ∈ Ioo (-ε) ε := ⟨(abs_lt.1 h2).1, (abs_lt.1 h2).2⟩
          have : τ ∈ Z ∧ s ∈ Ioo (-ε) ε ∧ τ + s ∈ Icc α β ∩ D :=
            ⟨hmem.1.1, hsI, Ioo_subset_Icc_self hmem'.1, hmem'.2⟩
          rw [hM]
          exact (ite_eq_left this).symm
      _ ≤ ∫⁻ s, M τ s := setLIntegral_le_lintegral _ _
  rw [hτ] at hpos
  exact lt_irrefl _ hpos

theorem absolutelyContinuous (S : ShiftData n ν ρ D J ι) [IsFiniteMeasure ν] [Countable ι]
    (hD : IsOpen D) (hJD : J ⊆ D) (hνJ : ν Jᶜ = 0) : ν ≪ volume := by
  intro Z hZ0
  set Z' := toMeasurable volume Z with hZ'
  have hZ'0 : volume Z' = 0 := by rwa [hZ', measure_toMeasurable]
  refine measure_mono_null (subset_toMeasurable volume Z) ?_
  rw [← hZ']
  have hcov : Z' ⊆ Jᶜ ∪ ⋃ i, (Z' ∩ Ioo (S.α i) (S.β i) ∩ D) := by
    intro t ht
    by_cases hJt : t ∈ J
    · obtain ⟨i, hi1, hi2⟩ := S.cover t hJt
      exact Or.inr (mem_iUnion.2 ⟨i, ⟨ht, ⟨hi1, hi2⟩⟩, hJD hJt⟩)
    · exact Or.inl hJt
  exact measure_mono_null hcov (measure_union_null hνJ
    (measure_iUnion_null fun i => ac_window S hD i (measurableSet_toMeasurable _ _) hZ'0))

end AbsolutelyContinuous

section Density

variable {n : ℕ} {ν : Measure ℝ} {ρ : ℝ → ℝ} {D J : Set ℝ} {ι : Type}

/-- The real-valued Radon-Nikodym density of `ν` with respect to Lebesgue measure. -/
noncomputable def dens (ν : Measure ℝ) (t : ℝ) : ℝ := (ν.rnDeriv volume t).toReal

theorem measurable_dens : Measurable (dens ν) := (Measure.measurable_rnDeriv _ _).ennreal_toReal

theorem dens_nonneg (t : ℝ) : 0 ≤ dens ν t := ENNReal.toReal_nonneg

theorem withDensity_dens [IsFiniteMeasure ν] (hac : ν ≪ volume) :
    volume.withDensity (fun t => ENNReal.ofReal (dens ν t)) = ν := by
  have : ∀ᵐ t, ENNReal.ofReal (dens ν t) = ν.rnDeriv volume t := by
    filter_upwards [Measure.rnDeriv_lt_top ν volume] with t ht
    simp [dens, ENNReal.ofReal_toReal ht.ne]
  rw [withDensity_congr_ae this, Measure.withDensity_rnDeriv_eq _ _ hac]

theorem setLIntegral_eq_dens [IsFiniteMeasure ν] (hac : ν ≪ volume) {G : ℝ → ℝ≥0∞}
    (hG : Measurable G) {X : Set ℝ} (hX : MeasurableSet X) :
    ∫⁻ t in X, G t ∂ν = ∫⁻ t in X, G t * ENNReal.ofReal (dens ν t) := by
  conv_lhs => rw [← withDensity_dens hac]
  rw [setLIntegral_withDensity_eq_setLIntegral_mul _ measurable_dens.ennreal_ofReal hG hX]
  refine setLIntegral_congr_fun hX fun t _ => ?_
  simp only [Pi.mul_apply]
  exact mul_comm _ _

theorem measure_eq_dens [IsFiniteMeasure ν] (hac : ν ≪ volume) {X : Set ℝ}
    (hX : MeasurableSet X) : ν X = ∫⁻ t in X, ENNReal.ofReal (dens ν t) := by
  conv_lhs => rw [← withDensity_dens hac]
  exact withDensity_apply _ hX

theorem measure_shiftSet_dens [IsFiniteMeasure ν] (hac : ν ≪ volume) (s : ℝ) {X : Set ℝ}
    (hX : MeasurableSet X) :
    ν (shiftSet s X) = ∫⁻ t in X, ENNReal.ofReal (dens ν (t + s)) := by
  conv_lhs => rw [← withDensity_dens hac]
  exact withDensity_shiftSet (fun t => ENNReal.ofReal (dens ν t)) s hX

/-- **Shift relation for the density, a.e. in `s`.** -/
theorem shift_density_eq (S : ShiftData n ν ρ D J ι) [IsFiniteMeasure ν] (hD : IsOpen D)
    (hρm : Measurable ρ) (hac : ν ≪ volume) (i : ι) :
    ∀ᵐ s ∂(volume : Measure ℝ), |s| < S.ε i → ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ Icc (S.α i) (S.β i) ∩ D →
        ENNReal.ofReal (dens ν (t + s)) =
          ENNReal.ofReal (ρ (t + s) / ρ t * S.Jac i s t) * ENNReal.ofReal (dens ν t) := by
  filter_upwards [S.shift i] with s hs hsε
  have hs := hs hsε
  set E := Icc (S.α i) (S.β i) ∩ D with hE
  have hEm : MeasurableSet E := measurableSet_Icc.inter hD.measurableSet
  rw [← ae_restrict_iff' hEm]
  have hJs : Measurable (S.Jac i s) := (S.jac_meas i).comp (measurable_const.prodMk measurable_id)
  have hGm : Measurable fun t => ρ (t + s) / ρ t * S.Jac i s t :=
    ((hρm.comp (measurable_add_const s)).div hρm).mul hJs
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (μ := volume.restrict E)
    ((measurable_dens.comp (measurable_add_const s)).ennreal_ofReal)
    (hGm.ennreal_ofReal.mul measurable_dens.ennreal_ofReal) fun K hK _ => ?_
  rw [Measure.restrict_restrict hK]
  have hI : MeasurableSet (K ∩ Icc (S.α i) (S.β i)) := hK.inter measurableSet_Icc
  have h1 := hs (K ∩ Icc (S.α i) (S.β i)) hI inter_subset_right
  have e : K ∩ Icc (S.α i) (S.β i) ∩ D = K ∩ E := by rw [hE, inter_assoc]
  rw [e] at h1
  rw [← measure_shiftSet_dens hac s (hK.inter hEm), h1,
    setLIntegral_eq_dens hac hGm.ennreal_ofReal (hK.inter hEm)]

/-- `t₀` is a good base point in window `i`: it lies in the window, the density is positive there,
the shift relation holds at `t₀` for almost every `s`, and the Jacobian at `t₀` factors. -/
def Good (S : ShiftData n ν ρ D J ι) (i : ι) (t₀ : ℝ) : Prop :=
  t₀ ∈ Ioo (S.α i) (S.β i) ∩ D ∧ 0 < dens ν t₀ ∧
  (∀ᵐ s ∂(volume : Measure ℝ), |s| < S.ε i →
    ENNReal.ofReal (dens ν (t₀ + s)) =
      ENNReal.ofReal (ρ (t₀ + s) / ρ t₀ * S.Jac i s t₀) * ENNReal.ofReal (dens ν t₀)) ∧
  ∃ lam : Fin n → ℝ, (∀ j, |lam j| ≤ 1 / S.ε i) ∧
    ∀ s, |s| < S.ε i → S.Jac i s t₀ = ∏ j, (1 + s * lam j)

theorem ae_good (S : ShiftData n ν ρ D J ι) [IsFiniteMeasure ν] (hD : IsOpen D)
    (hρm : Measurable ρ) (hac : ν ≪ volume) (i : ι) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo (S.α i) (S.β i) ∩ D → 0 < dens ν t → Good S i t := by
  have hA := shift_density_eq S hD hρm hac i
  have hB := S.jac i
  have hae : ae ν = ae (volume.withDensity fun t => ENNReal.ofReal (dens ν t)) := by
    rw [withDensity_dens hac]
  rw [hae, ae_withDensity_iff measurable_dens.ennreal_ofReal] at hB
  have hA' : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ s ∂(volume : Measure ℝ), (|s| < S.ε i →
      t ∈ Icc (S.α i) (S.β i) ∩ D → ENNReal.ofReal (dens ν (t + s)) =
        ENNReal.ofReal (ρ (t + s) / ρ t * S.Jac i s t) * ENNReal.ofReal (dens ν t)) := by
    rw [← Measure.ae_ae_comm]
    · filter_upwards [hA] with s hs
      by_cases hsε : |s| < S.ε i
      · filter_upwards [hs hsε] with t ht
        exact fun _ h => ht h
      · exact Filter.Eventually.of_forall fun t h => absurd h hsε
    · have hEm : MeasurableSet (Icc (S.α i) (S.β i) ∩ D) := measurableSet_Icc.inter hD.measurableSet
      have hGm : Measurable fun p : ℝ × ℝ => ρ (p.2 + p.1) / ρ p.2 * S.Jac i p.1 p.2 :=
        ((hρm.comp (measurable_snd.add measurable_fst)).div (hρm.comp measurable_snd)).mul
          (S.jac_meas i)
      have h1 : MeasurableSet {p : ℝ × ℝ | |p.1| < S.ε i} :=
        measurableSet_lt measurable_fst.abs measurable_const
      have h2 : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Icc (S.α i) (S.β i) ∩ D} := measurable_snd hEm
      have h3 : MeasurableSet {p : ℝ × ℝ | ENNReal.ofReal (dens ν (p.2 + p.1)) =
          ENNReal.ofReal (ρ (p.2 + p.1) / ρ p.2 * S.Jac i p.1 p.2) * ENNReal.ofReal (dens ν p.2)} :=
        measurableSet_eq_fun
          (measurable_dens.comp (measurable_snd.add measurable_fst)).ennreal_ofReal
          (hGm.ennreal_ofReal.mul (measurable_dens.comp measurable_snd).ennreal_ofReal)
      exact h1.imp (h2.imp h3)
  filter_upwards [hA', hB] with t ht1 ht2 htE htpos
  refine ⟨⟨htE.1, htE.2⟩, htpos, ?_, ?_⟩
  · filter_upwards [ht1] with s hs hsε
    exact hs hsε ⟨Ioo_subset_Icc_self htE.1, htE.2⟩
  · exact ht2 (by simpa [ENNReal.ofReal_eq_zero, not_le] using htpos)
      ⟨Ioo_subset_Icc_self htE.1, htE.2⟩

theorem one_add_mul_pos {ε s l : ℝ} (hε : 0 < ε) (hl : |l| ≤ 1 / ε) (hs : |s| < ε) :
    0 < 1 + s * l := by
  have h1 : |s * l| < 1 := by
    rw [abs_mul]
    calc |s| * |l| ≤ |s| * (1 / ε) := mul_le_mul_of_nonneg_left hl (abs_nonneg s)
      _ < ε * (1 / ε) := by gcongr
      _ = 1 := by field_simp
  linarith [(abs_lt.1 h1).1]

theorem prod_pos_of_abs_lt {m : ℕ} {ε : ℝ} (hε : 0 < ε) {lam : Fin m → ℝ}
    (hl : ∀ j, |lam j| ≤ 1 / ε) {s : ℝ} (hs : |s| < ε) : 0 < ∏ j, (1 + s * lam j) :=
  Finset.prod_pos fun j _ => one_add_mul_pos hε (hl j) hs

/-- **Frozen formula.**  At a good base point `t₀` of window `i`, the density is, near `t₀`,
`ρ(t) · c · ∏_j (1 + (t - t₀) λ_j)` with `c = h(t₀)/ρ(t₀)`. -/
theorem frozen_formula (S : ShiftData n ν ρ D J ι) (hρ0 : ∀ t, 0 ≤ ρ t) (hρD : ∀ t ∈ D, 0 < ρ t)
    {i : ι} {t₀ : ℝ} (hg : Good S i t₀) :
    ∃ lam : Fin n → ℝ, (∀ j, |lam j| ≤ 1 / S.ε i) ∧
      ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo (t₀ - S.ε i) (t₀ + S.ε i) →
        dens ν t = ρ t * (dens ν t₀ / ρ t₀ * ∏ j, (1 + (t - t₀) * lam j)) := by
  obtain ⟨⟨_, ht₀D⟩, hpos, hae, lam, hlam, hJ⟩ := hg
  refine ⟨lam, hlam, ?_⟩
  have hε := S.ε_pos i
  have hae' := (measurePreserving_sub_right (volume : Measure ℝ) t₀).quasiMeasurePreserving.ae hae
  filter_upwards [hae'] with t ht htI
  have hts : |t - t₀| < S.ε i := abs_lt.2 ⟨by linarith [htI.1], by linarith [htI.2]⟩
  have h1 := ht hts
  rw [add_sub_cancel, hJ _ hts] at h1
  have hρ₀ := hρD t₀ ht₀D
  have hP := prod_pos_of_abs_lt hε hlam hts
  have hnn : 0 ≤ ρ t / ρ t₀ * ∏ j, (1 + (t - t₀) * lam j) :=
    mul_nonneg (div_nonneg (hρ0 t) hρ₀.le) hP.le
  rw [← ENNReal.ofReal_mul hnn, ENNReal.ofReal_eq_ofReal_iff (dens_nonneg t)
    (mul_nonneg hnn (dens_nonneg t₀))] at h1
  rw [h1]
  field_simp

end Density

section Gluing

open Polynomial

/-- The polynomial `c * ∏_j (1 + λ_j (X - t₀))`. -/
noncomputable def qpol {m : ℕ} (c : ℝ) (lam : Fin m → ℝ) (t₀ : ℝ) : ℝ[X] :=
  C c * ∏ j, (1 + C (lam j) * (X - C t₀))

theorem eval_qpol {m : ℕ} (c : ℝ) (lam : Fin m → ℝ) (t₀ t : ℝ) :
    (qpol c lam t₀).eval t = c * ∏ j, (1 + (t - t₀) * lam j) := by
  simp [qpol, eval_prod, mul_comm]

theorem poly_eq_of_ae_eq {O : Set ℝ} (hOm : MeasurableSet O) (hO : 0 < volume O) {f g : ℝ[X]}
    (hfg : ∀ᵐ τ ∂(volume.restrict O), f.eval τ = g.eval τ) : f = g := by
  refine Polynomial.eq_of_infinite_eval_eq f g ?_
  intro hfin
  have hnull : volume {x | f.eval x = g.eval x} = 0 := hfin.measure_zero _
  rw [ae_restrict_iff' hOm] at hfg
  have h2 : volume {x | ¬ (x ∈ O → f.eval x = g.eval x)} = 0 := ae_iff.1 hfg
  have : O ⊆ {x | f.eval x = g.eval x} ∪ {x | ¬ (x ∈ O → f.eval x = g.eval x)} := by
    intro x hx
    by_cases h : f.eval x = g.eval x
    · exact Or.inl h
    · exact Or.inr fun h' => h (h' hx)
  have := measure_mono_null this (measure_union_null hnull h2)
  exact absurd this hO.ne'

variable {n : ℕ} {ν : Measure ℝ} {ρ : ℝ → ℝ} {D J : Set ℝ} {ι : Type}

/-- **Extension of the explicit formula.**  If `dens = ρ · q` a.e. on an open set `W ⊆ D` containing
a good base point `t₀`, then the polynomial `q` is positive, and `dens = ρ · q` a.e., on the whole
window `(t₀ - ε, t₀ + ε)` of `t₀` (inside `D`). -/
theorem extend_formula (S : ShiftData n ν ρ D J ι) (hD : IsOpen D) (hρ0 : ∀ t, 0 ≤ ρ t)
    (hρD : ∀ t ∈ D, 0 < ρ t) {i : ι} {t₀ : ℝ} (hg : Good S i t₀) {W : Set ℝ} (hW : IsOpen W)
    (ht₀W : t₀ ∈ W) (hWD : W ⊆ D) (q : ℝ[X])
    (hq : ∀ᵐ τ ∂(volume.restrict W), dens ν τ = ρ τ * q.eval τ) :
    (∀ τ ∈ Ioo (t₀ - S.ε i) (t₀ + S.ε i), 0 < q.eval τ) ∧
      ∀ᵐ τ ∂(volume.restrict (Ioo (t₀ - S.ε i) (t₀ + S.ε i) ∩ D)),
        dens ν τ = ρ τ * q.eval τ := by
  obtain ⟨lam, hlam, hform⟩ := frozen_formula S hρ0 hρD hg
  have hε := S.ε_pos i
  have ht₀D : t₀ ∈ D := hg.1.2
  set c₀ := dens ν t₀ / ρ t₀ with hc₀
  have hc₀pos : 0 < c₀ := div_pos hg.2.1 (hρD t₀ ht₀D)
  set O := W ∩ Ioo (t₀ - S.ε i) (t₀ + S.ε i) with hO
  have hOo : IsOpen O := hW.inter isOpen_Ioo
  have ht₀O : t₀ ∈ O := ⟨ht₀W, by constructor <;> linarith⟩
  have hOpos : 0 < volume O := hOo.measure_pos _ ⟨t₀, ht₀O⟩
  have hqeq : q = qpol c₀ lam t₀ := by
    refine poly_eq_of_ae_eq hOo.measurableSet hOpos ?_
    have h1 : ∀ᵐ τ ∂(volume.restrict O), dens ν τ = ρ τ * q.eval τ :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hq
    have h2 : ∀ᵐ τ ∂(volume.restrict O),
        dens ν τ = ρ τ * (c₀ * ∏ j, (1 + (τ - t₀) * lam j)) := by
      rw [ae_restrict_iff' hOo.measurableSet]
      filter_upwards [hform] with τ hτ hτO using hτ hτO.2
    filter_upwards [h1, h2, ae_restrict_mem hOo.measurableSet] with τ a b hτO
    rw [eval_qpol]
    exact mul_left_cancel₀ (hρD τ (hWD hτO.1)).ne' (a.symm.trans b)
  refine ⟨fun τ hτ => ?_, ?_⟩
  · rw [hqeq, eval_qpol]
    have hts : |τ - t₀| < S.ε i := abs_lt.2 ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact mul_pos hc₀pos (prod_pos_of_abs_lt hε hlam hts)
  · rw [ae_restrict_iff' (measurableSet_Ioo.inter hD.measurableSet)]
    filter_upwards [hform] with τ hτ hτI
    rw [hqeq, eval_qpol]
    exact hτ hτI.1

/-- The set of points of `J` near which `dens = ρ · q` a.e. with `q > 0`. -/
def GlueSet (ν : Measure ℝ) (ρ : ℝ → ℝ) (J : Set ℝ) (q : ℝ[X]) : Set ℝ :=
  {t | t ∈ J ∧ ∃ δ > 0, (∀ τ ∈ Ioo (t - δ) (t + δ) ∩ J, 0 < q.eval τ) ∧
    ∀ᵐ τ ∂(volume.restrict (Ioo (t - δ) (t + δ) ∩ J)), dens ν τ = ρ τ * q.eval τ}

theorem mem_glueSet_of_subset {q : ℝ[X]} {t₁ a b : ℝ} (ht₁J : t₁ ∈ J) (ht₁ : t₁ ∈ Ioo a b)
    (hpos : ∀ τ ∈ Ioo a b ∩ J, 0 < q.eval τ)
    (hae : ∀ᵐ τ ∂(volume.restrict (Ioo a b ∩ J)), dens ν τ = ρ τ * q.eval τ) :
    t₁ ∈ GlueSet ν ρ J q := by
  set δ := min (t₁ - a) (b - t₁) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith [ht₁.1]) (by linarith [ht₁.2])
  have hsub : Ioo (t₁ - δ) (t₁ + δ) ∩ J ⊆ Ioo a b ∩ J := by
    rintro τ ⟨⟨h1, h2⟩, hτJ⟩
    refine ⟨⟨?_, ?_⟩, hτJ⟩
    · have := min_le_left (t₁ - a) (b - t₁); linarith
    · have := min_le_right (t₁ - a) (b - t₁); linarith
  exact ⟨ht₁J, δ, hδ0, fun τ hτ => hpos τ (hsub hτ),
    ae_restrict_of_ae_restrict_of_subset hsub hae⟩

theorem isOpen_glueSet (hJo : IsOpen J) (q : ℝ[X]) : IsOpen (GlueSet ν ρ J q) := by
  rw [isOpen_iff_mem_nhds]
  rintro t ⟨htJ, δ, hδ, hpos, hae⟩
  have hnhds : Ioo (t - δ) (t + δ) ∩ J ∈ 𝓝 t :=
    inter_mem (Ioo_mem_nhds (by linarith) (by linarith)) (hJo.mem_nhds htJ)
  filter_upwards [hnhds] with t' ht'
  exact mem_glueSet_of_subset ht'.2 ht'.1 hpos hae

/-- **Connectivity (gluing).**  If the explicit formula `dens = ρ · q` (with `q > 0`) holds near one
point of the open interval `J`, it holds near every point of `J`. -/
theorem glue_subset (S : ShiftData n ν ρ D J ι) [IsFiniteMeasure ν] (hD : IsOpen D)
    (hρm : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρD : ∀ t ∈ D, 0 < ρ t) (hac : ν ≪ volume)
    (hJo : IsOpen J) (hJc : Convex ℝ J) (hJD : J ⊆ D) (q : ℝ[X])
    (hne : (GlueSet ν ρ J q).Nonempty) : J ⊆ GlueSet ν ρ J q := by
  refine hJc.isPreconnected.subset_of_closure_inter_subset (isOpen_glueSet hJo q) ?_ ?_
  · obtain ⟨t, ht⟩ := hne
    exact ⟨t, ht.1, ht⟩
  rintro t₁ ⟨ht₁cl, ht₁J⟩
  obtain ⟨i, hα, hβ⟩ := S.cover t₁ ht₁J
  have hε := S.ε_pos i
  obtain ⟨δ₁', hδ₁', hball⟩ := Metric.isOpen_iff.1 (isOpen_Ioo.inter hJo) t₁ ⟨⟨hα, hβ⟩, ht₁J⟩
  set δ₁ := min δ₁' (S.ε i) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min hδ₁' hε
  have hδ₁ε : δ₁ ≤ S.ε i := min_le_right _ _
  have hsub1 : Ioo (t₁ - δ₁) (t₁ + δ₁) ⊆ Ioo (S.α i) (S.β i) ∩ J := by
    intro τ hτ
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    have := min_le_left δ₁' (S.ε i)
    constructor <;> linarith [hτ.1, hτ.2]
  obtain ⟨t₂, ht₂1, ht₂V⟩ := mem_closure_iff.1 ht₁cl (Ioo (t₁ - δ₁) (t₁ + δ₁)) isOpen_Ioo
    ⟨by linarith, by linarith⟩
  obtain ⟨ht₂J, δ₂, hδ₂, hpos₂, hae₂⟩ := ht₂V
  set W := Ioo (t₂ - δ₂) (t₂ + δ₂) ∩ Ioo (t₁ - δ₁) (t₁ + δ₁) with hW
  have hWo : IsOpen W := isOpen_Ioo.inter isOpen_Ioo
  have ht₂W : t₂ ∈ W := ⟨⟨by linarith, by linarith⟩, ht₂1⟩
  have hWsub : W ⊆ Ioo (t₂ - δ₂) (t₂ + δ₂) ∩ J := fun τ hτ => ⟨hτ.1, (hsub1 hτ.2).2⟩
  have hWJ : W ⊆ J := fun τ hτ => (hsub1 hτ.2).2
  have hWD : W ⊆ D := fun τ hτ => hJD (hWJ hτ)
  have haeW : ∀ᵐ τ ∂(volume.restrict W), dens ν τ = ρ τ * q.eval τ :=
    ae_restrict_of_ae_restrict_of_subset hWsub hae₂
  have hWpos : 0 < volume W := hWo.measure_pos _ ⟨t₂, ht₂W⟩
  have hgood : ∀ᵐ τ ∂(volume.restrict W), Good S i τ := by
    filter_upwards [ae_restrict_of_ae (ae_good S hD hρm hac i), haeW,
      ae_restrict_mem hWo.measurableSet] with τ h1 h2 h3
    refine h1 ⟨(hsub1 h3.2).1, hWD h3⟩ ?_
    rw [h2]
    exact mul_pos (hρD τ (hWD h3)) (hpos₂ τ (hWsub h3))
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ ∈ W, Good S i τ₀ := by
    by_contra hcon
    push Not at hcon
    have h0 : volume {τ | ¬ (τ ∈ W → Good S i τ)} = 0 := by
      have := (ae_restrict_iff' hWo.measurableSet).1 hgood
      exact ae_iff.1 this
    have : W ⊆ {τ | ¬ (τ ∈ W → Good S i τ)} := fun τ hτ h => hcon τ hτ (h hτ)
    exact hWpos.ne' (measure_mono_null this h0)
  obtain ⟨hτ₀W, hg⟩ := hτ₀
  obtain ⟨hpos', hae'⟩ := extend_formula S hD hρ0 hρD hg hWo hτ₀W hWD q haeW
  have hτ₀1 : τ₀ ∈ Ioo (t₁ - δ₁) (t₁ + δ₁) := hτ₀W.2
  have ht₁I : t₁ ∈ Ioo (τ₀ - S.ε i) (τ₀ + S.ε i) := by
    constructor <;> linarith [hτ₀1.1, hτ₀1.2]
  have hsub : Ioo (τ₀ - S.ε i) (τ₀ + S.ε i) ∩ J ⊆ Ioo (τ₀ - S.ε i) (τ₀ + S.ε i) ∩ D :=
    fun τ hτ => ⟨hτ.1, hJD hτ.2⟩
  exact mem_glueSet_of_subset ht₁J ht₁I (fun τ hτ => hpos' τ hτ.1)
    (ae_restrict_of_ae_restrict_of_subset hsub hae')

theorem ae_restrict_of_local {J : Set ℝ} {p : ℝ → Prop}
    (h : ∀ t ∈ J, ∃ δ > 0, ∀ᵐ τ ∂(volume.restrict (Ioo (t - δ) (t + δ) ∩ J)), p τ) :
    ∀ᵐ τ ∂(volume.restrict J), p τ := by
  choose! δ hδ hp using h
  obtain ⟨T, hTJ, hT, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun t => Ioo (t - δ t) (t + δ t) ∩ J) (s := J) (fun t ht =>
      inter_mem (mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith [hδ t ht])
        (by linarith [hδ t ht]))) self_mem_nhdsWithin)
  exact ae_restrict_of_ae_restrict_of_subset hcov
    ((ae_restrict_biUnion_iff _ hT p).2 fun t ht => hp t (hTJ ht))

theorem exists_good_base (S : ShiftData n ν ρ D J ι) [IsProbabilityMeasure ν] [Countable ι]
    (hD : IsOpen D) (hρm : Measurable ρ) (hac : ν ≪ volume) (hJo : IsOpen J) (hJD : J ⊆ D)
    (hνJ : ν Jᶜ = 0) : ∃ i t₀, Good S i t₀ ∧ t₀ ∈ J := by
  have hJ1 : ν J = 1 := (prob_compl_eq_zero_iff hJo.measurableSet).1 hνJ
  have hex : ∃ i, ν (Ioo (S.α i) (S.β i) ∩ J) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : ν J = 0 := by
      refine measure_mono_null (fun t ht => ?_) (measure_iUnion_null hcon)
      obtain ⟨i, hi1, hi2⟩ := S.cover t ht
      exact mem_iUnion.2 ⟨i, ⟨hi1, hi2⟩, ht⟩
    rw [hJ1] at this
    exact one_ne_zero this
  obtain ⟨i, hi⟩ := hex
  set A := Ioo (S.α i) (S.β i) ∩ J with hA
  have hAm : MeasurableSet A := measurableSet_Ioo.inter hJo.measurableSet
  have hP : MeasurableSet {t | 0 < dens ν t} := measurableSet_lt measurable_const measurable_dens
  have hνA : ν (A ∩ {t | 0 < dens ν t}) ≠ 0 := by
    intro h0
    apply hi
    refine nonpos_iff_eq_zero.1 ?_
    have h1 : ν (A ∩ {t | 0 < dens ν t}ᶜ) = 0 := by
      rw [measure_eq_dens hac (hAm.inter hP.compl)]
      refine setLIntegral_eq_zero (hAm.inter hP.compl) fun t ht => ?_
      have : dens ν t ≤ 0 := not_lt.1 ht.2
      simp [ENNReal.ofReal_eq_zero, this]
    calc ν A ≤ ν (A ∩ {t | 0 < dens ν t}) + ν (A ∩ {t | 0 < dens ν t}ᶜ) := by
          refine (measure_mono ?_).trans (measure_union_le _ _)
          intro t ht
          by_cases h : 0 < dens ν t
          · exact Or.inl ⟨ht, h⟩
          · exact Or.inr ⟨ht, h⟩
      _ = 0 := by rw [h0, h1, add_zero]
  have hvol : volume (A ∩ {t | 0 < dens ν t}) ≠ 0 := fun h => hνA (hac h)
  have hg := ae_good S hD hρm hac i
  obtain ⟨t₀, ht₀A, ht₀P⟩ : ∃ t₀ ∈ A, 0 < dens ν t₀ ∧ Good S i t₀ := by
    by_contra hcon
    push Not at hcon
    have h0 : volume {t | ¬ (t ∈ Ioo (S.α i) (S.β i) ∩ D → 0 < dens ν t → Good S i t)} = 0 :=
      ae_iff.1 hg
    refine hvol (measure_mono_null (fun t ht => ?_) h0)
    intro hcont
    exact hcon t ht.1 ht.2 (hcont ⟨ht.1.1, hJD ht.1.2⟩ ht.2)
  exact ⟨i, t₀, ht₀P.2, ht₀A.2⟩

/-- **Global explicit formula.**  There are `c > 0`, real numbers `λ_j` and `t₀ ∈ J` such that every
factor `1 + (t - t₀) λ_j` is positive on `J` and the density is `ρ · c · ∏_j (1 + (t - t₀) λ_j)`
almost everywhere on `J`. -/
theorem global_formula (S : ShiftData n ν ρ D J ι) [IsProbabilityMeasure ν] [Countable ι]
    (hD : IsOpen D) (hρm : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρD : ∀ t ∈ D, 0 < ρ t)
    (hac : ν ≪ volume) (hJo : IsOpen J) (hJc : Convex ℝ J) (hJD : J ⊆ D) (hνJ : ν Jᶜ = 0) :
    ∃ (c : ℝ) (lam : Fin n → ℝ) (t₀ : ℝ), 0 < c ∧ t₀ ∈ J ∧
      (∀ t ∈ J, ∀ j, 0 < 1 + (t - t₀) * lam j) ∧
      ∀ᵐ τ ∂(volume.restrict J), dens ν τ = ρ τ * (c * ∏ j, (1 + (τ - t₀) * lam j)) := by
  obtain ⟨i, t₀, hg, ht₀J⟩ := exists_good_base S hD hρm hac hJo hJD hνJ
  obtain ⟨lam, hlam, hform⟩ := frozen_formula S hρ0 hρD hg
  have hε := S.ε_pos i
  have hc : 0 < dens ν t₀ / ρ t₀ := div_pos hg.2.1 (hρD t₀ hg.1.2)
  set c := dens ν t₀ / ρ t₀ with hcdef
  set q := qpol c lam t₀ with hq
  have h0 : t₀ ∈ GlueSet ν ρ J q := by
    refine mem_glueSet_of_subset ht₀J (a := t₀ - S.ε i) (b := t₀ + S.ε i)
      ⟨by linarith, by linarith⟩ (fun τ hτ => ?_) ?_
    · rw [hq, eval_qpol]
      have hts : |τ - t₀| < S.ε i := abs_lt.2 ⟨by linarith [hτ.1.1], by linarith [hτ.1.2]⟩
      exact mul_pos hc (prod_pos_of_abs_lt hε hlam hts)
    · rw [ae_restrict_iff' (measurableSet_Ioo.inter hJo.measurableSet)]
      filter_upwards [hform] with τ hτ hτm
      rw [hq, eval_qpol]
      exact hτ hτm.1
  have hall := glue_subset S hD hρm hρ0 hρD hac hJo hJc hJD q ⟨t₀, h0⟩
  have hqpos : ∀ t ∈ J, 0 < q.eval t := by
    intro t ht
    obtain ⟨_, δ, hδ, hpos, _⟩ := hall ht
    exact hpos t ⟨⟨by linarith, by linarith⟩, ht⟩
  refine ⟨c, lam, t₀, hc, ht₀J, ?_, ?_⟩
  · intro t ht j
    by_contra hneg
    push Not at hneg
    have hx : (t - t₀) * lam j ≤ -1 := by linarith
    set x := (t - t₀) * lam j with hxdef
    have hxneg : x < 0 := by linarith
    set θ := -1 / x with hθ
    have hθ0 : 0 < θ := by rw [hθ]; exact div_pos_of_neg_of_neg (by norm_num) hxneg
    have hθ1 : θ ≤ 1 := by
      rw [hθ, div_le_one_of_neg hxneg]; linarith
    have hr : t₀ + θ • (t - t₀) ∈ J := hJc.add_smul_sub_mem ht₀J ht ⟨hθ0.le, hθ1⟩
    have hfac : 1 + (t₀ + θ • (t - t₀) - t₀) * lam j = 0 := by
      have : (t₀ + θ • (t - t₀) - t₀) * lam j = θ * x := by
        rw [hxdef]; simp only [smul_eq_mul]; ring
      rw [this, hθ]
      have hx0 : x ≠ 0 := hxneg.ne
      field_simp
      ring
    have := hqpos _ hr
    rw [hq, eval_qpol, Finset.prod_eq_zero (Finset.mem_univ j) hfac, mul_zero] at this
    exact lt_irrefl _ this
  · refine ae_restrict_of_local fun t ht => ?_
    obtain ⟨_, δ, hδ, _, hae⟩ := hall ht
    refine ⟨δ, hδ, ?_⟩
    filter_upwards [hae] with τ hτ
    rw [hq, eval_qpol] at hτ
    exact hτ

end Gluing

section LogConcavity

theorem isLogConcaveFunction_one : IsLogConcaveFunction (fun _ : ℝ => (1 : ℝ)) :=
  isLogConcaveFunction_of_rpow_le (fun _ => zero_le_one) fun _ _ t _ _ => by
    simp

theorem isLogConcaveFunction_indicator {J : Set ℝ} (hJ : Convex ℝ J) :
    IsLogConcaveFunction (J.indicator fun _ => (1 : ℝ)) := by
  refine isLogConcaveFunction_of_rpow_le (fun x => indicator_nonneg (fun _ _ => zero_le_one) x)
    fun x y t ht0 ht1 => ?_
  by_cases hx : x ∈ J
  · by_cases hy : y ∈ J
    · have hz : t • x + (1 - t) • y ∈ J := hJ hx hy ht0.le (sub_pos.2 ht1).le (by ring)
      rw [indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem hz]
      simp
    · rw [indicator_of_notMem hy, Real.zero_rpow (sub_pos.2 ht1).ne', mul_zero]
      exact indicator_nonneg (fun _ _ => zero_le_one) _
  · rw [indicator_of_notMem hx, Real.zero_rpow ht0.ne', zero_mul]
    exact indicator_nonneg (fun _ _ => zero_le_one) _

theorem isLogConcaveFunction_max_affine (a b : ℝ) :
    IsLogConcaveFunction (fun t : ℝ => max (a + b * t) 0) := by
  refine isLogConcaveFunction_of_rpow_le (fun t => le_max_right _ _) fun x y t ht0 ht1 => ?_
  have hnn : ∀ z, 0 ≤ max (a + b * z) 0 := fun z => le_max_right _ _
  by_cases hx : 0 < a + b * x
  · by_cases hy : 0 < a + b * y
    · have h1 := Real.geom_mean_le_arith_mean2_weighted ht0.le (sub_pos.2 ht1).le hx.le hy.le
        (by ring : t + (1 - t) = 1)
      have h2 : t * (a + b * x) + (1 - t) * (a + b * y) ≤
          max (a + b * (t • x + (1 - t) • y)) 0 := by
        refine le_trans (le_of_eq ?_) (le_max_left _ _)
        simp only [smul_eq_mul]; ring
      rw [max_eq_left hx.le, max_eq_left hy.le]
      exact h1.trans h2
    · have : max (a + b * y) 0 = 0 := max_eq_right (not_lt.1 hy)
      rw [this, Real.zero_rpow (sub_pos.2 ht1).ne', mul_zero]
      exact hnn _
  · have : max (a + b * x) 0 = 0 := max_eq_right (not_lt.1 hx)
    rw [this, Real.zero_rpow ht0.ne', zero_mul]
    exact hnn _

theorem isLogConcaveFunction_prod {m : ℕ} {g : Fin m → ℝ → ℝ}
    (hg : ∀ j, IsLogConcaveFunction (g j)) :
    IsLogConcaveFunction (fun t => ∏ j, g j t) := by
  have : ∀ s : Finset (Fin m), IsLogConcaveFunction (fun t => ∏ j ∈ s, g j t) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isLogConcaveFunction_one
    | insert a s ha ih =>
      simpa [Finset.prod_insert ha] using (hg a).mul ih
  simpa using this Finset.univ

/-- The explicit needle profile `1_J · c ρ · ∏_j (1 + (t - t₀) λ_j)_+`. -/
noncomputable def needleProfile {m : ℕ} (J : Set ℝ) (ρ : ℝ → ℝ) (c t₀ : ℝ) (lam : Fin m → ℝ)
    (t : ℝ) : ℝ :=
  J.indicator (fun _ => (1 : ℝ)) t * (c * ρ t) * ∏ j, max (1 + (t - t₀) * lam j) 0

theorem isLogConcaveFunction_needleProfile {m : ℕ} {J : Set ℝ} (hJc : Convex ℝ J) {ρ : ℝ → ℝ}
    (hρ : IsLogConcaveFunction ρ) {c : ℝ} (hc : 0 < c) (t₀ : ℝ) (lam : Fin m → ℝ) :
    IsLogConcaveFunction (needleProfile J ρ c t₀ lam) := by
  have h3 : IsLogConcaveFunction (fun t => ∏ j, max (1 + (t - t₀) * lam j) 0) :=
    isLogConcaveFunction_prod fun j => by
      have := isLogConcaveFunction_max_affine (1 - t₀ * lam j) (lam j)
      convert this using 2 with t
      ring_nf
  exact ((isLogConcaveFunction_indicator hJc).mul (hρ.const_mul hc)).mul h3

theorem measurable_needleProfile {m : ℕ} {J : Set ℝ} (hJm : MeasurableSet J) {ρ : ℝ → ℝ}
    (hρm : Measurable ρ) (c t₀ : ℝ) (lam : Fin m → ℝ) :
    Measurable (needleProfile J ρ c t₀ lam) := by
  unfold needleProfile
  refine ((measurable_const.indicator hJm).mul (measurable_const.mul hρm)).mul ?_
  exact Finset.measurable_prod _ fun j _ =>
    ((measurable_const.add ((measurable_id.sub measurable_const).mul measurable_const)).max
      measurable_const)

end LogConcavity





section Main

variable {n : ℕ} {ν : Measure ℝ} {ρ : ℝ → ℝ} {D J : Set ℝ} {ι : Type}

/-- **One-dimensional log-concavity from the shift identity.**  Let `ν` be a probability measure on
`ℝ` carried by an open interval `J ⊆ D`, where `ρ > 0` on the open set `D` and `ρ` is a measurable
log-concave function.  Suppose that for a countable family of windows the shift identity holds
(`ShiftData`).  Then `ν` has a log-concave density with respect to Lebesgue measure. -/
theorem exists_logConcave_density (S : ShiftData n ν ρ D J ι) [IsProbabilityMeasure ν] [Countable ι]
    (hD : IsOpen D) (hρm : Measurable ρ) (hρ : IsLogConcaveFunction ρ) (hρD : ∀ t ∈ D, 0 < ρ t)
    (hJo : IsOpen J) (hJc : Convex ℝ J) (hJD : J ⊆ D) (hνJ : ν Jᶜ = 0) :
    ∃ h : ℝ → ℝ, Measurable h ∧ IsLogConcaveFunction h ∧
      ν = volume.withDensity (fun t => ENNReal.ofReal (h t)) := by
  have hac : ν ≪ volume := absolutelyContinuous S hD hJD hνJ
  obtain ⟨c, lam, t₀, hc, ht₀J, hpos, hae⟩ :=
    global_formula S hD hρm hρ.nonnegative hρD hac hJo hJc hJD hνJ
  set h := needleProfile J ρ c t₀ lam with hh
  have hJ : ∀ t ∈ J, h t = ρ t * (c * ∏ j, (1 + (t - t₀) * lam j)) := by
    intro t ht
    simp only [hh, needleProfile, indicator_of_mem ht]
    rw [one_mul, Finset.prod_congr rfl fun j _ => max_eq_left (hpos t ht j).le]
    ring
  have hJc0 : ∀ t ∉ J, h t = 0 := by
    intro t ht
    simp [hh, needleProfile, indicator_of_notMem ht]
  have hdens : ∀ᵐ t ∂(volume : Measure ℝ), dens ν t = h t := by
    have h1 : ∀ᵐ t ∂(volume.restrict J), dens ν t = h t := by
      filter_upwards [hae, ae_restrict_mem hJo.measurableSet] with t ht1 ht2
      rw [ht1, hJ t ht2]
    have h2 : ∀ᵐ t ∂(volume.restrict Jᶜ), dens ν t = h t := by
      have h0 : ∫⁻ t in Jᶜ, ENNReal.ofReal (dens ν t) = 0 := by
        rw [← measure_eq_dens hac hJo.measurableSet.compl]
        exact hνJ
      have := (setLIntegral_eq_zero_iff hJo.measurableSet.compl
        measurable_dens.ennreal_ofReal).1 h0
      filter_upwards [(ae_restrict_iff' hJo.measurableSet.compl).2 this,
        ae_restrict_mem hJo.measurableSet.compl] with t ht1 ht2
      rw [hJc0 t ht2]
      have : ENNReal.ofReal (dens ν t) = 0 := ht1
      exact le_antisymm (ENNReal.ofReal_eq_zero.1 this) (dens_nonneg t)
    have := (ae_restrict_union_iff (s := J) (t := Jᶜ) _).2 ⟨h1, h2⟩
    simpa using this
  refine ⟨h, measurable_needleProfile hJo.measurableSet hρm c t₀ lam,
    isLogConcaveFunction_needleProfile hJc hρ hc t₀ lam, ?_⟩
  rw [← withDensity_dens hac]
  exact withDensity_congr_ae (hdens.mono fun t ht => congrArg ENNReal.ofReal ht)

end Main

end CvxBody.NeedleLC
