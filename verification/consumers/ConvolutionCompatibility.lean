import HitAndRun.External.EllipticPDE.Embedding.ConvolutionCompatibility
noncomputable section
open MeasureTheory EllipticPdes.Embedding
open scoped ENNReal Convolution Topology
variable {d : ℕ}
example {p : ℝ} (hp : 1 ≤ p) {ρ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hρ0 : 0 ≤ ρ) (hρm : AEStronglyMeasurable ρ volume) (hρ1 : ∫ y, ρ y ∂volume = 1)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hh : MemLp h (ENNReal.ofReal p) volume)
    (s : Set (EuclideanSpace ℝ (Fin d))) :
    eLpNorm (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) (ENNReal.ofReal p) (volume.restrict s)
      ≤ eLpNorm h (ENNReal.ofReal p) volume := eLpNorm_convolution_restrict_le hp hρ0 hρm hρ1 hh s
example {E : Type*} [NormedAddCommGroup E] (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    stdBump (E := E) δ hδ n = EllipticPdes.mollifier hδ n := rfl
example {E : Type*} [NormedAddCommGroup E] {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (stdBump (E := E) δ hδ n).rIn = δ / (n + 1) / 2 := rIn_stdBump hδ n
example {E : Type*} [NormedAddCommGroup E] {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (stdBump (E := E) δ hδ n).rOut = δ / (n + 1) := rOut_stdBump hδ n
example {E : Type*} [NormedAddCommGroup E] {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun n => (stdBump (E := E) δ hδ n).rOut) Filter.atTop (𝓝 0) :=
  tendsto_rOut_stdBump hδ
example {E : Type*} [NormedAddCommGroup E] {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (stdBump (E := E) δ hδ n).rOut ≤ δ := rOut_stdBump_le_self hδ n
example {E : Type*} [NormedAddCommGroup E] {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (stdBump (E := E) δ hδ n).rOut ≤ 2 * (stdBump (E := E) δ hδ n).rIn :=
  rOut_stdBump_le hδ n
example {δ : ℝ} (hδ : 0 < δ) {h : EuclideanSpace ℝ (Fin d) → ℝ} (hh : Integrable h volume) :
    Filter.Tendsto (fun n => eLpNorm (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (stdBump δ hδ n : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))).normed volume - h) 1 volume)
      Filter.atTop (𝓝 0) := tendsto_eLpNorm_one_stdBump_convolution_sub hδ hh
#print axioms eLpNorm_convolution_restrict_le
#print axioms stdBump
#print axioms rIn_stdBump
#print axioms rOut_stdBump
#print axioms tendsto_rOut_stdBump
#print axioms rOut_stdBump_le_self
#print axioms rOut_stdBump_le
#print axioms tendsto_eLpNorm_one_stdBump_convolution_sub
