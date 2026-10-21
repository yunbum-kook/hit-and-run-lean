/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file ../LICENSE.
Authors: Alejandro Soto Franco

Compatibility signatures adapted from the licensed EllipticPdes Convolution interface.
Proofs reuse this project's pinned production Young and mollifier implementations.
No staged KLS endpoint or duplicate Sobolev carrier is imported.
-/
module
public import HitAndRun.External.EllipticPDE.Embedding.Convolution
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal Convolution Topology
namespace EllipticPdes.Embedding
variable {d : ℕ}

/-- Restricted form of the production scalar Young inequality, with the historical API. -/
theorem eLpNorm_convolution_restrict_le {p : ℝ} (hp : 1 ≤ p)
    {ρ : EuclideanSpace ℝ (Fin d) → ℝ} (hρ0 : 0 ≤ ρ) (hρm : AEStronglyMeasurable ρ volume)
    (hρ1 : ∫ y, ρ y ∂volume = 1) {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hh : MemLp h (ENNReal.ofReal p) volume) (s : Set (EuclideanSpace ℝ (Fin d))) :
    eLpNorm (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) (ENNReal.ofReal p)
        (volume.restrict s) ≤ eLpNorm h (ENNReal.ofReal p) volume :=
  le_trans (eLpNorm_mono_measure _ Measure.restrict_le_self)
    (eLpNorm_convolution_le hp hρ0 hρm hρ1 hh)

/-- Historical name for the identical production shrinking bump. -/
def stdBump {E : Type*} [NormedAddCommGroup E] (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    ContDiffBump (0 : E) := mollifier hδ n

@[simp] theorem rIn_stdBump {E : Type*} [NormedAddCommGroup E]
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (stdBump (E := E) δ hδ n).rIn = δ / (n + 1) / 2 := rfl

@[simp] theorem rOut_stdBump {E : Type*} [NormedAddCommGroup E]
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (stdBump (E := E) δ hδ n).rOut = δ / (n + 1) := rfl

theorem tendsto_rOut_stdBump {E : Type*} [NormedAddCommGroup E]
    {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun n => (stdBump (E := E) δ hδ n).rOut) Filter.atTop (𝓝 0) :=
  tendsto_rOut_mollifier hδ

theorem rOut_stdBump_le_self {E : Type*} [NormedAddCommGroup E]
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : (stdBump (E := E) δ hδ n).rOut ≤ δ :=
  rOut_mollifier_le hδ n

theorem rOut_stdBump_le {E : Type*} [NormedAddCommGroup E]
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (stdBump (E := E) δ hδ n).rOut ≤ 2 * (stdBump (E := E) δ hδ n).rIn :=
  rOut_mollifier_le_two_mul_rIn hδ n

theorem tendsto_eLpNorm_one_stdBump_convolution_sub {δ : ℝ} (hδ : 0 < δ)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hh : Integrable h volume) :
    Filter.Tendsto (fun n => eLpNorm (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (stdBump δ hδ n : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))).normed volume - h) 1 volume)
      Filter.atTop (𝓝 0) :=
  tendsto_eLpNorm_one_mollifier_convolution_sub hδ hh
end EllipticPdes.Embedding
