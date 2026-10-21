module
public import HitAndRun.Markov.CoordinateKernelIdentificationNative
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
@[expose] public section

namespace HitAndRun.Markov
open MeasureTheory ProbabilityTheory DikinD2
open scoped ENNReal ProbabilityTheory RealInnerProductSpace

/-- Symmetry of the genuine native integral operator implies symmetry of its actual joint law. -/
theorem jointReversible_of_native_symmetric {A : Type*} [MeasurableSpace A]
    [TopologicalSpace A] [BorelSpace A] [HasOuterApproxClosed A]
    (κ : Kernel A A) [IsMarkovKernel κ] (π : Measure A) [IsProbabilityMeasure π]
    (hstat : κ ∘ₘ π = π) (hsym : (NativeL2.operator κ π hstat).IsSymmetric) :
    ReversibleSupport.JointReversible κ π := by
  have hf : ∀ f : BoundedContinuousFunction A ℝ, MemLp f 2 π := fun f => f.memLp_top.mono_exponent le_top
  have hform : ∀ f g : BoundedContinuousFunction A ℝ,
      inner ℝ ((hf f).toLp f) (NativeL2.operator κ π hstat ((hf g).toLp g)) =
        ∫ z, f z.1 * g z.2 ∂(π ⊗ₘ κ) := by
    intro f g
    rw [NativeL2.inner_operator hstat]
    have hfst : MeasurePreserving (Prod.fst : A × A → A) (π ⊗ₘ κ) π :=
      ⟨measurable_fst, Measure.fst_compProd π κ⟩
    have hsnd : MeasurePreserving (Prod.snd : A × A → A) (π ⊗ₘ κ) π := by
      refine ⟨measurable_snd, ?_⟩
      change (π ⊗ₘ κ).snd = π
      rw [Measure.snd_compProd, hstat]
    exact integral_congr_ae ((hfst.quasiMeasurePreserving.ae_eq_comp (hf f).coeFn_toLp).mul
      (hsnd.quasiMeasurePreserving.ae_eq_comp (hf g).coeFn_toLp))
  apply Measure.ext_of_integral_mul_boundedContinuousFunction
  intro f g
  change (∫ p : A × A, f p.1 * g p.2 ∂(π ⊗ₘ κ).map
    (MeasurableEquiv.prodComm (α := A) (β := A))) = _
  rw [integral_map_equiv (MeasurableEquiv.prodComm (α := A) (β := A))]
  calc
    (∫ z, f z.2 * g z.1 ∂(π ⊗ₘ κ)) = ∫ z, g z.1 * f z.2 ∂(π ⊗ₘ κ) := by
      apply integral_congr_ae
      filter_upwards with z
      exact mul_comm _ _
    _ = inner ℝ ((hf g).toLp g) (NativeL2.operator κ π hstat ((hf f).toLp f)) := (hform g f).symm
    _ = inner ℝ (NativeL2.operator κ π hstat ((hf f).toLp f)) ((hf g).toLp g) := real_inner_comm _ _
    _ = inner ℝ ((hf f).toLp f) (NativeL2.operator κ π hstat ((hf g).toLp g)) := hsym _ _
    _ = _ := hform f g

variable {n : ℕ} [NeZero n] (K : HitAndRun.Sobolev.BoundedOpenDomain n)
local instance : IsMarkovKernel (coordinateHitAndRun K.carrier K.isOpen.measurableSet) :=
  coordinateHitAndRun_markov K.isOpen K.isBounded

/-- Genuine detailed balance of coordinate Hit-and-Run, as equality of joint measures. -/
theorem coordinateHitAndRun_jointReversible :
    ReversibleSupport.JointReversible (coordinateHitAndRun K.carrier K.isOpen.measurableSet)
      K.bodyUniform :=
  jointReversible_of_native_symmetric _ _ (coordinateHitAndRun_stationary K)
    (coordinateNativeOperator_symmetric K)

end HitAndRun.Markov
