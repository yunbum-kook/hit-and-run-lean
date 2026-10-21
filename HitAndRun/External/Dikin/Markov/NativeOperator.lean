module
public import HitAndRun.External.Dikin.Markov.KernelLpLift
public import HitAndRun.External.Dikin.Markov.ReversibleSupport
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace DikinD2.NativeL2
set_option maxHeartbeats 800000
local instance : Fact (1 ≤ (2 : NNReal)) := ⟨by norm_num⟩
variable {α : Type*} [MeasurableSpace α]
variable {κ : Kernel α α} [IsMarkovKernel κ] {π : Measure α} [IsProbabilityMeasure π]

/-- Genuine Markov operator on real L2, formed from the Bochner kernel integral. -/
noncomputable def operator (κ : Kernel α α) [IsMarkovKernel κ] (π : Measure α)
    (hstat : κ ∘ₘ π = π) : Lp ℝ 2 π →L[ℝ] Lp ℝ 2 π :=
  MarkovProcess.kernelLpFinite π κ (MarkovProcess.IsSubMarkovKernel.of_isMarkovKernel κ)
    hstat.le 2

theorem operator_ae (hstat : κ ∘ₘ π = π) (f : Lp ℝ 2 π) :
    operator κ π hstat f =ᵐ[π] fun x => ∫ y, f y ∂κ x :=
  MarkovProcess.coeFn_kernelLpFinite π κ _ hstat.le 2 f

theorem operator_contract (hstat : κ ∘ₘ π = π) (f : Lp ℝ 2 π) :
    ‖operator κ π hstat f‖ ≤ ‖f‖ :=
  MarkovProcess.norm_kernelLpFinite_apply_le π κ _ hstat.le 2 f

theorem operator_norm_le (hstat : κ ∘ₘ π = π) : ‖operator κ π hstat‖ ≤ 1 :=
  MarkovProcess.norm_kernelLpFinite_le π κ _ hstat.le 2

theorem joint_fst (f : Lp ℝ 2 π) :
    MemLp (fun z : α × α => f z.1) 2 (π ⊗ₘ κ) :=
  (Lp.memLp f).comp_measurePreserving ⟨measurable_fst, Measure.fst_compProd π κ⟩

theorem joint_snd (hstat : κ ∘ₘ π = π) (f : Lp ℝ 2 π) :
    MemLp (fun z : α × α => f z.2) 2 (π ⊗ₘ κ) := by
  apply (Lp.memLp f).comp_measurePreserving
  refine ⟨measurable_snd, ?_⟩
  change Measure.snd (π ⊗ₘ κ) = π
  rw [Measure.snd_compProd, hstat]

/-- The actual L2 bilinear form is integration against the one-step joint law. -/
theorem inner_operator (hstat : κ ∘ₘ π = π) (f g : Lp ℝ 2 π) :
    inner ℝ f (operator κ π hstat g) = ∫ z, f z.1 * g z.2 ∂(π ⊗ₘ κ) := by
  have hi : Integrable (fun z : α × α => f z.1 * g z.2) (π ⊗ₘ κ) :=
    (joint_fst (κ := κ) f).integrable_mul (joint_snd hstat g)
  rw [L2.inner_def, Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards [operator_ae hstat g] with x hx
  simp only [Real.inner_apply, hx]
  rw [integral_const_mul]

theorem operator_symmetric (hrev : ReversibleSupport.JointReversible κ π) :
    (operator κ π (ReversibleSupport.stationary hrev)).IsSymmetric := by
  let hs := ReversibleSupport.stationary hrev
  intro f g
  change inner ℝ (operator κ π hs f) g = inner ℝ f (operator κ π hs g)
  rw [real_inner_comm, inner_operator hs, inner_operator hs]
  have hi : Integrable (fun z : α × α => g z.1 * f z.2) (π ⊗ₘ κ) :=
    (joint_fst (κ := κ) g).integrable_mul (joint_snd hs f)
  calc
    (∫ z, g z.1 * f z.2 ∂(π ⊗ₘ κ)) =
        ∫ z, g z.2 * f z.1 ∂(π ⊗ₘ κ) := by
      conv_lhs => rw [← hrev]
      exact integral_map measurable_swap.aemeasurable (by rw [show (π ⊗ₘ κ).map Prod.swap = π ⊗ₘ κ from hrev]; exact hi.aestronglyMeasurable)
    _ = _ := by apply integral_congr_ae; filter_upwards with z; ring

theorem operator_selfAdjoint (hrev : ReversibleSupport.JointReversible κ π) :
    IsSelfAdjoint (operator κ π (ReversibleSupport.stationary hrev)) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (operator_symmetric hrev)

/-- The true zero-expectation subspace, without a bounded-representative condition. -/
def meanZero (π : Measure α) [IsProbabilityMeasure π] : Submodule ℝ (Lp ℝ 2 π) where
  carrier := {f | ∫ x, f x ∂π = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change (∫ x, (f + g) x ∂π) = 0
    rw [integral_congr_ae (Lp.coeFn_add f g)]
    simp only [Pi.add_apply]
    rw [integral_add
      ((Lp.memLp f).integrable (by norm_num)) ((Lp.memLp g).integrable (by norm_num))]
    rw [show (∫ x, f x ∂π) = 0 from hf, show (∫ x, g x ∂π) = 0 from hg, add_zero]
  smul_mem' := by
    intro c f hf
    change (∫ x, (c • f) x ∂π) = 0
    rw [integral_congr_ae (Lp.coeFn_smul c f)]
    simp only [Pi.smul_apply]
    rw [integral_smul, show (∫ x, f x ∂π) = 0 from hf, smul_zero]

@[simp] theorem mem_meanZero (f : Lp ℝ 2 π) :
    f ∈ meanZero π ↔ ∫ x, f x ∂π = 0 := Iff.rfl

theorem mean_preserved (hrev : ReversibleSupport.JointReversible κ π) (f : Lp ℝ 2 π) :
    (∫ x, operator κ π (ReversibleSupport.stationary hrev) f x ∂π) = ∫ x, f x ∂π := by
  rw [integral_congr_ae (operator_ae _ f)]
  exact ReversibleSupport.integral_preserved hrev ((Lp.memLp f).integrable (by norm_num))

theorem meanZero_invariant (hrev : ReversibleSupport.JointReversible κ π)
    (f : Lp ℝ 2 π) (hf : f ∈ meanZero π) :
    operator κ π (ReversibleSupport.stationary hrev) f ∈ meanZero π := by
  rw [mem_meanZero, mean_preserved hrev]
  exact hf

noncomputable def constant (π : Measure α) [IsProbabilityMeasure π] (c : ℝ) : Lp ℝ 2 π :=
  (memLp_const c).toLp (fun _ => c)

theorem constant_ae (c : ℝ) : constant π c =ᵐ[π] fun _ => c := MemLp.coeFn_toLp _

theorem operator_constant (hstat : κ ∘ₘ π = π) (c : ℝ) :
    operator κ π hstat (constant π c) = constant π c := by
  apply Lp.ext
  refine (operator_ae hstat _).trans ?_
  refine (MarkovProcess.kernelIntegral_congr_ae hstat.le (constant_ae c)).trans ?_
  have he : MarkovProcess.kernelIntegral κ (fun _ => c) = fun _ => c := by
    funext x
    simp [MarkovProcess.kernelIntegral]
  rw [he]
  exact (constant_ae c).symm
end DikinD2.NativeL2
