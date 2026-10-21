module
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic
@[expose] public section

/-! Selected Dikin generic positive-operator contraction results.
Reused with the owner's explicit authorization from dikin-d2 commit
c5f8471b62573fc0417bfafeb16c2b5be2637ff1. No half-lazy kernel is introduced.
No public license grant is inferred for original upstream code.
-/
namespace HitAndRun.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- A positive operator with a quadratic gap has the sharp operator-norm bound. -/
lemma norm_le_one_sub_gap (P : E →L[ℝ] E) (hP : P.IsPositive)
    (lam : ℝ) (hlam : lam ≤ 1)
    (hgap : ∀ x, lam * ‖x‖ ^ 2 ≤ ⟪x, x - P x⟫) : ‖P‖ ≤ 1 - lam := by
  rw [P.norm_eq_iSup_rayleighQuotient hP.isSymmetric]
  apply ciSup_le
  intro x
  have hp := hP.inner_nonneg_left x
  have hg := hgap x
  rw [inner_sub_right, real_inner_self_eq_norm_sq, ← real_inner_comm x (P x)] at hg
  change |⟪P x, x⟫ / ‖x‖ ^ 2| ≤ 1 - lam
  rw [abs_of_nonneg (div_nonneg hp (sq_nonneg _))]
  by_cases hx : x = 0
  · simp [hx]; linarith
  · apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).2
    nlinarith

/-- Sharp squared decay, with explicit range including both endpoints. -/
theorem iterate_sq_le_exp (P : E →L[ℝ] E) (hP : P.IsPositive)
    (lam : ℝ) (_hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1)
    (hgap : ∀ x, lam * ‖x‖ ^ 2 ≤ ⟪x, x - P x⟫) (N : ℕ) (x : E) :
    ‖(P : E → E)^[N] x‖ ^ 2 ≤ Real.exp (-2 * lam * N) * ‖x‖ ^ 2 := by
  have hn := norm_le_one_sub_gap P hP lam hlam₁ hgap
  have he : 1 - lam ≤ Real.exp (-lam) := by
    have := Real.add_one_le_exp (-lam)
    linarith
  have hstep (y : E) : ‖P y‖ ≤ Real.exp (-lam) * ‖y‖ :=
    (P.le_opNorm y).trans (mul_le_mul_of_nonneg_right (hn.trans he) (norm_nonneg y))
  have hi : ‖(P : E → E)^[N] x‖ ≤ Real.exp (-lam * N) * ‖x‖ := by
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        ‖P ((P : E → E)^[n] x)‖ ≤ Real.exp (-lam) * ‖(P : E → E)^[n] x‖ := hstep _
        _ ≤ Real.exp (-lam) * (Real.exp (-lam * n) * ‖x‖) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)
        _ = Real.exp (-lam * (n + 1 : ℕ)) * ‖x‖ := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          push_cast
          ring
  have hs := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)) |>.2 hi
  calc
    ‖(P : E → E)^[N] x‖ ^ 2 ≤ (Real.exp (-lam * N) * ‖x‖) ^ 2 := hs
    _ = Real.exp (-2 * lam * N) * ‖x‖ ^ 2 := by
      rw [mul_pow, sq, ← Real.exp_add]
      congr 2
      ring

/-- Gap assumptions need hold only on the invariant subspace (e.g. mean-zero L2).
No closedness, completeness, dimension, or nontriviality is required. -/
theorem iterate_sq_le_exp_on_submodule (P : E →L[ℝ] E) (hP : P.IsPositive)
    (S : Submodule ℝ E) (hinv : ∀ x ∈ S, P x ∈ S)
    (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1)
    (hgap : ∀ x ∈ S, lam * ‖x‖ ^ 2 ≤ ⟪x, x - P x⟫)
    (N : ℕ) (x : E) (hx : x ∈ S) :
    ‖(P : E → E)^[N] x‖ ^ 2 ≤ Real.exp (-2 * lam * N) * ‖x‖ ^ 2 := by
  let R : S →L[ℝ] S := P.restrict hinv
  have hR : R.IsPositive := by
    apply (ContinuousLinearMap.isPositive_iff _).2
    constructor
    · intro a b
      exact hP.isSymmetric (a : E) (b : E)
    · intro a
      exact hP.inner_nonneg_left (a : E)
  have hg : ∀ a : S, lam * ‖a‖ ^ 2 ≤ inner ℝ a (a - R a) := by
    intro a
    exact hgap a a.property
  have hit (n : ℕ) : ((R : S → S)^[n] ⟨x, hx⟩ : E) = (P : E → E)^[n] x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [Function.iterate_succ_apply']
      change P (((R : S → S)^[n] ⟨x, hx⟩ : S) : E) = _
      rw [ih]
  have h := iterate_sq_le_exp R hR lam hlam₀ hlam₁ hg N ⟨x, hx⟩
  change ‖((R : S → S)^[N] ⟨x, hx⟩ : E)‖ ^ 2 ≤ Real.exp (-2 * lam * N) * ‖x‖ ^ 2 at h
  simpa only [hit] using h

end HitAndRun.Analysis
