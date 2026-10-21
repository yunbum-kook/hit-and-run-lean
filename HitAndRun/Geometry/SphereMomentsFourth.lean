module
public import HitAndRun.Geometry.SphereMomentsSecond
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
@[expose] public section

namespace HitAndRun.Geometry
open MeasureTheory Set
open scoped InnerProductSpace
variable {n : ℕ} [NeZero n]

/-- Fourth directional moment, evaluated against the genuine uniform sphere. -/
noncomputable def sphereFourth (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ θ : UnitDirection n, (⟪v, θ.val⟫_ℝ)^4 ∂uniformSphere n

/-- Orthogonal invariance of fourth directional moments follows from invariance of the measure. -/
theorem sphereFourth_isometry
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) : sphereFourth (U v) = sphereFourth v := by
  have h := uniformSphere_integral_rotation U
    ((continuous_const.inner continuous_subtype_val).pow 4 :
      Continuous (fun θ : UnitDirection n => (⟪U v, θ.val⟫_ℝ)^4))
  simpa only [sphereFourth, Pi.pow_apply, sphereAction, U.inner_map_map] using h.symm

/-- The fourth moment is radial; the reflection witnessing equal norms is constructed in Mathlib. -/
theorem sphereFourth_eq_of_norm_eq {v w : EuclideanSpace ℝ (Fin n)}
    (h : ‖v‖ = ‖w‖) : sphereFourth v = sphereFourth w := by
  have hi := sphereFourth_isometry ((ℝ ∙ (v - w))ᗮ.reflection) v
  rw [Submodule.reflection_sub h] at hi
  exact hi.symm

/-- The fourth moment is exactly degree-four homogeneous. -/
theorem sphereFourth_smul (r : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    sphereFourth (r • v) = r^4 * sphereFourth v := by
  simp only [sphereFourth, real_inner_smul_left, mul_pow, integral_const_mul]

/-- Radiality and homogeneity reduce every fourth linear-form moment to a unit vector. -/
theorem sphereFourth_eq_norm_pow_four_mul (v w : EuclideanSpace ℝ (Fin n))
    (hw : ‖w‖ = 1) : sphereFourth v = ‖v‖^4 * sphereFourth w := by
  calc
    sphereFourth v = sphereFourth (‖v‖ • w) :=
      sphereFourth_eq_of_norm_eq (by simp [norm_smul, hw])
    _ = _ := sphereFourth_smul _ _


theorem sphereFourth_basis (i : Fin n) :
    sphereFourth (EuclideanSpace.basisFun (Fin n) ℝ i) =
      ∫ θ : UnitDirection n, (θ.val i)^4 ∂uniformSphere n := by
  simp only [sphereFourth, EuclideanSpace.basisFun_inner]

theorem uniformSphere_integral_fourth_eq (i j : Fin n) :
    (∫ θ : UnitDirection n, (θ.val i)^4 ∂uniformSphere n) =
      ∫ θ : UnitDirection n, (θ.val j)^4 ∂uniformSphere n := by
  rw [← sphereFourth_basis, ← sphereFourth_basis]
  exact sphereFourth_eq_of_norm_eq (by simp only [OrthonormalBasis.norm_eq_one])

/-- The fourth moment of the sum of two distinct coordinates is four times a diagonal moment. -/
theorem uniformSphere_integral_add_fourth (i j : Fin n) (hij : i ≠ j) :
    (∫ θ : UnitDirection n, (θ.val i + θ.val j)^4 ∂uniformSphere n) =
      4 * ∫ θ : UnitDirection n, (θ.val i)^4 ∂uniformSphere n := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hn : ‖b i + b j‖^2 = 2 := by
    rw [norm_add_sq_real, b.norm_eq_one, b.norm_eq_one, b.orthonormal.inner_eq_zero hij]
    norm_num
  have hn4 : ‖b i + b j‖^4 = 4 := by nlinarith [sq_nonneg (‖b i + b j‖^2 - 2)]
  have h := sphereFourth_eq_norm_pow_four_mul (b i + b j) (b i) (b.norm_eq_one i)
  rw [hn4] at h
  simpa only [sphereFourth, b, inner_add_left, EuclideanSpace.basisFun_inner] using h

/-- The difference has the same fourth moment as the sum. -/
theorem uniformSphere_integral_sub_fourth (i j : Fin n) (hij : i ≠ j) :
    (∫ θ : UnitDirection n, (θ.val i - θ.val j)^4 ∂uniformSphere n) =
      4 * ∫ θ : UnitDirection n, (θ.val i)^4 ∂uniformSphere n := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hn : ‖b i - b j‖^2 = 2 := by
    rw [norm_sub_sq_real, b.norm_eq_one, b.norm_eq_one, b.orthonormal.inner_eq_zero hij]
    norm_num
  have hn4 : ‖b i - b j‖^4 = 4 := by nlinarith [sq_nonneg (‖b i - b j‖^2 - 2)]
  have h := sphereFourth_eq_norm_pow_four_mul (b i - b j) (b i) (b.norm_eq_one i)
  rw [hn4] at h
  simpa only [sphereFourth, b, inner_sub_left, EuclideanSpace.basisFun_inner] using h


/-- The true fourth moments satisfy the classical diagonal-to-mixed ratio three. -/
theorem uniformSphere_fourth_eq_three_mixed (i j : Fin n) (hij : i ≠ j) :
    (∫ θ : UnitDirection n, (θ.val i)^4 ∂uniformSphere n) =
      3 * ∫ θ : UnitDirection n, (θ.val i)^2 * (θ.val j)^2 ∂uniformSphere n := by
  have ci : Continuous (fun θ : UnitDirection n => θ.val i) := (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp continuous_subtype_val
  have cj : Continuous (fun θ : UnitDirection n => θ.val j) := (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp continuous_subtype_val
  have ha : Integrable (fun θ : UnitDirection n => (θ.val i + θ.val j)^4) (uniformSphere n) :=
    uniformSphere_integrable (by fun_prop)
  have hs : Integrable (fun θ : UnitDirection n => (θ.val i - θ.val j)^4) (uniformSphere n) :=
    uniformSphere_integrable (by fun_prop)
  have hi : Integrable (fun θ : UnitDirection n => (θ.val i)^4) (uniformSphere n) :=
    uniformSphere_integrable (by fun_prop)
  have hj : Integrable (fun θ : UnitDirection n => (θ.val j)^4) (uniformSphere n) :=
    uniformSphere_integrable (by fun_prop)
  have hm : Integrable (fun θ : UnitDirection n => (θ.val i)^2 * (θ.val j)^2) (uniformSphere n) :=
    uniformSphere_integrable (by fun_prop)
  have hl : Integrable (fun θ : UnitDirection n => 2 * (θ.val i)^4 + 12 * ((θ.val i)^2 * (θ.val j)^2)) (uniformSphere n) :=
    uniformSphere_integrable (by fun_prop)
  have hpoly : (fun θ : UnitDirection n => (θ.val i + θ.val j)^4 + (θ.val i - θ.val j)^4) =
      (fun θ => 2 * (θ.val i)^4 + 12 * ((θ.val i)^2 * (θ.val j)^2) + 2 * (θ.val j)^4) := by
    funext θ
    ring
  have h := congrArg (fun f : UnitDirection n → ℝ => ∫ θ, f θ ∂uniformSphere n) hpoly
  rw [integral_add ha hs, integral_add hl (hj.const_mul 2),
    integral_add (hi.const_mul 2) (hm.const_mul 12), integral_const_mul,
    integral_const_mul, integral_const_mul, uniformSphere_integral_add_fourth i j hij,
    uniformSphere_integral_sub_fourth i j hij, uniformSphere_integral_fourth_eq j i] at h
  linarith


/-- Exact diagonal fourth moment; no isotropy or moment hypotheses are assumed. -/
theorem uniformSphere_integral_fourth (i : Fin n) :
    (∫ θ : UnitDirection n, (θ.val i)^4 ∂uniformSphere n) =
      3 / ((n : ℝ) * (n + 2)) := by
  let a := ∫ θ : UnitDirection n, (θ.val i)^4 ∂uniformSphere n
  let m := fun j : Fin n => ∫ θ : UnitDirection n, (θ.val i)^2 * (θ.val j)^2 ∂uniformSphere n
  have hsum : ∑ j, m j = 1 / (n : ℝ) := by
    unfold m
    rw [← integral_finsetSum]
    · simp_rw [← Finset.mul_sum, unitDirection_sum_sq, mul_one]
      exact uniformSphere_integral_sq i
    · intro j _
      exact uniformSphere_integrable
        ((((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp continuous_subtype_val).pow 2).mul
          (((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp continuous_subtype_val).pow 2))
  have hp (j : Fin n) : 3 * m j = a + if j = i then 2 * a else 0 := by
    by_cases h : j = i
    · subst j
      have hm : m i = a := by
        unfold m a
        congr 1
        funext θ
        ring
      simp [hm]
      ring
    · simp only [if_neg h, add_zero]
      exact (uniformSphere_fourth_eq_three_mixed i j (Ne.symm h)).symm
  have htotal : 3 / (n : ℝ) = ((n : ℝ) + 2) * a := by
    calc
      3 / (n : ℝ) = 3 * ∑ j, m j := by rw [hsum]; ring
      _ = ∑ j, (a + if j = i then 2 * a else 0) := by simp_rw [Finset.mul_sum, hp]
      _ = ((n : ℝ) + 2) * a := by simp [Finset.sum_add_distrib]; ring
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  apply (eq_div_iff (mul_ne_zero hn hn2)).2
  have ht := congrArg (fun x : ℝ => (n : ℝ) * x) htotal
  have hc : (n : ℝ) * (3 / (n : ℝ)) = 3 := by field_simp
  rw [hc] at ht
  change a * ((n : ℝ) * ((n : ℝ) + 2)) = 3
  nlinarith

/-- Exact mixed even fourth moment for distinct coordinates. -/
theorem uniformSphere_integral_sq_mul_sq (i j : Fin n) (hij : i ≠ j) :
    (∫ θ : UnitDirection n, (θ.val i)^2 * (θ.val j)^2 ∂uniformSphere n) =
      1 / ((n : ℝ) * (n + 2)) := by
  have h := uniformSphere_fourth_eq_three_mixed i j hij
  rw [uniformSphere_integral_fourth] at h
  simp only [div_eq_mul_inv] at *
  linarith

end HitAndRun.Geometry
