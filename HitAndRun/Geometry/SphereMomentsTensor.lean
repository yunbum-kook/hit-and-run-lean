module
public import HitAndRun.Geometry.SphereMomentsFourth
@[expose] public section
namespace HitAndRun.Geometry
open MeasureTheory
variable {n : ℕ} [NeZero n]

/-- A continuous integrand odd under one coordinate flip has zero spherical mean. -/
theorem uniformSphere_integral_odd (r : Fin n) {f : UnitDirection n → ℝ}
    (hf : Continuous f) (hodd : ∀ θ, f (sphereAction (coordinateFlip r) θ) = -f θ) :
    (∫ θ, f θ ∂uniformSphere n) = 0 := by
  have h := uniformSphere_integral_rotation (coordinateFlip r) hf
  simp_rw [hodd, integral_neg] at h
  linarith

/-- Exact fourth-order coordinate tensor of the genuine uniform sphere. -/
theorem uniformSphere_integral_four (i j k l : Fin n) :
    (∫ θ : UnitDirection n, θ.val i * θ.val j * θ.val k * θ.val l ∂uniformSphere n) =
      ((if i = j ∧ k = l then (1 : ℝ) else 0) +
       (if i = k ∧ j = l then (1 : ℝ) else 0) +
       (if i = l ∧ j = k then (1 : ℝ) else 0)) / ((n : ℝ) * (n + 2)) := by
  by_cases hij : i = j
  · subst j
    by_cases hkl : k = l
    · subst l
      by_cases hik : i = k
      · subst k
        have h := uniformSphere_integral_fourth i
        convert h using 1
        · congr 1; funext θ; ring
        · norm_num
      · have h := uniformSphere_integral_sq_mul_sq i k hik
        convert h using 1
        · congr 1; funext θ; ring
        · simp [hik]
    · have hz : (∫ θ : UnitDirection n, θ.val i * θ.val i * θ.val k * θ.val l ∂uniformSphere n) = 0 := by
        by_cases hik : i = k
        · subst k
          apply uniformSphere_integral_odd l (by fun_prop)
          intro θ
          simp [sphereAction, hkl, Ne.symm hkl]
        · apply uniformSphere_integral_odd k (by fun_prop)
          intro θ
          simp [sphereAction, hik, Ne.symm hkl] <;> ring
      rw [hz]
      have hn : ¬ (i = k ∧ i = l) := by rintro ⟨rfl, h⟩; exact hkl h
      have hn' : ¬ (i = l ∧ i = k) := by rintro ⟨h, rfl⟩; exact hkl h
      simp [hkl, hn, hn']
  · by_cases hik : i = k
    · subst k
      by_cases hjl : j = l
      · subst l
        have h := uniformSphere_integral_sq_mul_sq i j hij
        convert h using 1
        · congr 1; funext θ; ring
        · simp [hij, Ne.symm hij]
      · have hz : (∫ θ : UnitDirection n, θ.val i * θ.val j * θ.val i * θ.val l ∂uniformSphere n) = 0 := by
          apply uniformSphere_integral_odd j (by fun_prop)
          intro θ
          simp [sphereAction, hij, Ne.symm hjl] <;> ring
        rw [hz]
        simp [hij, Ne.symm hij, hjl]
    · by_cases hil : i = l
      · subst l
        by_cases hjk : j = k
        · subst k
          have h := uniformSphere_integral_sq_mul_sq i j hij
          convert h using 1
          · congr 1; funext θ; ring
          · simp [hij, Ne.symm hij]
        · have hz : (∫ θ : UnitDirection n, θ.val i * θ.val j * θ.val k * θ.val i ∂uniformSphere n) = 0 := by
            apply uniformSphere_integral_odd j (by fun_prop)
            intro θ
            simp [sphereAction, hij, Ne.symm hjk] <;> ring
          rw [hz]
          simp [hij, hik, hjk]
      · have hz : (∫ θ : UnitDirection n, θ.val i * θ.val j * θ.val k * θ.val l ∂uniformSphere n) = 0 := by
          apply uniformSphere_integral_odd i (by fun_prop)
          intro θ
          simp [sphereAction, Ne.symm hij, Ne.symm hik, Ne.symm hil]
        rw [hz]
        simp [hij, hik, hil]
end HitAndRun.Geometry
