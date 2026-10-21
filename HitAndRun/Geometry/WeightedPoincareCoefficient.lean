module
public import HitAndRun.Geometry.WeightedPoincareGeometry
@[expose] public section
namespace HitAndRun.Geometry
/-- The geometric assembly has the paper's dimension scaling at its specified
contraction parameter. This does not supply the ordinary L1 input. -/
theorem radial_assembly_coefficient_le (n : ℕ) (hn : 0 < n)
    {R B r : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B) (hr : 0 < r) :
    let a : ℝ := 1 - 1 / (2 * (n : ℝ))
    R * (a ^ n)⁻¹ / r + B * a * (a ^ n)⁻¹ / ((1 - a) * r) ≤
      (2 * R + 4 * (n : ℝ) * B) / r := by
  dsimp only
  let a : ℝ := 1 - 1 / (2 * (n : ℝ))
  change R * (a ^ n)⁻¹ / r + B * a * (a ^ n)⁻¹ / ((1 - a) * r) ≤ _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ha0 : 0 < a := by
    dsimp [a]
    have h : 1 / (2 * (n : ℝ)) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    linarith
  have ha1 : a < 1 := by
    dsimp [a]
    have h : 0 < 1 / (2 * (n : ℝ)) := by positivity
    linarith
  have hp : (a ^ n)⁻¹ ≤ 2 := contraction_inverse_power_upper n hn
  have hfirst : R * (a ^ n)⁻¹ / r ≤ 2 * R / r :=
    div_le_div_of_nonneg_right (by nlinarith) hr.le
  have hnum : B * a * (a ^ n)⁻¹ ≤ 2 * B := by
    have h := mul_le_mul_of_nonneg_left hp (mul_nonneg hB ha0.le)
    nlinarith
  have hsecond : B * a * (a ^ n)⁻¹ / ((1 - a) * r) ≤ 4 * (n : ℝ) * B / r := by
    have h := div_le_div_of_nonneg_right hnum (mul_nonneg (sub_nonneg.mpr ha1.le) hr.le)
    have he : 2 * B / ((1 - a) * r) = 4 * (n : ℝ) * B / r := by
      dsimp [a]
      field_simp
      <;> ring
    exact h.trans_eq he
  have h := add_le_add hfirst hsecond
  simpa only [← add_div] using h
end HitAndRun.Geometry
