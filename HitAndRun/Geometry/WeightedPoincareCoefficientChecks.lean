module
public import HitAndRun.Geometry.WeightedPoincareCoefficient
@[expose] public section
open HitAndRun.Geometry
example (n : ℕ) (hn : 0 < n)
    {R B r : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B) (hr : 0 < r) :
    let a : ℝ := 1 - 1 / (2 * (n : ℝ))
    R * (a ^ n)⁻¹ / r + B * a * (a ^ n)⁻¹ / ((1 - a) * r) ≤
      (2 * R + 4 * (n : ℝ) * B) / r := radial_assembly_coefficient_le n hn hR hB hr
#print axioms HitAndRun.Geometry.radial_assembly_coefficient_le
