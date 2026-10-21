module
public import HitAndRun.Analysis.IntegralCertificate
@[expose] public section
open MeasureTheory HitAndRun.Analysis
example {α H : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (r g : α → H) (hr : MemLp r 2 μ) (hg : MemLp g 2 μ)
    (F C : ℝ) (hF : 0 ≤ F) (hC : 0 ≤ C)
    (hpair : (∫ x, inner ℝ (r x) (g x) ∂μ) = F)
    (hbound : (∫ x, ‖g x‖ ^ 2 ∂μ) ≤ C * F) :
    F ≤ C * ∫ x, ‖r x‖ ^ 2 ∂μ := integral_certificate_energy r g hr hg F C hF hC hpair hbound
#print axioms HitAndRun.Analysis.integral_certificate_energy
