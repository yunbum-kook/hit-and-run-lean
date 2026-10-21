module
import KLS15
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace KLS15ReuseAudit

theorem exactDensity15 {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) 15 :=
  KLS15.openaiPoincare15 hn hρ hiso

theorem exactAdmissible15 {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (KLS.Space n)} (hμ : KLS.admissibleMeasure μ)
    {f : KLS.Space n → ℝ} (hf : KLS.LocallyLipschitzTests μ f) :
    KLS.variance μ f ≤ (15 : ℝ≥0∞) * KLS.energy μ f :=
  KLS15.poincare15 hn hμ hf

#print KLS15.openaiPoincare15
#print axioms exactDensity15
#print axioms exactAdmissible15
#print axioms KLS15.poincare15_mem
#print axioms KLS15.poincare15
#print axioms KLS15.universalPoincareUpper15
#print axioms KLS15.openaiPoincare15
#print axioms KLS15.openaiKLS
#print axioms KLS.OpenAIBridge.density_measureLogConcave
#print axioms KLS.OpenAIBridge.isotropic
#print axioms KLS.OpenAIBridge.admissible
#print axioms KLS.OpenAIBridge.poincareBound_of_mem
end KLS15ReuseAudit
