import HitAndRun

noncomputable section

example {c d M ε : ℝ} (hc : 0 < c) (hd : 0 < d) :
    HitAndRun.Markov.mixingBudget (c / d) M ε =
      if M ≤ ε then 0 else Nat.ceil (d * Real.log (M / ε) / (2 * c)) :=
  HitAndRun.Markov.mixingSource_budget_formula hc hd

#print axioms HitAndRun.Markov.mixingSource_budget_formula
