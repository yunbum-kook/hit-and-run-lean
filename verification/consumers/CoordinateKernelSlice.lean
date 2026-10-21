import HitAndRun.Markov.CoordinateKernelIdentification
open MeasureTheory HitAndRun.Markov HitAndRun.Geometry
example {n : ℕ} (i : Fin n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    chordLaw K x (EuclideanSpace.basisFun (Fin n) ℝ i) =
      coordinateSliceLaw i K (coordinateChart i x).1 :=
  chordLaw_eq_coordinateSliceLaw i K x
#print axioms HitAndRun.Markov.coordinateInsert_line
#print axioms HitAndRun.Markov.lineChord_volume_eq_coordinateSlice
#print axioms HitAndRun.Markov.chordLaw_eq_coordinateSliceLaw
