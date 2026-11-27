import Theorems.HarmonicSeriesDiverges.A
import Theorems.HarmonicSeriesDiverges.B

namespace TuriMath.HarmonicSeriesDiverges

open Filter Topology

/-- The two partial-sum sequences are the same function. -/
theorem partialSum_eq_H : A.partialSum = B.H := rfl

/-- Statements A (`Tendsto` form) and B (ε–N form) say the same thing: unfold both and match
the negated limit predicates through the metric characterisation of `Tendsto`. -/
theorem equiv : A.Statement ↔ B.Statement := by
  unfold A.Statement B.Statement
  rw [partialSum_eq_H]
  refine not_congr (exists_congr fun L => ?_)
  rw [Metric.tendsto_atTop]
  simp only [Real.dist_eq, ge_iff_le, gt_iff_lt]

end TuriMath.HarmonicSeriesDiverges
