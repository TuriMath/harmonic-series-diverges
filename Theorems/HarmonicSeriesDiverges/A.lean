import Mathlib

/-!
# Divergence of the harmonic series — statement A (Noether)

Source (Wikipedia, "Harmonic series (mathematics)", lead; Wiedijk 100 #34):
> In mathematics, the harmonic series is the infinite series formed by summing all
> positive unit fractions. … the harmonic series does not have a finite limit:
> it is a divergent series.
-/

namespace TuriMath.HarmonicSeriesDiverges.A

open Filter Topology

/-- The `N`-th partial sum of the harmonic series, `1/1 + 1/2 + ⋯ + 1/N`, in `ℝ`.
`partialSum 0 = 0` (empty sum). -/
noncomputable def partialSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n

/-- **The harmonic series diverges.**

Mapping from the source quote to the Lean:
* "positive unit fractions" ↦ `(1 : ℝ) / n` for `n : ℕ` with `1 ≤ n`
  (ℕ starting at 1, because "positive"; values in ℝ, the usual setting of a "finite limit").
* "the infinite series formed by summing all" ↦ the sequence of partial sums
  `partialSum N = ∑ n ∈ Finset.Icc 1 N, 1 / n`, indexed by `N : ℕ`, `N → ∞` (`atTop`).
* "does not have a finite limit" ↦ `¬ ∃ L : ℝ, Tendsto partialSum atTop (𝓝 L)`:
  there is no real number that the partial sums converge to.
* "it is a divergent series" ↦ the same thing (a series diverges iff its partial sums
  do not converge). Nothing stronger is claimed: in particular, not `Tendsto … atTop atTop`.
-/
def Statement : Prop :=
  ¬ ∃ L : ℝ, Tendsto partialSum atTop (𝓝 L)

/-! ## Sanity section

`Statement` has no hypotheses, so there is nothing to show jointly satisfiable.
Instead, check that `partialSum` is the intended sequence on small values. -/

example : partialSum 0 = 0 := by
  simp [partialSum]

example : partialSum 1 = 1 := by
  simp [partialSum]

example : partialSum 3 = 1 + 1 / 2 + 1 / 3 := by
  simp [partialSum, Finset.sum_Icc_succ_top]

end TuriMath.HarmonicSeriesDiverges.A
