import Mathlib

/-!
# Divergence of the harmonic series — statement B (Gauss)

Source (Wikipedia, "Harmonic series (mathematics)", lead; Wiedijk 100, item 34):
> In mathematics, the harmonic series is the infinite series formed by summing all positive
> unit fractions.
> … the harmonic series does not have a finite limit: it is a divergent series.

Mapping, one line each:
* "all positive unit fractions"              ↦ the terms `1 / k` for `k = 1, 2, 3, …`
                                                (`k ∈ Finset.Icc 1 n`, so `1/0` never appears)
* "the infinite series formed by summing"    ↦ its partial sums `H n = 1/1 + 1/2 + ⋯ + 1/n` in `ℝ`
* "a finite limit"                           ↦ a real number `L` with the elementary ε–N property
                                                `∀ ε > 0, ∃ N, ∀ n ≥ N, |H n - L| < ε`
* "does not have a finite limit"             ↦ `¬ ∃ L : ℝ, …` (no real `L` works)
* "it is a divergent series"                 ↦ same content: not convergent to any real number

Phrasing is deliberately elementary (explicit ε–N, `Finset.Icc 1 n`), not `Tendsto`/`Summable`.
-/

namespace TuriMath.HarmonicSeriesDiverges.B

/-- `H n = 1/1 + 1/2 + ⋯ + 1/n`, the `n`-th partial sum of the harmonic series (`H 0 = 0`). -/
noncomputable def H (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k

/-- The harmonic series has no finite limit: no real `L` is the ε–N limit of its partial sums. -/
def Statement : Prop :=
  ¬ ∃ L : ℝ, ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |H n - L| < ε

/-! ## Sanity section -/

-- The statement has no hypotheses, so nothing can be vacuous on that side.
-- Concrete partial sums: H 1 = 1, H 2 = 3/2, H 4 = 25/12 (= 1 + 1/2 + 1/3 + 1/4).
example : H 0 = 0 := by simp [H]
example : H 1 = 1 := by simp [H]
example : H 2 = 3 / 2 := by
  simp only [H]; rw [show Finset.Icc 1 2 = {1, 2} from by decide]; norm_num
example : H 4 = 25 / 12 := by
  simp only [H]; rw [show Finset.Icc 1 4 = {1, 2, 3, 4} from by decide]; norm_num

-- Every term really is a positive unit fraction 1/k with k ≥ 1.
example (n k : ℕ) (hk : k ∈ Finset.Icc 1 n) : 0 < (1 : ℝ) / k := by
  have : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  positivity

-- The "has a finite limit" predicate is not vacuous: it holds for a convergent sequence
-- (the constant sequence 1 has limit 1), so `Statement` is a genuine negation, not `¬ False`.
example : ∃ L : ℝ, ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(fun _ : ℕ => (1 : ℝ)) n - L| < ε :=
  ⟨1, fun ε hε => ⟨0, fun n _ => by simpa using hε⟩⟩

-- …and it fails for a sequence that clearly diverges (n itself), matching the intended reading.
example : ¬ ∃ L : ℝ, ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |(n : ℝ) - L| < ε := by
  rintro ⟨L, hL⟩
  obtain ⟨N, hN⟩ := hL 1 one_pos
  obtain ⟨m, hm⟩ := exists_nat_gt (L + 1)
  have h := hN (max N m) (le_max_left _ _)
  have : (m : ℝ) ≤ (max N m : ℕ) := by exact_mod_cast le_max_right N m
  have := (abs_lt.mp h).2
  linarith

end TuriMath.HarmonicSeriesDiverges.B
