import Theorems.HarmonicSeriesDiverges.A

namespace TuriMath.HarmonicSeriesDiverges

open Filter Topology A

/-- Block estimate: `H(2n) - H(n) ≥ 1/2` for `n ≥ 1` (n terms, each `≥ 1/(2n)`). -/
theorem block_ge (n : ℕ) (hn : 1 ≤ n) : 1 / 2 ≤ partialSum (2 * n) - partialSum n := by
  have hI : ∀ N : ℕ, Finset.Icc 1 N = Finset.Ioc 0 N := by
    intro N; ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hsplit : partialSum (2 * n) = partialSum n + ∑ k ∈ Finset.Ioc n (2 * n), (1 : ℝ) / k := by
    unfold partialSum
    rw [hI, hI]
    exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le n) (by omega)).symm
  rw [hsplit, add_sub_cancel_left]
  have hle : ∀ k ∈ Finset.Ioc n (2 * n), (1 : ℝ) / (2 * n) ≤ 1 / k := by
    intro k hk
    rw [Finset.mem_Ioc] at hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have : (k : ℝ) ≤ 2 * n := by exact_mod_cast hk.2
    exact one_div_le_one_div_of_le hk0 this
  have := Finset.card_nsmul_le_sum _ _ _ hle
  simp only [Nat.card_Ioc, nsmul_eq_mul] at this
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : ((2 * n - n : ℕ) : ℝ) = n := by
    rw [show 2 * n - n = n by omega]
  rw [hc] at this
  have : (n : ℝ) * (1 / (2 * n)) = 1 / 2 := by field_simp
  linarith

/-- **The harmonic series diverges**: proved by the Cauchy-style block estimate, not by
citing Mathlib's divergence theorem. -/
theorem main : A.Statement := by
  rintro ⟨L, hL⟩
  have h2 : Tendsto (fun n : ℕ => partialSum (2 * n)) atTop (𝓝 L) :=
    hL.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
  have hd : Tendsto (fun n : ℕ => partialSum (2 * n) - partialSum n) atTop (𝓝 (L - L)) :=
    h2.sub hL
  rw [sub_self] at hd
  have hev := (Metric.tendsto_nhds.mp hd) (1 / 2) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have h1 := hN (max N 1) (le_max_left _ _)
  have h2 := block_ge (max N 1) (le_max_right _ _)
  rw [Real.dist_eq, sub_zero] at h1
  have := (abs_lt.mp h1).2
  linarith

end TuriMath.HarmonicSeriesDiverges
