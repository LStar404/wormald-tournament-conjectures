import Wormald.ComparisonCone

/-!
# Strictness of comparison on the prefix cone

The comparison matrix need not be invertible. Its kernel, however, meets the
nonnegative-prefix cone only at zero when the dimension is at least two.
The first two rows force the total sum to vanish; the remaining coordinates
are then recovered from right to left.
-/

namespace Wormald
noncomputable section
open scoped BigOperators
open Matrix

private theorem comparisonMatrix_row_of_tail_zero {n : ℕ} (x : Fin n → ℝ)
    (j : Fin n) (htail : ∀ k : Fin n, j.val < k.val → x k = 0) :
    (comparisonMatrix n *ᵥ x) ⟨n - 1 - j.val, by have := j.isLt; omega⟩ =
      prefixSum x j.val := by
  simp only [Matrix.mulVec, dotProduct, prefixSum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  have hL : n - 1 - (n - 1 - j.val) = j.val := by have := j.isLt; omega
  rw [comparisonMatrix_entry]
  simp only [hL]
  by_cases hk : k.val < j.val
  · simp [hk]
  · by_cases hkj : k.val = j.val
    · simp [hkj]
    · rw [htail k (by omega)]
      simp [hk]

private theorem prefixSum_eq_sum_of_tail_zero {n : ℕ} (x : Fin n → ℝ)
    (r : ℕ) (htail : ∀ k : Fin n, r ≤ k.val → x k = 0) :
    prefixSum x r = ∑ k, x k := by
  simp only [prefixSum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.val < r
  · simp [hk]
  · simp [hk, htail k (by omega)]

/-- A zero-sum vector in the comparison kernel vanishes, even in odd dimension. -/
theorem comparisonMatrix_kernel_eq_zero_of_sum_eq_zero {n : ℕ} (x : Fin n → ℝ)
    (hker : comparisonMatrix n *ᵥ x = 0) (hsum : (∑ k, x k) = 0) : x = 0 := by
  have hzero : ∀ r : ℕ, ∀ j : Fin n, n - j.val = r → x j = 0 := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro j hj
      have htail : ∀ k : Fin n, j.val < k.val → x k = 0 := by
        intro k hk
        exact ih (n - k.val) (by have := k.isLt; omega) k rfl
      have hcur : prefixSum x j.val = 0 := by
        have h := congrFun hker ⟨n - 1 - j.val, by have := j.isLt; omega⟩
        rw [comparisonMatrix_row_of_tail_zero x j htail] at h
        exact h
      have hnext : prefixSum x (j.val + 1) = 0 := by
        rw [prefixSum_eq_sum_of_tail_zero x _ (fun k hk => htail k (by omega)), hsum]
      rw [prefixSum_succ x j.val j.isLt, hcur, zero_add] at hnext
      exact hnext
  funext j
  exact hzero _ j rfl

private theorem comparisonMatrix_first_row {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    (comparisonMatrix n *ᵥ x) ⟨0, hn⟩ = prefixSum x (n - 1) := by
  simpa using comparisonMatrix_row_of_tail_zero x ⟨n - 1, by omega⟩
    (fun k hk => by change n - 1 < k.val at hk; have := k.isLt; omega)

private theorem comparisonMatrix_second_row {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    (comparisonMatrix n *ᵥ x) ⟨1, by omega⟩ =
      prefixSum x (n - 2) + prefixSum x n - prefixSum x (n - 1) := by
  simp only [Matrix.mulVec, dotProduct, prefixSum, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hk := k.isLt
  have hL : n - 1 - 1 = n - 2 := by omega
  rw [comparisonMatrix_entry]
  simp only [hL]
  by_cases hk2 : k.val < n - 2
  · have hk1 : k.val < n - 1 := by omega
    simp [hk2, hk1, hk]
  · by_cases heq : k.val = n - 2
    · have hn0 : 0 < n := by omega
      have hn1 : n - 2 < n - 1 := by omega
      simp [heq, hn0, hn1]
    · have hk1 : ¬k.val < n - 1 := by omega
      have hmod : (k.val - (n - 2)) % 2 ≠ 0 := by omega
      simp [hk2, heq, hk1, hk, hmod]

/-- Nonnegative prefixes eliminate the remaining one-dimensional kernel. -/
theorem comparisonMatrix_kernel_eq_zero_of_prefix_nonneg {n : ℕ} (hn : 2 ≤ n)
    (x : Fin n → ℝ) (hprefix : PrefixDominated 0 x)
    (hker : comparisonMatrix n *ᵥ x = 0) : x = 0 := by
  have hfirst : prefixSum x (n - 1) = 0 := by
    have h := congrFun hker ⟨0, by omega⟩
    rw [comparisonMatrix_first_row (by omega) x] at h
    exact h
  have hsecond : prefixSum x (n - 2) + prefixSum x n = 0 := by
    have h := congrFun hker ⟨1, by omega⟩
    rw [comparisonMatrix_second_row hn x, hfirst, sub_zero] at h
    exact h
  have hpn : 0 ≤ prefixSum x n := by simpa [prefixSum] using hprefix n le_rfl
  have hpn2 : 0 ≤ prefixSum x (n - 2) := by
    simpa [prefixSum] using hprefix (n - 2) (by omega)
  apply comparisonMatrix_kernel_eq_zero_of_sum_eq_zero x hker
  rw [← prefixSum_full]
  linarith

/-- Equality after one comparison step is strict under prefix domination.
No ordering or coordinatewise sign assumption on either vector is needed. -/
theorem comparisonMatrix_eq_of_prefixDominated {n : ℕ} (hn : 2 ≤ n)
    (u v : Fin n → ℝ) (huv : PrefixDominated u v)
    (heq : comparisonMatrix n *ᵥ u = comparisonMatrix n *ᵥ v) : u = v := by
  have hprefix : PrefixDominated 0 (v - u) := by
    intro r hr
    have h := huv r hr
    simpa [prefixSum, Pi.sub_apply, Finset.sum_sub_distrib] using sub_nonneg.mpr h
  have hker : comparisonMatrix n *ᵥ (v - u) = 0 := by
    rw [Matrix.mulVec_sub, ← heq, sub_self]
  have hz := comparisonMatrix_kernel_eq_zero_of_prefix_nonneg hn (v - u) hprefix hker
  funext j
  have hj := congrFun hz j
  exact (sub_eq_zero.mp hj).symm

end
end Wormald
