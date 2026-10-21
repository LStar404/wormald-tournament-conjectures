import Wormald.ComparisonMatrix

namespace Wormald

noncomputable section

/-- The prefix-difference definition is precisely the source's symmetric
anti-triangular sign matrix: ones, a zero anti-diagonal, and alternating signs. -/
theorem comparisonMatrix_entry (n : ℕ) (i j : Fin n) :
    comparisonMatrix n i j =
      if j.val < n - 1 - i.val then 1
      else if j.val = n - 1 - i.val then 0
      else if (j.val - (n - 1 - i.val)) % 2 = 0 then -1 else 1 := by
  have hi := i.isLt
  have hL1 : n - (i.val + 1) = n - 1 - i.val := by omega
  have hL0 : n - i.val = n - 1 - i.val + 1 := by omega
  by_cases hj : j.val < n - 1 - i.val
  · have hj0 : j.val < n - 1 - i.val + 1 := by omega
    simp only [comparisonMatrix, comparisonWeights, hL1, hL0,
      ite_eq_left hj, ite_eq_left hj0]
    push_cast
    ring
  · by_cases heq : j.val = n - 1 - i.val
    · have hj0 : j.val < n - 1 - i.val + 1 := by omega
      simp [comparisonMatrix, comparisonWeights, hL1, hL0, heq]
    · have hj0 : ¬j.val < n - 1 - i.val + 1 := by omega
      simp only [comparisonMatrix, comparisonWeights, hL1, hL0,
        ite_eq_right hj, ite_eq_right hj0, ite_eq_right heq]
      by_cases hpar : (j.val - (n - 1 - i.val)) % 2 = 0
      · have hdiv : (j.val - (n - 1 - i.val)) / 2 =
            (j.val - (n - 1 - i.val + 1)) / 2 + 1 := by omega
        rw [ite_eq_left hpar, hdiv]
        push_cast
        ring
      · have hdiv : (j.val - (n - 1 - i.val)) / 2 =
            (j.val - (n - 1 - i.val + 1)) / 2 := by omega
        rw [ite_eq_right hpar, hdiv]
        push_cast
        ring

/-- The comparison matrix is symmetric, so its row-prefix sums are the already
verified nonnegative decreasing column-prefix weights. -/
theorem comparisonMatrix_symmetric (n : ℕ) (i j : Fin n) :
    comparisonMatrix n i j = comparisonMatrix n j i := by
  rw [comparisonMatrix_entry, comparisonMatrix_entry]
  have hi := i.isLt
  have hj := j.isLt
  split_ifs <;> norm_num <;> omega

end
end Wormald
