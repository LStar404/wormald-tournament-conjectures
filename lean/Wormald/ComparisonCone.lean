import Wormald.ComparisonMatrixEntries

/-!
# The comparison operator preserves decreasing nonnegative vectors

Symmetry identifies each row-prefix with the column-prefix weights. Their
nonnegativity and monotonicity, followed by finite Abel summation, give the
two assertions without a separate alternating-sum computation.
-/

namespace Wormald
noncomputable section
open scoped BigOperators
open Matrix

theorem prefixSum_comparisonMatrix_row {n : ℕ} (i : Fin n)
    (r : ℕ) (hr : r ≤ n) :
    prefixSum (fun j => comparisonMatrix n i j) r = comparisonWeights n r i := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [prefixSum_succ _ r (by omega), ih (by omega), comparisonMatrix_symmetric]
    simp only [comparisonMatrix]
    ring

theorem comparisonMatrix_row_nonneg_prefix {n : ℕ} (i : Fin n) :
    PrefixDominated (fun _ => 0) (fun j => comparisonMatrix n i j) := by
  intro r hr
  rw [prefixSum_comparisonMatrix_row i r hr]
  simpa [prefixSum] using comparisonWeights_nonneg n r hr i

theorem comparisonMatrix_rows_prefixDominated {n : ℕ} (i j : Fin n) (hij : i ≤ j) :
    PrefixDominated (fun k => comparisonMatrix n j k) (fun k => comparisonMatrix n i k) := by
  intro r hr
  rw [prefixSum_comparisonMatrix_row j r hr, prefixSum_comparisonMatrix_row i r hr]
  exact comparisonWeights_antitone n r hij

/-- Each coordinate of the comparison image is nonnegative on the decreasing
nonnegative cone. Individual matrix entries may have either sign. -/
theorem comparisonMatrix_mulVec_nonneg {n : ℕ} (x : Fin n → ℝ)
    (hx : Antitone x) (hx0 : ∀ j, 0 ≤ x j) (i : Fin n) :
    0 ≤ (comparisonMatrix n *ᵥ x) i := by
  have h := prefixDominated_weighted_sum_le (fun _ => 0)
    (fun j => comparisonMatrix n i j) x (comparisonMatrix_row_nonneg_prefix i) hx hx0
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h

/-- The comparison image remains decreasing. -/
theorem comparisonMatrix_mulVec_antitone {n : ℕ} (x : Fin n → ℝ)
    (hx : Antitone x) (hx0 : ∀ j, 0 ≤ x j) :
    Antitone (comparisonMatrix n *ᵥ x) := by
  intro i j hij
  have h := prefixDominated_weighted_sum_le (fun k => comparisonMatrix n j k)
    (fun k => comparisonMatrix n i k) x
    (comparisonMatrix_rows_prefixDominated i j hij) hx hx0
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h

end
end Wormald
