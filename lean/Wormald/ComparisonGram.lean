import Wormald.ComparisonTransitive

namespace Wormald

noncomputable section
open Matrix Finset

theorem comparisonMatrix_transpose (n : ℕ) :
    (comparisonMatrix n).transpose = comparisonMatrix n := by
  ext i j
  exact comparisonMatrix_symmetric n j i

theorem transitiveSign_transpose (n : ℕ) :
    (transitiveSign n ℝ).transpose = -transitiveSign n ℝ := by
  ext i j
  rcases lt_trichotomy i j with hij | heq | hji
  · simp [transitiveSign, hij, not_lt_of_gt hij]
  · subst j
    simp [transitiveSign]
  · simp [transitiveSign, hji, not_lt_of_gt hji]

/-- A finite column energy is the corresponding diagonal entry of a Gram power,
provided the matrix commutes with its transpose. -/
theorem pow_column_energy_eq_gram {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hcomm : Commute M.transpose M) (p : ℕ) (j : Fin n) :
    (∑ i, (M ^ p) i j ^ 2) = ((M.transpose * M) ^ p) j j := by
  rw [hcomm.mul_pow, ← Matrix.transpose_pow]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, pow_two]

theorem comparison_pow_column_energy (n p : ℕ) (j : Fin n) :
    (∑ i, (comparisonMatrix n ^ p) i j ^ 2) =
      (comparisonMatrix n ^ (2 * p)) j j := by
  have hcomm : Commute (comparisonMatrix n).transpose (comparisonMatrix n) := by
    rw [comparisonMatrix_transpose]
  rw [pow_column_energy_eq_gram _ hcomm, comparisonMatrix_transpose, ← pow_two, ← pow_mul]

theorem transitive_pow_column_energy_gram (n p : ℕ) (j : Fin n) :
    (∑ i, (transitiveSign n ℝ ^ p) i j ^ 2) =
      ((transitiveSign n ℝ * (transitiveSign n ℝ).transpose) ^ p) j j := by
  have hcomm : Commute (transitiveSign n ℝ).transpose (transitiveSign n ℝ) := by
    rw [transitiveSign_transpose]
    change (-transitiveSign n ℝ) * transitiveSign n ℝ =
      transitiveSign n ℝ * (-transitiveSign n ℝ)
    simp
  rw [pow_column_energy_eq_gram _ hcomm, hcomm.eq]

theorem comparisonShuffle_zero {n : ℕ} (hn : 0 < n) :
    comparisonShuffle n ⟨0, hn⟩ = ⟨0, hn⟩ := by
  apply Fin.ext
  simp [comparisonShuffle, hn]

/-- The comparison bound at the first basis vector is exactly the genuine
transitive tournament's column energy, at every natural exponent. -/
theorem comparison_column_energy_zero (n : ℕ) (hn : 0 < n) (p : ℕ) :
    (∑ i, (comparisonMatrix n ^ p) i ⟨0, hn⟩ ^ 2) =
      ∑ i, (transitiveSign n ℝ ^ p) i ⟨0, hn⟩ ^ 2 := by
  rw [comparison_pow_column_energy, transitive_pow_column_energy_gram,
    transitive_gram_pow_eq_comparisonConjugate]
  simp [comparisonConjugate, comparisonShuffle_zero hn, comparisonSign]

end
end Wormald
