import Wormald.ComparisonMatrixEntries
import Mathlib.Data.Fin.Rev

namespace Wormald

noncomputable section
open Matrix Finset

/-- The vertex order 0,2,4,...,...,5,3,1 turns the signed reversal of K into T. -/
def comparisonShuffle (n : ℕ) : Equiv.Perm (Fin n) where
  toFun i := ⟨if 2 * i.val < n then 2 * i.val else 2 * (n - 1 - i.val) + 1, by
    have hi := i.isLt
    split_ifs <;> omega⟩
  invFun j := ⟨if j.val % 2 = 0 then j.val / 2 else n - 1 - j.val / 2, by
    have hj := j.isLt
    split_ifs <;> omega⟩
  left_inv i := by
    apply Fin.ext
    have hi := i.isLt
    dsimp
    split_ifs <;> omega
  right_inv j := by
    apply Fin.ext
    have hj := j.isLt
    dsimp
    split_ifs <;> omega

def comparisonSign {n : ℕ} (i : Fin n) : ℝ := if i.val % 2 = 0 then 1 else -1

@[simp] theorem comparisonSign_sq {n : ℕ} (i : Fin n) : comparisonSign i ^ 2 = 1 := by
  unfold comparisonSign
  split_ifs <;> norm_num

private theorem comparisonMatrix_rev (n : ℕ) (i j : Fin n) :
    comparisonMatrix n i j.rev =
      if i < j then 1 else if i = j then 0
      else if (i.val - j.val) % 2 = 0 then -1 else 1 := by
  rw [comparisonMatrix_entry]
  have hi := i.isLt
  have hj := j.isLt
  have hrev : j.rev.val = n - 1 - j.val := by simp [Fin.rev]; omega
  rw [hrev]
  simp only [Fin.lt_def, Fin.ext_iff]
  split_ifs <;> norm_num <;> omega

private theorem comparisonSign_mul_rev (n : ℕ) (i j : Fin n) :
    comparisonSign i * comparisonMatrix n i j.rev =
      if i < j then comparisonSign i else if i = j then 0 else -comparisonSign j := by
  rw [comparisonMatrix_rev]
  unfold comparisonSign
  simp only [Fin.lt_def, Fin.ext_iff]
  split_ifs <;> norm_num <;> omega

/-- The source's signed row/column permutation identity, for every dimension. -/
theorem comparisonMatrix_signed_reversal (n : ℕ) (i j : Fin n) :
    comparisonSign (comparisonShuffle n i) *
      comparisonMatrix n (comparisonShuffle n i) (comparisonShuffle n j).rev =
        transitiveSign n ℝ i j := by
  rw [comparisonSign_mul_rev]
  simp only [comparisonShuffle, Equiv.coe_fn_mk, comparisonSign, transitiveSign,
    Fin.lt_def, Fin.ext_iff]
  have hi := i.isLt
  have hj := j.isLt
  split_ifs <;> norm_num <;> omega

/-- Conjugation by the exact signed vertex permutation above. -/
def comparisonConjugate (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  comparisonSign (comparisonShuffle n i) * M (comparisonShuffle n i) (comparisonShuffle n j) *
    comparisonSign (comparisonShuffle n j)

theorem comparisonConjugate_mul (n : ℕ) (M N : Matrix (Fin n) (Fin n) ℝ) :
    comparisonConjugate n (M * N) = comparisonConjugate n M * comparisonConjugate n N := by
  ext i j
  simp only [comparisonConjugate, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [← Equiv.sum_comp (comparisonShuffle n)
    (fun k => comparisonSign (comparisonShuffle n i) *
      (M (comparisonShuffle n i) k * N k (comparisonShuffle n j)) *
      comparisonSign (comparisonShuffle n j))]
  apply Finset.sum_congr rfl
  intro k hk
  have hs : comparisonSign (comparisonShuffle n k) *
      comparisonSign (comparisonShuffle n k) = 1 := by
    simpa only [pow_two] using comparisonSign_sq (comparisonShuffle n k)
  calc
    _ = comparisonSign (comparisonShuffle n i) * M (comparisonShuffle n i) (comparisonShuffle n k) *
        (comparisonSign (comparisonShuffle n k) * comparisonSign (comparisonShuffle n k)) *
        N (comparisonShuffle n k) (comparisonShuffle n j) * comparisonSign (comparisonShuffle n j) := by
      rw [hs]
      ring
    _ = _ := by ring

@[simp] theorem comparisonConjugate_one (n : ℕ) :
    comparisonConjugate n 1 = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simpa [comparisonConjugate, Matrix.one_apply, pow_two] using
      comparisonSign_sq (comparisonShuffle n i)
  · have hp : comparisonShuffle n i ≠ comparisonShuffle n j :=
      (comparisonShuffle n).injective.ne hij
    simp [comparisonConjugate, hij, hp]

theorem comparisonConjugate_pow (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (p : ℕ) :
    comparisonConjugate n (M ^ p) = comparisonConjugate n M ^ p := by
  induction p with
  | zero => simp
  | succ p ih => rw [pow_succ, comparisonConjugate_mul, ih, pow_succ]

/-- The transitive and comparison Gram matrices are exactly signed-conjugate. -/
theorem transitive_gram_eq_comparisonConjugate (n : ℕ) :
    transitiveSign n ℝ * (transitiveSign n ℝ).transpose =
      comparisonConjugate n (comparisonMatrix n ^ 2) := by
  ext i j
  let q : Equiv.Perm (Fin n) := (comparisonShuffle n).trans Fin.revPerm
  simp only [Matrix.mul_apply, Matrix.transpose_apply, comparisonConjugate, pow_two,
    Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ k : Fin n, comparisonSign (comparisonShuffle n i) *
        (comparisonMatrix n (comparisonShuffle n i) (q k) *
          comparisonMatrix n (q k) (comparisonShuffle n j)) *
        comparisonSign (comparisonShuffle n j) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← comparisonMatrix_signed_reversal n i k,
        ← comparisonMatrix_signed_reversal n j k]
      change _ = comparisonSign (comparisonShuffle n i) *
        (comparisonMatrix n (comparisonShuffle n i) (comparisonShuffle n k).rev *
          comparisonMatrix n (comparisonShuffle n k).rev (comparisonShuffle n j)) *
        comparisonSign (comparisonShuffle n j)
      rw [comparisonMatrix_symmetric n (comparisonShuffle n k).rev]
      ring
    _ = _ := Equiv.sum_comp q (fun k => comparisonSign (comparisonShuffle n i) *
      (comparisonMatrix n (comparisonShuffle n i) k * comparisonMatrix n k (comparisonShuffle n j)) *
      comparisonSign (comparisonShuffle n j))

/-- Every Gram power, hence every even spectral moment, has the same conjugacy. -/
theorem transitive_gram_pow_eq_comparisonConjugate (n p : ℕ) :
    (transitiveSign n ℝ * (transitiveSign n ℝ).transpose) ^ p =
      comparisonConjugate n (comparisonMatrix n ^ (2 * p)) := by
  rw [transitive_gram_eq_comparisonConjugate, ← comparisonConjugate_pow, ← pow_mul]

end
end Wormald
