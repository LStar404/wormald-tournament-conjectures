import Wormald.MarkovCriticalBridge
import Mathlib.LinearAlgebra.Matrix.Stochastic

/-! Explicit finite mixing for the actual regular tournament transition.
The real matrix below maps exactly to `criticalTransition` and to the finite
counting model's `markovBase`; no auxiliary transition is postulated. -/

namespace Wormald

noncomputable section
open Matrix
open scoped BigOperators

def Tournament.realCriticalTransition {n : ℕ} (T : Tournament n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (1 + (T.sign i j : ℝ)) / (n : ℝ)

theorem Tournament.realCriticalTransition_map {n : ℕ} (T : Tournament n) :
    T.realCriticalTransition.map Complex.ofRealHom = T.criticalTransition := by
  ext i j
  change (((1 + (T.sign i j : ℝ)) / (n : ℝ) : ℝ) : ℂ) =
    1 / (n : ℂ) + ((T.sign i j / (n : ℚ) : ℚ) : ℂ)
  push_cast
  ring

theorem FiniteModel.markovBase_eq_realCriticalTransition {n : ℕ}
    (base : FiniteModel.Orientation n) :
    FiniteModel.markovBase base = (FiniteModel.toTournament base).realCriticalTransition := by
  have h := FiniteModel.markovBase_map_eq_criticalTransition base
  rw [← (FiniteModel.toTournament base).realCriticalTransition_map] at h
  ext i j
  exact Complex.ofReal_injective (congrFun (congrFun h i) j)

@[simp] theorem Tournament.real_sign_diagonal {n : ℕ} (T : Tournament n) (i : Fin n) :
    (T.sign i i : ℝ) = 0 := by simp [Tournament.sign, T.diagonal]

theorem Tournament.real_sign_skew {n : ℕ} (T : Tournament n) (i j : Fin n) :
    (T.sign j i : ℝ) = -(T.sign i j : ℝ) := by
  exact_mod_cast congrFun (congrFun T.sign_skew i) j

theorem Tournament.real_sign_sq_le_one {n : ℕ} (T : Tournament n) (i j : Fin n) :
    (T.sign i j : ℝ) ^ 2 ≤ 1 := by
  have h := T.sign_entry_square i j
  by_cases hij : i = j
  · subst j; simp
  · have h' : (T.sign i j : ℝ) ^ 2 = 1 := by exact_mod_cast (by simpa [hij] using h)
    exact h'.le

theorem Tournament.realCriticalTransition_nonneg {n : ℕ} (T : Tournament n) (i j : Fin n) :
    0 ≤ T.realCriticalTransition i j := by
  apply div_nonneg _ (Nat.cast_nonneg n)
  nlinarith [T.real_sign_sq_le_one i j]

theorem Tournament.real_sign_row_sum {n : ℕ} (T : Tournament n) (hT : T.Regular)
    (i : Fin n) : (∑ j, (T.sign i j : ℝ)) = 0 := by
  exact_mod_cast T.sign_row_sum hT i

theorem Tournament.real_sign_col_sum {n : ℕ} (T : Tournament n) (hT : T.Regular)
    (j : Fin n) : (∑ i, (T.sign i j : ℝ)) = 0 := by
  simp only [T.real_sign_skew j, Finset.sum_neg_distrib, T.real_sign_row_sum hT j, neg_zero]

theorem Tournament.realCriticalTransition_row_sum {n : ℕ} (T : Tournament n)
    (hn : n ≠ 0) (hT : T.Regular) (i : Fin n) :
    (∑ j, T.realCriticalTransition i j) = 1 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp [Tournament.realCriticalTransition, ← Finset.sum_div, Finset.sum_add_distrib,
    T.real_sign_row_sum hT i, hnR]

theorem Tournament.realCriticalTransition_col_sum {n : ℕ} (T : Tournament n)
    (hn : n ≠ 0) (hT : T.Regular) (j : Fin n) :
    (∑ i, T.realCriticalTransition i j) = 1 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp [Tournament.realCriticalTransition, ← Finset.sum_div, Finset.sum_add_distrib,
    T.real_sign_col_sum hT j, hnR]

theorem Tournament.realCriticalTransition_rowStochastic {n : ℕ} (T : Tournament n)
    (hn : n ≠ 0) (hT : T.Regular) : T.realCriticalTransition ∈ Matrix.rowStochastic ℝ (Fin n) :=
  Matrix.mem_rowStochastic_iff_sum.mpr
    ⟨T.realCriticalTransition_nonneg, T.realCriticalTransition_row_sum hn hT⟩

theorem Tournament.realCriticalTransition_colStochastic {n : ℕ} (T : Tournament n)
    (hn : n ≠ 0) (hT : T.Regular) : T.realCriticalTransition ∈ Matrix.colStochastic ℝ (Fin n) :=
  Matrix.mem_colStochastic_iff_sum.mpr
    ⟨T.realCriticalTransition_nonneg, T.realCriticalTransition_col_sum hn hT⟩

theorem Tournament.realCriticalTransition_sq_apply {n : ℕ} (T : Tournament n)
    (hT : T.Regular) (i j : Fin n) :
    (T.realCriticalTransition ^ 2) i j =
      ((n : ℝ) + ∑ k, (T.sign i k : ℝ) * (T.sign k j : ℝ)) / (n : ℝ) ^ 2 := by
  rw [pow_two, Matrix.mul_apply]
  simp only [Tournament.realCriticalTransition, div_mul_div_comm, ← Finset.sum_div, ← sq]
  congr 1
  simp only [add_mul, mul_add, one_mul, mul_one, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, T.real_sign_row_sum hT i, T.real_sign_col_sum hT j]
  ring

theorem Tournament.realCriticalTransition_sq_diagonal {n : ℕ} (T : Tournament n)
    (hT : T.Regular) (i : Fin n) :
    (T.realCriticalTransition ^ 2) i i = 1 / (n : ℝ) ^ 2 := by
  rw [T.realCriticalTransition_sq_apply hT]
  have hsum : (∑ k, (T.sign i k : ℝ) * (T.sign k i : ℝ)) = -((n : ℝ) - 1) := by
    have he : (∑ k, (T.sign i k : ℝ) ^ 2) = (n : ℝ) - 1 := by
      exact_mod_cast T.sign_row_energy i
    simp only [T.real_sign_skew i, mul_neg, ← sq, Finset.sum_neg_distrib, he]
  rw [hsum]
  congr 1
  ring

/-- Off-diagonal entries of the two-step transition have twice the common
minorization mass; the two excluded sign products are both exactly zero. -/
theorem Tournament.realCriticalTransition_sq_offdiag {n : ℕ} (T : Tournament n)
    (hT : T.Regular) (i j : Fin n) (hij : i ≠ j) :
    2 / (n : ℝ) ^ 2 ≤ (T.realCriticalTransition ^ 2) i j := by
  have hterm (k : Fin n) :
      -1 + (if k = i then (1 : ℝ) else 0) + (if k = j then 1 else 0) ≤
        (T.sign i k : ℝ) * (T.sign k j : ℝ) := by
    by_cases hki : k = i
    · subst k; simp [hij]
    by_cases hkj : k = j
    · subst k; simp [Ne.symm hij]
    simp only [ite_eq_right hki, ite_eq_right hkj, add_zero]
    nlinarith [T.real_sign_sq_le_one i k, T.real_sign_sq_le_one k j,
      sq_nonneg ((T.sign i k : ℝ) + (T.sign k j : ℝ))]
  have hsum : -(n : ℝ) + 2 ≤ ∑ k, (T.sign i k : ℝ) * (T.sign k j : ℝ) := by
    have hh := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hterm k)
    simp [Finset.sum_add_distrib] at hh
    linarith
  rw [T.realCriticalTransition_sq_apply hT]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  linarith

theorem Tournament.realCriticalTransition_sq_lower {n : ℕ} (T : Tournament n)
    (hT : T.Regular) (i j : Fin n) :
    1 / (n : ℝ) ^ 2 ≤ (T.realCriticalTransition ^ 2) i j := by
  by_cases hij : i = j
  · subst j; exact (T.realCriticalTransition_sq_diagonal hT i).ge
  · exact (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (sq_nonneg _)).trans
      (T.realCriticalTransition_sq_offdiag hT i j hij)

def uniformTransition (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun _ _ => 1 / (n : ℝ)

def Tournament.doeblinRemainder {n : ℕ} (T : Tournament n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ((T.realCriticalTransition ^ 2) i j - 1 / (n : ℝ) ^ 2) / (1 - 1 / (n : ℝ))

theorem one_sub_inv_nat_pos {n : ℕ} (hn : 1 < n) : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := lt_trans zero_lt_one hnR
  have hi : 1 / (n : ℝ) < 1 := (div_lt_one hp).mpr hnR
  linarith

theorem Tournament.doeblinRemainder_nonneg {n : ℕ} (T : Tournament n)
    (hn : 1 < n) (hT : T.Regular) (i j : Fin n) : 0 ≤ T.doeblinRemainder i j :=
  div_nonneg (sub_nonneg.mpr (T.realCriticalTransition_sq_lower hT i j))
    (one_sub_inv_nat_pos hn).le

theorem sum_uniform_square_mass {n : ℕ} (hn : n ≠ 0) :
    (∑ _j : Fin n, 1 / (n : ℝ) ^ 2) = 1 / (n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem Tournament.doeblinRemainder_row_sum {n : ℕ} (T : Tournament n)
    (hn : 1 < n) (hT : T.Regular) (i : Fin n) :
    (∑ j, T.doeblinRemainder i j) = 1 := by
  have hn0 : n ≠ 0 := by omega
  have hp := (Matrix.rowStochastic ℝ (Fin n)).pow_mem
    (T.realCriticalTransition_rowStochastic hn0 hT) 2
  simp only [Tournament.doeblinRemainder, ← Finset.sum_div, Finset.sum_sub_distrib,
    Matrix.sum_row_of_mem_rowStochastic hp i, sum_uniform_square_mass hn0]
  exact div_self (one_sub_inv_nat_pos hn).ne'

theorem Tournament.doeblinRemainder_col_sum {n : ℕ} (T : Tournament n)
    (hn : 1 < n) (hT : T.Regular) (j : Fin n) :
    (∑ i, T.doeblinRemainder i j) = 1 := by
  have hn0 : n ≠ 0 := by omega
  have hp := (Matrix.colStochastic ℝ (Fin n)).pow_mem
    (T.realCriticalTransition_colStochastic hn0 hT) 2
  simp only [Tournament.doeblinRemainder, ← Finset.sum_div, Finset.sum_sub_distrib,
    Matrix.sum_col_of_mem_colStochastic hp j, sum_uniform_square_mass hn0]
  exact div_self (one_sub_inv_nat_pos hn).ne'

theorem Tournament.doeblinRemainder_rowStochastic {n : ℕ} (T : Tournament n)
    (hn : 1 < n) (hT : T.Regular) : T.doeblinRemainder ∈ Matrix.rowStochastic ℝ (Fin n) :=
  Matrix.mem_rowStochastic_iff_sum.mpr
    ⟨T.doeblinRemainder_nonneg hn hT, T.doeblinRemainder_row_sum hn hT⟩

/-- The explicit Doeblin mass is `epsilon = 1/n`; the remaining matrix is
itself nonnegative and doubly stochastic. -/
theorem Tournament.realCriticalTransition_sq_doeblin {n : ℕ} (T : Tournament n)
    (hn : 1 < n) :
    T.realCriticalTransition ^ 2 = (1 / (n : ℝ)) • uniformTransition n +
      (1 - 1 / (n : ℝ)) • T.doeblinRemainder := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, uniformTransition,
    Tournament.doeblinRemainder]
  rw [mul_div_cancel₀ _ (one_sub_inv_nat_pos hn).ne']
  ring

end
end Wormald
