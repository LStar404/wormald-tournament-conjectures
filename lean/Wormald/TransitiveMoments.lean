import Wormald.ComparisonGram
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The signed cyclic symmetry of the actual transitive tournament matrix.
It makes the diagonal of every matrix power constant. -/

namespace Wormald
noncomputable section
open Matrix
open scoped BigOperators

def transitiveRotationSign (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  if i = Fin.last n then -1 else 1

theorem transitiveRotationSign_square (n : ℕ) (i : Fin (n + 1)) :
    transitiveRotationSign n i * transitiveRotationSign n i = 1 := by
  unfold transitiveRotationSign
  split_ifs <;> norm_num

/-- Rotation preserves the transitive matrix once the wrapping coordinate
changes sign. This is the entrywise form of the signed cyclic conjugacy. -/
theorem transitiveSign_rotate (n : ℕ) (i j : Fin (n + 1)) :
    transitiveSign (n + 1) ℝ (finRotate (n + 1) i) (finRotate (n + 1) j) =
      transitiveRotationSign n i * transitiveRotationSign n j *
        transitiveSign (n + 1) ℝ i j := by
  by_cases hi : i = Fin.last n
  · subst i
    by_cases hj : j = Fin.last n
    · subst j
      simp [transitiveSign, transitiveRotationSign]
    · have hjlast : j < Fin.last n := Fin.lt_last_iff_ne_last.mpr hj
      have hjrot : (0 : Fin (n + 1)) < finRotate (n + 1) j := by
        change 0 < ((finRotate (n + 1)) j).val
        rw [coe_finRotate_of_ne_last hj]
        exact Nat.succ_pos _
      rw [finRotate_last]
      simp only [transitiveSign, transitiveRotationSign, ite_eq_right hj,
        hjlast, not_lt_of_gt hjlast, hjrot, not_lt_of_gt hjrot, ite_true, ite_false]
      norm_num
  · by_cases hj : j = Fin.last n
    · subst j
      have hilast : i < Fin.last n := Fin.lt_last_iff_ne_last.mpr hi
      have hirot : (0 : Fin (n + 1)) < finRotate (n + 1) i := by
        change 0 < ((finRotate (n + 1)) i).val
        rw [coe_finRotate_of_ne_last hi]
        exact Nat.succ_pos _
      rw [finRotate_last]
      simp only [transitiveSign, transitiveRotationSign, ite_eq_right hi,
        hilast, not_lt_of_gt hilast, hirot, not_lt_of_gt hirot, ite_true, ite_false]
      norm_num
    · have hlt : finRotate (n + 1) i < finRotate (n + 1) j ↔ i < j := by
        simp only [Fin.lt_def, coe_finRotate_of_ne_last hi,
          coe_finRotate_of_ne_last hj]
        omega
      have hgt : finRotate (n + 1) j < finRotate (n + 1) i ↔ j < i := by
        simp only [Fin.lt_def, coe_finRotate_of_ne_last hi,
          coe_finRotate_of_ne_last hj]
        omega
      simp only [transitiveSign, transitiveRotationSign, ite_eq_right hi, ite_eq_right hj, hlt, hgt,
        one_mul]

private theorem signedRotation_mul (n : ℕ)
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : ∀ i j, A (finRotate (n + 1) i) (finRotate (n + 1) j) =
      transitiveRotationSign n i * transitiveRotationSign n j * A i j)
    (hB : ∀ i j, B (finRotate (n + 1) i) (finRotate (n + 1) j) =
      transitiveRotationSign n i * transitiveRotationSign n j * B i j) :
    ∀ i j, (A * B) (finRotate (n + 1) i) (finRotate (n + 1) j) =
      transitiveRotationSign n i * transitiveRotationSign n j * (A * B) i j := by
  intro i j
  calc
    (A * B) (finRotate (n + 1) i) (finRotate (n + 1) j) =
        ∑ k, A (finRotate (n + 1) i) (finRotate (n + 1) k) *
          B (finRotate (n + 1) k) (finRotate (n + 1) j) :=
      (Equiv.sum_comp (finRotate (n + 1)) _).symm
    _ = ∑ k, transitiveRotationSign n i * transitiveRotationSign n j * (A i k * B k j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hA, hB]
      calc
        _ = (transitiveRotationSign n i * transitiveRotationSign n j * (A i k * B k j)) *
            (transitiveRotationSign n k * transitiveRotationSign n k) := by ring
        _ = _ := by rw [transitiveRotationSign_square, mul_one]
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem transitiveSign_pow_rotate (n p : ℕ) (i j : Fin (n + 1)) :
    (transitiveSign (n + 1) ℝ ^ p) (finRotate (n + 1) i) (finRotate (n + 1) j) =
      transitiveRotationSign n i * transitiveRotationSign n j *
        (transitiveSign (n + 1) ℝ ^ p) i j := by
  induction p generalizing i j with
  | zero =>
      by_cases hij : i = j
      · subst j
        simp [transitiveRotationSign_square]
      · simp [hij]
  | succ p ih =>
      rw [pow_succ]
      exact signedRotation_mul n _ _ ih (transitiveSign_rotate n) i j

theorem transitiveSign_pow_diagonal_rotate (n p : ℕ) (i : Fin (n + 1)) :
    (transitiveSign (n + 1) ℝ ^ p) (finRotate (n + 1) i) (finRotate (n + 1) i) =
      (transitiveSign (n + 1) ℝ ^ p) i i := by
  simpa only [transitiveRotationSign_square, one_mul] using transitiveSign_pow_rotate n p i i

private theorem transitiveSign_pow_diagonal_zero (n p : ℕ) (i : Fin (n + 1)) :
    (transitiveSign (n + 1) ℝ ^ p) i i = (transitiveSign (n + 1) ℝ ^ p) 0 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
      have hrot : finRotate (n + 1) i.castSucc = i.succ := by
        apply Fin.ext
        rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last i)]
        rfl
      have h := transitiveSign_pow_diagonal_rotate n p i.castSucc
      rw [hrot] at h
      exact h.trans ih

/-- Every power of the actual transitive sign matrix has a constant diagonal. -/
theorem transitiveSign_pow_diagonal_eq (n p : ℕ) (i j : Fin n) :
    (transitiveSign n ℝ ^ p) i i = (transitiveSign n ℝ ^ p) j j := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
      exact (transitiveSign_pow_diagonal_zero n p i).trans
        (transitiveSign_pow_diagonal_zero n p j).symm

theorem transitive_pow_column_energy_rotate (n p : ℕ) (j : Fin (n + 1)) :
    (∑ i, (transitiveSign (n + 1) ℝ ^ p) i (finRotate (n + 1) j) ^ 2) =
      ∑ i, (transitiveSign (n + 1) ℝ ^ p) i j ^ 2 := by
  calc
    _ = ∑ i, (transitiveSign (n + 1) ℝ ^ p)
        (finRotate (n + 1) i) (finRotate (n + 1) j) ^ 2 :=
      (Equiv.sum_comp (finRotate (n + 1)) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [transitiveSign_pow_rotate]
      calc
        _ = (transitiveRotationSign n i * transitiveRotationSign n i) *
          (transitiveRotationSign n j * transitiveRotationSign n j) *
          ((transitiveSign (n + 1) ℝ ^ p) i j ^ 2) := by ring
        _ = _ := by rw [transitiveRotationSign_square, transitiveRotationSign_square]; ring

private theorem transitive_pow_column_energy_zero (n p : ℕ) (j : Fin (n + 1)) :
    (∑ i, (transitiveSign (n + 1) ℝ ^ p) i j ^ 2) =
      ∑ i, (transitiveSign (n + 1) ℝ ^ p) i 0 ^ 2 := by
  induction j using Fin.induction with
  | zero => rfl
  | succ j ih =>
      have hrot : finRotate (n + 1) j.castSucc = j.succ := by
        apply Fin.ext
        rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last j)]
        rfl
      have h := transitive_pow_column_energy_rotate n p j.castSucc
      rw [hrot] at h
      exact h.trans ih

/-- Every power has the same squared Euclidean norm in every column. -/
theorem transitive_pow_column_energy_eq (n p : ℕ) (i j : Fin n) :
    (∑ k, (transitiveSign n ℝ ^ p) k i ^ 2) =
      ∑ k, (transitiveSign n ℝ ^ p) k j ^ 2 := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
      exact (transitive_pow_column_energy_zero n p i).trans
        (transitive_pow_column_energy_zero n p j).symm

end
end Wormald
