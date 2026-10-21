import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-!
# The transitive sign-matrix determinant

The proof uses a rank-one update and two triangular matrices. Adding the
constant matrix tJ to I+tT produces an upper triangular matrix with diagonal
1+t; subtracting tJ produces a lower triangular matrix with diagonal 1−t.
A determinant is affine along a rank-one update, so the two triangular
determinants add to twice the middle determinant.
-/

namespace Wormald

noncomputable section
open Matrix

private theorem det_rankOne_affine {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin n) (Fin 1) K)
    (C : Matrix (Fin 1) (Fin n) K) (hA : IsUnit A.det) (c : K) :
    (A + c • (B * C)).det = A.det * (1 + c * (C * A⁻¹ * B) 0 0) := by
  rw [← Matrix.smul_mul, Matrix.det_add_mul (c • B) C hA, Matrix.det_fin_one]
  simp only [Matrix.mul_smul, Matrix.add_apply, Matrix.one_apply_eq,
    Matrix.smul_apply, smul_eq_mul]

/-- The transitive tournament sign matrix: upper entries 1, lower entries −1. -/
def transitiveSign (n : ℕ) (K : Type*) [Zero K] [One K] [Neg K] :
    Matrix (Fin n) (Fin n) K :=
  fun i j => if i < j then 1 else if j < i then -1 else 0

private def transitivePencil {K : Type*} [Field K] (n : ℕ) (t : K) :
    Matrix (Fin n) (Fin n) K :=
  fun i j => if i = j then 1 else if i < j then t else -t

private def upperPencil {K : Type*} [Field K] (n : ℕ) (t : K) :
    Matrix (Fin n) (Fin n) K :=
  fun i j => if i = j then 1 + t else if i < j then 2 * t else 0

private def lowerPencil {K : Type*} [Field K] (n : ℕ) (t : K) :
    Matrix (Fin n) (Fin n) K :=
  fun i j => if i = j then 1 - t else if j < i then -(2 * t) else 0

private theorem det_upperPencil {K : Type*} [Field K] (n : ℕ) (t : K) :
    (upperPencil n t).det = (1 + t) ^ n := by
  have hu : (upperPencil n t).IsUpperTriangular := by
    intro i j hji
    change j < i at hji
    simp [upperPencil, ne_of_gt hji, not_lt_of_gt hji]
  rw [Matrix.det_of_isUpperTriangular hu]
  simp [upperPencil]

private theorem det_lowerPencil {K : Type*} [Field K] (n : ℕ) (t : K) :
    (lowerPencil n t).det = (1 - t) ^ n := by
  have hl : (lowerPencil n t).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    simp [lowerPencil, ne_of_lt hij, not_lt_of_gt hij]
  rw [Matrix.det_of_isLowerTriangular _ hl]
  simp [lowerPencil]

private theorem det_transitivePencil_of_ne {K : Type*} [Field K] [CharZero K]
    (n : ℕ) (t : K) (ht : 1 + t ≠ 0) :
    (transitivePencil n t).det = ((1 + t) ^ n + (1 - t) ^ n) / 2 := by
  let B : Matrix (Fin n) (Fin 1) K := fun _ _ => t
  let C : Matrix (Fin 1) (Fin n) K := fun _ _ => 1
  have hA : IsUnit (upperPencil n t).det := by
    rw [det_upperPencil]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero n ht)
  have hBC : ∀ i j, (B * C) i j = t := by
    intro i j
    change (∑ k : Fin 1, t * 1) = t
    simp
  have hmid : upperPencil n t + (-1 : K) • (B * C) = transitivePencil n t := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hBC, upperPencil, transitivePencil]
    split_ifs <;> ring
  have hlow : upperPencil n t + (-2 : K) • (B * C) = lowerPencil n t := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hBC, upperPencil, lowerPencil]
    by_cases heq : i = j
    · simp [heq]
      ring
    · by_cases hij : i < j
      · simp [heq, hij, not_lt_of_gt hij]
      · have hji : j < i := by omega
        simp [heq, hij, hji]
  have h1 := det_rankOne_affine (upperPencil n t) B C hA (-1)
  have h2 := det_rankOne_affine (upperPencil n t) B C hA (-2)
  rw [hmid, det_upperPencil] at h1
  rw [hlow, det_upperPencil, det_lowerPencil] at h2
  apply (eq_div_iff (two_ne_zero : (2 : K) ≠ 0)).2
  linear_combination 2 * h1 - h2

private theorem transitivePencil_transpose {K : Type*} [Field K] (n : ℕ) (t : K) :
    (transitivePencil n t).transpose = transitivePencil n (-t) := by
  ext i j
  simp only [Matrix.transpose_apply, transitivePencil]
  by_cases heq : i = j
  · simp [heq]
  · by_cases hij : i < j
    · simp [heq, Ne.symm heq, hij, not_lt_of_gt hij]
    · have hji : j < i := by omega
      simp [heq, Ne.symm heq, hij, hji]

/-- The determinant polynomial of the transitive sign matrix, in any characteristic-zero field. -/
theorem det_one_add_smul_transitiveSign {K : Type*} [Field K] [CharZero K]
    (n : ℕ) (t : K) :
    (1 + t • transitiveSign n K).det = ((1 + t) ^ n + (1 - t) ^ n) / 2 := by
  have hpencil : 1 + t • transitiveSign n K = transitivePencil n t := by
    ext i j
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
      transitiveSign, transitivePencil]
    by_cases heq : i = j
    · simp [heq]
    · by_cases hij : i < j
      · simp [heq, hij]
      · have hji : j < i := by omega
        simp [heq, hij, hji]
  rw [hpencil]
  by_cases ht : 1 + t ≠ 0
  · exact det_transitivePencil_of_ne n t ht
  · have hz : 1 + t = 0 := not_ne_iff.mp ht
    have htneg : 1 + (-t) ≠ 0 := by
      intro h
      apply (two_ne_zero : (2 : K) ≠ 0)
      linear_combination h + hz
    have hdet : (transitivePencil n t).det = (transitivePencil n (-t)).det := by
      rw [← transitivePencil_transpose, Matrix.det_transpose]
    rw [hdet, det_transitivePencil_of_ne n (-t) htneg]
    ring

end
end Wormald
