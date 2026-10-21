import Wormald.Compression
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic

open Matrix
open scoped BigOperators

namespace Wormald

private def borderBasis (n : ℕ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks 1 (Matrix.of fun _ _ => 1) (Matrix.of fun _ _ => -1) 1

private def borderEmbedding (n : ℕ) : Matrix (Fin n ⊕ Fin 1) (Fin n) ℝ :=
  fun i j => Sum.elim (fun a => if a = j then 1 else 0) (fun _ => -1) i

private theorem det_borderBasis (n : ℕ) : (borderBasis n).det = (n : ℝ) + 1 := by
  rw [borderBasis, Matrix.det_fromBlocks_one₁₁, Matrix.det_unique]
  simp [Matrix.sub_apply, Matrix.mul_apply, add_comm]

private theorem borderBasis_left (n : ℕ) (i : Fin n ⊕ Fin 1) (j : Fin n) :
    borderBasis n i (Sum.inl j) = borderEmbedding n i j := by
  cases i <;> simp [borderBasis, borderEmbedding, Matrix.one_apply]

private theorem borderBasis_right (n : ℕ) (i : Fin n ⊕ Fin 1) (j : Fin 1) :
    borderBasis n i (Sum.inr j) = 1 := by
  cases i with
  | inl i => rfl
  | inr i =>
    change (1 : Matrix (Fin 1) (Fin 1) ℝ) i j = 1
    have hij : i = j := Subsingleton.elim _ _
    subst j
    exact Matrix.one_apply_eq i

private theorem borderEmbedding_sum (n : ℕ) (j : Fin n) :
    (∑ i, borderEmbedding n i j) = 0 := by
  simp [borderEmbedding, Fintype.sum_sum_type]

private theorem borderBasis_mul_right (n : ℕ)
    (Q : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (hQ : Q *ᵥ (fun _ => 1) = (fun _ => 1))
    (i : Fin n ⊕ Fin 1) (j : Fin 1) :
    (Q * borderBasis n) i (Sum.inr j) = 1 := by
  simpa [Matrix.mul_apply, borderBasis_right, Matrix.mulVec, dotProduct]
    using congrFun hQ i

private theorem border_embedding_reindex (n : ℕ) :
    borderEmbedding n = (coordinateEmbedding n).submatrix finSumFinEquiv id := by
  ext i j
  cases i with
  | inl i =>
    have hi : Fin.castAdd 1 i = i.castSucc := rfl
    simp [borderEmbedding, coordinateEmbedding, Matrix.submatrix_apply, hi]
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change -1 = if Fin.last n = j.castSucc then 1 else if Fin.last n = Fin.last n then -1 else 0
    have hl : Fin.last n ≠ j.castSucc := ne_of_gt (Fin.castSucc_lt_last j)
    simp [hl]

private theorem border_congruence (n : ℕ)
    (Q : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (hQsym : Q.transpose = Q)
    (hQ : Q *ᵥ (fun _ => 1) = (fun _ => 1)) :
    (borderBasis n).transpose * Q * borderBasis n =
      Matrix.fromBlocks ((borderEmbedding n).transpose * Q * borderEmbedding n)
        0 0 (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (n : ℝ) + 1) := by
  let M := (borderBasis n).transpose * Q * borderBasis n
  have hsymM : M.transpose = M := by
    dsimp [M]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hQsym, Matrix.mul_assoc]
  have hleft (i j : Fin n) :
      M (Sum.inl i) (Sum.inl j) =
        ((borderEmbedding n).transpose * Q * borderEmbedding n) i j := by
    simp only [M, Matrix.mul_apply, Matrix.transpose_apply, borderBasis_left]
  have hright (i : Fin n) (j : Fin 1) : M (Sum.inl i) (Sum.inr j) = 0 := by
    dsimp [M]
    rw [Matrix.mul_assoc]
    change ((borderBasis n).transpose * (Q * borderBasis n)) (Sum.inl i) (Sum.inr j) = 0
    change (∑ k, borderBasis n k (Sum.inl i) *
      (Q * borderBasis n) k (Sum.inr j)) = 0
    simp only [borderBasis_mul_right n Q hQ, mul_one, borderBasis_left]
    exact borderEmbedding_sum n i
  have hbottom (i j : Fin 1) : M (Sum.inr i) (Sum.inr j) = (n : ℝ) + 1 := by
    dsimp [M]
    rw [Matrix.mul_assoc]
    change ((borderBasis n).transpose * (Q * borderBasis n)) (Sum.inr i) (Sum.inr j) = _
    change (∑ k, borderBasis n k (Sum.inr i) *
      (Q * borderBasis n) k (Sum.inr j)) = _
    simp only [borderBasis_mul_right n Q hQ, borderBasis_right, mul_one]
    simp
  change M = _
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => exact hleft i j
    | inr j => exact hright i j
  | inr i =>
    cases j with
    | inl j =>
      change M (Sum.inr i) (Sum.inl j) = 0
      exact (congrFun (congrFun hsymM (Sum.inl j)) (Sum.inr i)).trans (hright j i)
    | inr j => exact hbottom i j

private theorem det_border_compression (n : ℕ)
    (Q : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (hQsym : Q.transpose = Q)
    (hQ : Q *ᵥ (fun _ => 1) = (fun _ => 1)) :
    ((borderEmbedding n).transpose * Q * borderEmbedding n).det =
      ((n : ℝ) + 1) * Q.det := by
  have hd : (n : ℝ) + 1 ≠ 0 := by positivity
  apply mul_right_cancel₀ hd
  calc
    ((borderEmbedding n).transpose * Q * borderEmbedding n).det * ((n : ℝ) + 1) =
        ((borderBasis n).transpose * Q * borderBasis n).det := by
      rw [border_congruence n Q hQsym hQ, Matrix.det_fromBlocks_zero₂₁]
      rw [Matrix.det_unique (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (n : ℝ) + 1)]
      rfl
    _ = (((n : ℝ) + 1) * Q.det) * ((n : ℝ) + 1) := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_borderBasis]

/-- The missing dimension factor in the manuscript: compression to the columns
`e_j-e_last` multiplies the determinant by the number of vertices, provided
`Q` is symmetric and fixes the constant vector. -/
theorem det_coordinateCompression {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQsym : Q.transpose = Q)
    (hQ : Q *ᵥ (fun _ => 1) = (fun _ => 1)) :
    ((coordinateEmbedding n).transpose * Q * coordinateEmbedding n).det =
      ((n : ℝ) + 1) * Q.det := by
  let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
  let Qb := Q.submatrix e e
  have hsymb : Qb.transpose = Qb := by
    simp [Qb, Matrix.transpose_submatrix, hQsym]
  have hQb : Qb *ᵥ (fun _ => 1) = (fun _ => 1) := by
    funext i
    calc
      (Qb *ᵥ (fun _ => 1)) i = ∑ j, Q (e i) (e j) := by
        simp [Qb, Matrix.mulVec, dotProduct]
      _ = ∑ j, Q (e i) j := Equiv.sum_comp e _
      _ = 1 := by simpa [Matrix.mulVec, dotProduct] using congrFun hQ (e i)
  have hH : (borderEmbedding n).transpose * Qb * borderEmbedding n =
      (coordinateEmbedding n).transpose * Q * coordinateEmbedding n := by
    rw [border_embedding_reindex]
    change ((coordinateEmbedding n).submatrix e id).transpose *
      Q.submatrix e e * (coordinateEmbedding n).submatrix e id = _
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv]
    rfl
  have hh := det_border_compression n Qb hsymb hQb
  rw [hH] at hh
  simpa only [Qb, Matrix.det_submatrix_equiv_self] using hh

end Wormald


