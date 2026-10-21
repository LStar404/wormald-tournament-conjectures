import Wormald.RankOneSpectralDecomposition

namespace Wormald
noncomputable section
open scoped BigOperators
open Matrix

/-- The scalar rank-one determinant lemma, proved from the general Schur
determinant identity. -/
theorem det_sub_vecMulVec {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (G : Matrix ι ι K) (u b : ι → K) (hG : IsUnit G.det) :
    (G - Matrix.vecMulVec u b).det = G.det * (1 - b ⬝ᵥ (G⁻¹ *ᵥ u)) := by
  let U : Matrix ι (Fin 1) K := Matrix.replicateCol (Fin 1) u
  let V : Matrix (Fin 1) ι K := Matrix.replicateRow (Fin 1) b
  have hM : G - Matrix.vecMulVec u b = G + (-U) * V := by
    ext i j
    simp [U, V, Matrix.mul_apply, Matrix.vecMulVec, sub_eq_add_neg]
  have hentry : (V * G⁻¹ * (-U)) 0 0 = -(b ⬝ᵥ (G⁻¹ *ᵥ u)) := by
    change (∑ k, (∑ j, b j * G⁻¹ j k) * (-u k)) = -(b ⬝ᵥ (G⁻¹ *ᵥ u))
    rw [Matrix.dot_mulVec_eq_sum_sum]
    simp [Finset.sum_mul, mul_neg, Finset.sum_neg_distrib]
  rw [hM, Matrix.det_add_mul (-U) V hG, Matrix.det_fin_one]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, hentry, sub_eq_add_neg]

/-- The resolvent of the unperturbed part gives both eigenvectors whenever
the actual rank-one perturbation has zero characteristic determinant. -/
theorem resolvent_rankOne_eigenvectors {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (B : Matrix ι ι K) (u b : ι → K) (lam : K)
    (hG : IsUnit (lam • (1 : Matrix ι ι K) - B).det)
    (hchar : (lam • (1 : Matrix ι ι K) - (B + Matrix.vecMulVec u b)).det = 0) :
    let H := (lam • (1 : Matrix ι ι K) - B)⁻¹
    let r := H *ᵥ u
    let l := b ᵥ* H
    b ⬝ᵥ r = 1 ∧
      (B + Matrix.vecMulVec u b) *ᵥ r = lam • r ∧
      l ᵥ* (B + Matrix.vecMulVec u b) = lam • l := by
  let G := lam • (1 : Matrix ι ι K) - B
  let H := G⁻¹
  let r := H *ᵥ u
  let l := b ᵥ* H
  have hbr : b ⬝ᵥ r = 1 := by
    have hzero : (G - Matrix.vecMulVec u b).det = 0 := by
      convert hchar using 1
      congr 1
      dsimp [G]
      abel
    rw [det_sub_vecMulVec G u b hG] at hzero
    have h := (mul_eq_zero.mp hzero).resolve_left hG.ne_zero
    exact (sub_eq_zero.mp h).symm
  have hlu : l ⬝ᵥ u = 1 := by
    simpa only [r, l, Matrix.dotProduct_mulVec] using hbr
  have hrG : G *ᵥ r = u := by
    dsimp [r, H]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hG, Matrix.one_mulVec]
  have hlG : l ᵥ* G = b := by
    dsimp [l, H]
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul G hG, Matrix.vecMul_one]
  have houter : Matrix.vecMulVec u b *ᵥ r = u := by
    funext i
    change (∑ j, u i * b j * r j) = u i
    simp only [mul_assoc, ← Finset.mul_sum]
    change u i * (b ⬝ᵥ r) = u i
    rw [hbr, mul_one]
  have houter' : l ᵥ* Matrix.vecMulVec u b = b := by
    rw [Matrix.vecMul_vecMulVec, hlu, one_smul]
  refine ⟨hbr, ?_, ?_⟩
  · rw [Matrix.add_mulVec, houter]
    simp only [G, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hrG
    funext i
    have h := congrFun hrG i
    change (B *ᵥ r) i + u i = lam * r i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    linear_combination -h
  · rw [Matrix.vecMul_add, houter']
    simp only [G, Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one] at hlG
    funext i
    have h := congrFun hlG i
    change (l ᵥ* B) i + b i = lam * l i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    linear_combination -h

end
end Wormald
