import Wormald.RegularCandidate

/-! Positive definiteness and the exact determinant of the anchored
covariance matrix. Two unitriangular basis changes isolate the constant
vector without changing the ambient determinant. -/

namespace Wormald
noncomputable section
open Matrix
open scoped BigOperators

def anchoredCovariance {n : ℕ} (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun j k => Q j.castSucc k.castSucc - 1 / ((n : ℝ) + 1)

private def centeredEmbedding (n : ℕ) : Matrix (Fin n ⊕ Fin 1) (Fin n) ℝ :=
  fun i j => (if i = Sum.inl j then 1 else 0) - 1 / ((n : ℝ) + 1)

private def centeredBasis (n : ℕ) : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks 1 (Matrix.of fun _ _ => 1) 0 1 *
    Matrix.fromBlocks 1 0 (Matrix.of fun _ _ => -(1 / ((n : ℝ) + 1))) 1

private theorem det_centeredBasis (n : ℕ) : (centeredBasis n).det = 1 := by
  rw [centeredBasis, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_fromBlocks_zero₁₂]
  simp

private theorem centeredBasis_left (n : ℕ) (i : Fin n ⊕ Fin 1) (j : Fin n) :
    centeredBasis n i (Sum.inl j) = centeredEmbedding n i j := by
  cases i with
  | inl i => simp [centeredBasis, centeredEmbedding, Matrix.mul_apply, Matrix.one_apply,
      sub_eq_add_neg]
  | inr i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [centeredBasis, centeredEmbedding, Matrix.mul_apply, Matrix.one_apply]

private theorem centeredBasis_right (n : ℕ) (i : Fin n ⊕ Fin 1) (j : Fin 1) :
    centeredBasis n i (Sum.inr j) = 1 := by
  cases i with
  | inl i => simp [centeredBasis, Matrix.fromBlocks_multiply]
  | inr i =>
      have hij : i = j := Subsingleton.elim _ _
      subst j
      simp [centeredBasis, Matrix.fromBlocks_multiply]

private theorem centeredEmbedding_sum (n : ℕ) (j : Fin n) :
    (∑ i, centeredEmbedding n i j) = 0 := by
  have hd : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [centeredEmbedding, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_sum,
    Fintype.card_fin, Nat.cast_add, Nat.cast_one, nsmul_eq_mul]
  field_simp
  norm_num

private theorem centered_Q_mul (n : ℕ)
    (Q : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (hfix : Q *ᵥ (fun _ => 1) = (fun _ => 1)) (i : Fin n ⊕ Fin 1) (j : Fin n) :
    (Q * centeredEmbedding n) i j = Q i (Sum.inl j) - 1 / ((n : ℝ) + 1) := by
  have hrow : (∑ k, Q i k) = 1 := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hfix i
  simp only [Matrix.mul_apply, centeredEmbedding, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.sum_mul, hrow, one_mul]

private theorem centered_congruence (n : ℕ)
    (Q : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (hsym : Q.transpose = Q) (hfix : Q *ᵥ (fun _ => 1) = (fun _ => 1)) :
    (centeredBasis n).transpose * Q * centeredBasis n =
      Matrix.fromBlocks (Matrix.of fun j k : Fin n =>
        Q (Sum.inl j) (Sum.inl k) - 1 / ((n : ℝ) + 1)) 0 0
        (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (n : ℝ) + 1) := by
  let M := (centeredBasis n).transpose * Q * centeredBasis n
  have hsymM : M.transpose = M := by
    dsimp [M]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hsym, Matrix.mul_assoc]
  have hright (i : Fin n ⊕ Fin 1) (j : Fin 1) :
      (Q * centeredBasis n) i (Sum.inr j) = 1 := by
    simpa [Matrix.mul_apply, centeredBasis_right, Matrix.mulVec, dotProduct]
      using congrFun hfix i
  have hleftMul (i : Fin n ⊕ Fin 1) (j : Fin n) :
      (Q * centeredBasis n) i (Sum.inl j) =
        Q i (Sum.inl j) - 1 / ((n : ℝ) + 1) := by
    simpa only [Matrix.mul_apply, centeredBasis_left] using centered_Q_mul n Q hfix i j
  have hcol (j : Fin n ⊕ Fin 1) : (∑ i, Q i j) = 1 := by
    have hrow : (∑ i, Q j i) = 1 := by
      simpa [Matrix.mulVec, dotProduct] using congrFun hfix j
    have he (i : Fin n ⊕ Fin 1) : Q i j = Q j i :=
      congrFun (congrFun hsym j) i
    simpa only [he] using hrow
  have hTL (i j : Fin n) : M (Sum.inl i) (Sum.inl j) =
      Q (Sum.inl i) (Sum.inl j) - 1 / ((n : ℝ) + 1) := by
    dsimp [M]
    rw [Matrix.mul_assoc]
    change (∑ k, centeredBasis n k (Sum.inl i) * (Q * centeredBasis n) k (Sum.inl j)) = _
    simp only [centeredBasis_left, hleftMul]
    have hd : (n : ℝ) + 1 ≠ 0 := by positivity
    simp only [centeredEmbedding, sub_mul, mul_sub, ite_mul, one_mul, zero_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      ← Finset.mul_sum, hcol, Finset.sum_const,
      Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Nat.cast_add,
      Nat.cast_one, nsmul_eq_mul]
    field_simp
    ring
  have hTR (i : Fin n) (j : Fin 1) : M (Sum.inl i) (Sum.inr j) = 0 := by
    dsimp [M]
    rw [Matrix.mul_assoc]
    change (∑ k, centeredBasis n k (Sum.inl i) * (Q * centeredBasis n) k (Sum.inr j)) = 0
    simp only [centeredBasis_left, hright, mul_one]
    exact centeredEmbedding_sum n i
  have hBR (i j : Fin 1) : M (Sum.inr i) (Sum.inr j) = (n : ℝ) + 1 := by
    dsimp [M]
    rw [Matrix.mul_assoc]
    change (∑ k, centeredBasis n k (Sum.inr i) * (Q * centeredBasis n) k (Sum.inr j)) = _
    simp [centeredBasis_right, hright]
  change M = _
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j => exact hTL i j
      | inr j => exact hTR i j
  | inr i =>
      cases j with
      | inl j => exact (congrFun (congrFun hsymM (Sum.inl j)) (Sum.inr i)).trans (hTR j i)
      | inr j => exact hBR i j

private theorem anchored_sum_facts (n : ℕ)
    (Q : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (hQ : Q.PosDef) (hfix : Q *ᵥ (fun _ => 1) = (fun _ => 1)) :
    (Matrix.of fun j k : Fin n => Q (Sum.inl j) (Sum.inl k) - 1 / ((n : ℝ) + 1)).PosDef ∧
      (Matrix.of fun j k : Fin n => Q (Sum.inl j) (Sum.inl k) - 1 / ((n : ℝ) + 1)).det =
        Q.det / ((n : ℝ) + 1) := by
  have hsym : Q.transpose = Q := Matrix.isHermitian_iff_isSymm.mp hQ.isHermitian
  have hconj := centered_congruence n Q hsym hfix
  have hZ : Function.Injective (centeredBasis n).mulVec :=
    Matrix.mulVec_injective_of_det_ne_zero (by rw [det_centeredBasis]; norm_num)
  have hpos : ((centeredBasis n).transpose * Q * centeredBasis n).PosDef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hQ.conjTranspose_mul_mul_same hZ
  constructor
  · have hh := hpos.submatrix (Sum.inl_injective : Function.Injective (Sum.inl : Fin n → Fin n ⊕ Fin 1))
    rw [hconj] at hh
    exact hh
  · have hd : (n : ℝ) + 1 ≠ 0 := by positivity
    apply (eq_div_iff hd).mpr
    calc
      _ = ((centeredBasis n).transpose * Q * centeredBasis n).det := by
        rw [hconj, Matrix.det_fromBlocks_zero₂₁,
          Matrix.det_unique (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (n : ℝ) + 1)]
        rfl
      _ = Q.det := by
        rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_centeredBasis]
        ring

theorem anchoredCovariance_posDef_and_det {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hQ : Q.PosDef)
    (hfix : Q *ᵥ (fun _ => 1) = (fun _ => 1)) :
    (anchoredCovariance Q).PosDef ∧ (anchoredCovariance Q).det = Q.det / ((n : ℝ) + 1) := by
  let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
  let Qb := Q.submatrix e e
  have hQb : Qb.PosDef := hQ.submatrix e.injective
  have hfixb : Qb *ᵥ (fun _ => 1) = (fun _ => 1) := by
    funext i
    calc
      _ = ∑ j, Q (e i) (e j) := by simp [Qb, Matrix.mulVec, dotProduct]
      _ = ∑ j, Q (e i) j := Equiv.sum_comp e _
      _ = 1 := by simpa [Matrix.mulVec, dotProduct] using congrFun hfix (e i)
  have hh := anchored_sum_facts n Qb hQb hfixb
  have hR : (Matrix.of fun j k : Fin n => Qb (Sum.inl j) (Sum.inl k) - 1 / ((n : ℝ) + 1)) =
      anchoredCovariance Q := by
    ext j k
    rfl
  rw [hR] at hh
  simpa only [Qb, Matrix.det_submatrix_equiv_self] using hh

theorem anchoredCovariance_posDef {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hQ : Q.PosDef)
    (hfix : Q *ᵥ (fun _ => 1) = (fun _ => 1)) : (anchoredCovariance Q).PosDef :=
  (anchoredCovariance_posDef_and_det Q hQ hfix).1

theorem det_anchoredCovariance {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hQ : Q.PosDef)
    (hfix : Q *ᵥ (fun _ => 1) = (fun _ => 1)) :
    (anchoredCovariance Q).det = Q.det / ((n : ℝ) + 1) :=
  (anchoredCovariance_posDef_and_det Q hQ hfix).2

def Tournament.covarianceAnchor {n : ℕ} (T : Tournament (n + 1)) : Matrix (Fin n) (Fin n) ℝ :=
  anchoredCovariance ((1 + T.realNormalizedSign * T.realNormalizedSign) *
    (1 - T.realNormalizedSign * T.realNormalizedSign)⁻¹)

theorem Tournament.covarianceAnchor_posDef_and_det {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    T.covarianceAnchor.PosDef ∧ T.covarianceAnchor.det =
      ((1 + T.realNormalizedSign * T.realNormalizedSign) *
        (1 - T.realNormalizedSign * T.realNormalizedSign)⁻¹).det / ((n : ℝ) + 1) := by
  exact anchoredCovariance_posDef_and_det _ (T.posDef_realNormalizedSign_core (Nat.succ_ne_zero n))
    (resolvent_mulVec_of_kernel _ T.realNormalizedSign_skew _ (T.realNormalizedSign_mulVec_one hT))

theorem Tournament.covarianceAnchor_posDef {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) : T.covarianceAnchor.PosDef :=
  (T.covarianceAnchor_posDef_and_det hT).1

theorem Tournament.covarianceAnchor_det {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    T.covarianceAnchor.det =
      ((1 + T.realNormalizedSign * T.realNormalizedSign) *
        (1 - T.realNormalizedSign * T.realNormalizedSign)⁻¹).det / ((n : ℝ) + 1) :=
  (T.covarianceAnchor_posDef_and_det hT).2

def Tournament.occupationCovariance {n : ℕ} (T : Tournament (n + 1)) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / ((n : ℝ) + 1)) • T.covarianceAnchor

theorem Tournament.occupationCovariance_posDef {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) : T.occupationCovariance.PosDef := by
  exact (T.covarianceAnchor_posDef hT).smul (by positivity : 0 < 1 / ((n : ℝ) + 1))

theorem Tournament.occupationCovariance_det {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    T.occupationCovariance.det =
      ((1 + T.realNormalizedSign * T.realNormalizedSign) *
        (1 - T.realNormalizedSign * T.realNormalizedSign)⁻¹).det / ((n : ℝ) + 1) ^ (n + 1) := by
  have hd : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [Tournament.occupationCovariance, Matrix.det_smul, Fintype.card_fin,
    T.covarianceAnchor_det hT, div_pow, one_pow, pow_succ]
  field_simp

end
end Wormald
