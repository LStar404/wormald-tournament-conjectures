import Wormald.PositiveTransitionSquare

namespace Wormald

noncomputable section
open Matrix
open scoped BigOperators

def finiteL1 {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, |x i|

theorem finiteL1_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ finiteL1 x :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem finiteL1_smul {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    finiteL1 (c • x) = |c| * finiteL1 x := by
  simp [finiteL1, Pi.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]

theorem rowStochastic_sum_vecMul {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ Matrix.rowStochastic ℝ (Fin n)) (x : Fin n → ℝ) :
    (∑ j, (x ᵥ* Q) j) = ∑ i, x i := by
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, Matrix.sum_row_of_mem_rowStochastic hQ, mul_one]

theorem rowStochastic_finiteL1_vecMul_le {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ Matrix.rowStochastic ℝ (Fin n)) (x : Fin n → ℝ) :
    finiteL1 (x ᵥ* Q) ≤ finiteL1 x := by
  calc
    _ = ∑ j, |∑ i, x i * Q i j| := rfl
    _ ≤ ∑ j, ∑ i, |x i * Q i j| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i, |x i| * ∑ j, Q i j := by
      simp only [abs_mul, abs_of_nonneg (Matrix.nonneg_of_mem_rowStochastic hQ)]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by simp only [Matrix.sum_row_of_mem_rowStochastic hQ, mul_one, finiteL1]

theorem vecMul_uniformTransition_eq_zero {n : ℕ} (x : Fin n → ℝ) (hx : ∑ i, x i = 0) :
    x ᵥ* uniformTransition n = 0 := by
  ext j
  change (∑ i, x i * (1 / (n : ℝ))) = 0
  rw [← Finset.sum_mul, hx, zero_mul]

theorem Tournament.vecMul_sq_eq_doeblin {n : ℕ} (T : Tournament n)
    (hn : 1 < n) (x : Fin n → ℝ) (hx : ∑ i, x i = 0) :
    x ᵥ* T.realCriticalTransition ^ 2 = (1 - 1 / (n : ℝ)) • (x ᵥ* T.doeblinRemainder) := by
  rw [T.realCriticalTransition_sq_doeblin hn, Matrix.vecMul_add,
    Matrix.vecMul_smul, Matrix.vecMul_smul, vecMul_uniformTransition_eq_zero x hx]
  simp

/-- Explicit contraction of signed mass-zero measures. Dividing by two gives
the same factor for total variation distance between probability measures. -/
theorem Tournament.finiteL1_vecMul_sq_le {n : ℕ} (T : Tournament n)
    (hn : 1 < n) (hT : T.Regular) (x : Fin n → ℝ) (hx : ∑ i, x i = 0) :
    finiteL1 (x ᵥ* T.realCriticalTransition ^ 2) ≤
      (1 - 1 / (n : ℝ)) * finiteL1 x := by
  rw [T.vecMul_sq_eq_doeblin hn x hx, finiteL1_smul,
    abs_of_nonneg (one_sub_inv_nat_pos hn).le]
  exact mul_le_mul_of_nonneg_left
    (rowStochastic_finiteL1_vecMul_le T.doeblinRemainder (T.doeblinRemainder_rowStochastic hn hT) x)
      (one_sub_inv_nat_pos hn).le

theorem rowStochastic_mulVec_mem_Icc {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ Matrix.rowStochastic ℝ (Fin n)) (f : Fin n → ℝ)
    (a b : ℝ) (hf : ∀ i, f i ∈ Set.Icc a b) (i : Fin n) :
    (Q *ᵥ f) i ∈ Set.Icc a b := by
  have hlo := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hf j).1 (Matrix.nonneg_of_mem_rowStochastic hQ (i := i) (j := j)))
  have hhi := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hf j).2 (Matrix.nonneg_of_mem_rowStochastic hQ (i := i) (j := j)))
  constructor
  · simpa only [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hQ, one_mul,
      Matrix.mulVec, dotProduct] using hlo
  · simpa only [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hQ, one_mul,
      Matrix.mulVec, dotProduct] using hhi

/-- A two-step transition shrinks the width of every interval containing the
observable by the explicit factor `1 - 1/n`. -/
theorem Tournament.mulVec_sq_amplitude_le {n : ℕ} (T : Tournament n)
    (hn : 1 < n) (hT : T.Regular) (f : Fin n → ℝ)
    (a b : ℝ) (hf : ∀ i, f i ∈ Set.Icc a b) (i j : Fin n) :
    |(T.realCriticalTransition ^ 2 *ᵥ f) i - (T.realCriticalTransition ^ 2 *ᵥ f) j| ≤
      (1 - 1 / (n : ℝ)) * (b - a) := by
  have hi := rowStochastic_mulVec_mem_Icc T.doeblinRemainder
    (T.doeblinRemainder_rowStochastic hn hT) f a b hf i
  have hj := rowStochastic_mulVec_mem_Icc T.doeblinRemainder
    (T.doeblinRemainder_rowStochastic hn hT) f a b hf j
  have hdiff : (T.realCriticalTransition ^ 2 *ᵥ f) i -
      (T.realCriticalTransition ^ 2 *ᵥ f) j =
      (1 - 1 / (n : ℝ)) * ((T.doeblinRemainder *ᵥ f) i - (T.doeblinRemainder *ᵥ f) j) := by
    rw [T.realCriticalTransition_sq_doeblin hn, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.smul_mulVec]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hu : (uniformTransition n *ᵥ f) i = (uniformTransition n *ᵥ f) j := rfl
    rw [hu]
    ring
  rw [hdiff, abs_mul, abs_of_nonneg (one_sub_inv_nat_pos hn).le]
  apply mul_le_mul_of_nonneg_left _ (one_sub_inv_nat_pos hn).le
  exact abs_sub_le_iff.mpr ⟨by linarith [hi.2, hj.1], by linarith [hj.2, hi.1]⟩

theorem Tournament.finiteL1_vecMul_even_pow_le {n : ℕ} (T : Tournament n)
    (hn : 1 < n) (hT : T.Regular) (x : Fin n → ℝ) (hx : ∑ i, x i = 0) (k : ℕ) :
    finiteL1 (x ᵥ* T.realCriticalTransition ^ (2 * k)) ≤
      (1 - 1 / (n : ℝ)) ^ k * finiteL1 x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmass : (∑ i, (x ᵥ* T.realCriticalTransition ^ (2 * k)) i) = 0 := by
      rw [rowStochastic_sum_vecMul _
        ((Matrix.rowStochastic ℝ (Fin n)).pow_mem
          (T.realCriticalTransition_rowStochastic (by omega) hT) _) x, hx]
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add, ← Matrix.vecMul_vecMul]
    calc
      _ ≤ (1 - 1 / (n : ℝ)) * finiteL1 (x ᵥ* T.realCriticalTransition ^ (2 * k)) :=
        T.finiteL1_vecMul_sq_le hn hT _ hmass
      _ ≤ (1 - 1 / (n : ℝ)) * ((1 - 1 / (n : ℝ)) ^ k * finiteL1 x) :=
        mul_le_mul_of_nonneg_left ih (one_sub_inv_nat_pos hn).le
      _ = _ := by rw [pow_succ]; ring

/-- Every two steps contract by `1-1/n`; the optional final step is
nonexpansive. The exponent is the exact floor `N/2`. -/
theorem Tournament.finiteL1_vecMul_pow_le {n : ℕ} (T : Tournament n)
    (hn : 1 < n) (hT : T.Regular) (x : Fin n → ℝ) (hx : ∑ i, x i = 0) (N : ℕ) :
    finiteL1 (x ᵥ* T.realCriticalTransition ^ N) ≤
      (1 - 1 / (n : ℝ)) ^ (N / 2) * finiteL1 x := by
  calc
    _ = finiteL1 ((x ᵥ* T.realCriticalTransition ^ (2 * (N / 2))) ᵥ*
        T.realCriticalTransition ^ (N % 2)) := by
      rw [Matrix.vecMul_vecMul, ← pow_add]
      rw [show 2 * (N / 2) + N % 2 = N by omega]
    _ ≤ finiteL1 (x ᵥ* T.realCriticalTransition ^ (2 * (N / 2))) :=
      rowStochastic_finiteL1_vecMul_le _
        ((Matrix.rowStochastic ℝ (Fin n)).pow_mem
          (T.realCriticalTransition_rowStochastic (by omega) hT) _) _
    _ ≤ _ := T.finiteL1_vecMul_even_pow_le hn hT x hx _

theorem finiteL1_sub_le {n : ℕ} (x y : Fin n → ℝ) :
    finiteL1 (x - y) ≤ finiteL1 x + finiteL1 y := by
  simpa only [finiteL1, Pi.sub_apply, Finset.sum_add_distrib] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      (show |x i - y i| ≤ |x i| + |y i| by
        simpa only [Real.norm_eq_abs] using norm_sub_le (x i) (y i)))

@[simp] theorem finiteL1_single_one {n : ℕ} (i : Fin n) :
    finiteL1 (Pi.single i (1 : ℝ)) = 1 := by
  simp only [finiteL1, Pi.single_apply, apply_ite, abs_one, abs_zero]
  simp

/-- Explicit total variation mixing of any pair of starting states. -/
theorem Tournament.sum_abs_row_pow_sub_le {n : ℕ} (T : Tournament n)
    (hn : 1 < n) (hT : T.Regular) (i j : Fin n) (N : ℕ) :
    (∑ k, |(T.realCriticalTransition ^ N) i k - (T.realCriticalTransition ^ N) j k|) ≤
      2 * (1 - 1 / (n : ℝ)) ^ (N / 2) := by
  have hx : (∑ k, ((Pi.single i (1 : ℝ) : Fin n → ℝ) -
      (Pi.single j (1 : ℝ) : Fin n → ℝ)) k) = 0 := by
    simp [Pi.sub_apply, Finset.sum_sub_distrib, Pi.single_apply]
  have hh := T.finiteL1_vecMul_pow_le hn hT _ hx N
  have hnorm : finiteL1 (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ)) ≤ 2 := by
    have hb := finiteL1_sub_le (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ))
    rw [finiteL1_single_one, finiteL1_single_one] at hb
    linarith
  rw [Matrix.sub_vecMul, Matrix.single_one_vecMul, Matrix.single_one_vecMul] at hh
  exact hh.trans (by
    have hb := mul_le_mul_of_nonneg_left hnorm (pow_nonneg (one_sub_inv_nat_pos hn).le (N / 2))
    simpa only [mul_comm] using hb)

end
end Wormald
