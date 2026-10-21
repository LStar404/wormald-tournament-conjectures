import Wormald.MomentBound

namespace Wormald

noncomputable section
open Matrix Finset

def signSwitch {n : ℕ} (ε : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal ε * M * Matrix.diagonal ε

private theorem sign_diagonal_sq {n : ℕ} (ε : Fin n → ℝ) (hε : ∀ i, ε i ^ 2 = 1) :
    Matrix.diagonal ε * Matrix.diagonal ε = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have h : (fun i => ε i * ε i) = (fun _ => (1 : ℝ)) := by
    funext i
    simpa only [pow_two] using hε i
  rw [h, Matrix.diagonal_one]

theorem signSwitch_mul {n : ℕ} (ε : Fin n → ℝ) (hε : ∀ i, ε i ^ 2 = 1)
    (M N : Matrix (Fin n) (Fin n) ℝ) :
    signSwitch ε (M * N) = signSwitch ε M * signSwitch ε N := by
  unfold signSwitch
  calc
    _ = Matrix.diagonal ε * M * (Matrix.diagonal ε * Matrix.diagonal ε) * N * Matrix.diagonal ε := by
      rw [sign_diagonal_sq ε hε]
      simp only [mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem signSwitch_pow {n : ℕ} (ε : Fin n → ℝ) (hε : ∀ i, ε i ^ 2 = 1)
    (M : Matrix (Fin n) (Fin n) ℝ) (p : ℕ) :
    signSwitch ε (M ^ p) = signSwitch ε M ^ p := by
  induction p with
  | zero => simp [signSwitch, sign_diagonal_sq ε hε]
  | succ p ih => rw [pow_succ, signSwitch_mul ε hε, ih, pow_succ]

theorem signSwitch_frobenius_sq {n : ℕ} (ε : Fin n → ℝ) (hε : ∀ i, ε i ^ 2 = 1)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, signSwitch ε M i j ^ 2) = ∑ i, ∑ j, M i j ^ 2 := by
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [signSwitch, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [mul_pow, mul_pow, hε, hε, one_mul, mul_one]

theorem submatrix_perm_pow {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (e : Equiv.Perm (Fin n)) (p : ℕ) :
    (M ^ p).submatrix e e = M.submatrix e e ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ, ← Matrix.submatrix_mul_equiv _ _ e e e, ih, pow_succ]

theorem submatrix_perm_frobenius_sq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (e : Equiv.Perm (Fin n)) :
    (∑ i, ∑ j, M.submatrix e e i j ^ 2) = ∑ i, ∑ j, M i j ^ 2 := by
  simp only [Matrix.submatrix_apply]
  calc
    _ = ∑ i, ∑ j, M (e i) j ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Equiv.sum_comp e (fun j => M (e i) j ^ 2)
    _ = _ := Equiv.sum_comp e (fun i => ∑ j, M i j ^ 2)

/-- Signed relabeling preserves every matrix-power moment. -/
theorem pow_frobenius_sq_eq_of_signSwitch {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℝ) (e : Equiv.Perm (Fin n))
    (ε : Fin n → ℝ) (hε : ∀ i, ε i ^ 2 = 1)
    (hMN : M.submatrix e e = signSwitch ε N) (p : ℕ) :
    (∑ i, ∑ j, (M ^ p) i j ^ 2) = ∑ i, ∑ j, (N ^ p) i j ^ 2 := by
  calc
    _ = ∑ i, ∑ j, (M ^ p).submatrix e e i j ^ 2 :=
      (submatrix_perm_frobenius_sq _ e).symm
    _ = ∑ i, ∑ j, signSwitch ε (N ^ p) i j ^ 2 := by
      rw [submatrix_perm_pow, hMN, ← signSwitch_pow ε hε]
    _ = _ := signSwitch_frobenius_sq ε hε _

/-- The actual odd carousel and the transitive tournament have exactly the same
power moments, despite having different ordinary isomorphism classes. -/
theorem carousel_pow_frobenius_sq_eq_transitive (q p : ℕ) :
    (∑ i, ∑ j, (orientationSign (FiniteModel.carousel (2 * q + 1)) ℝ ^ p) i j ^ 2) =
      ∑ i, ∑ j, (transitiveSign (2 * q + 1) ℝ ^ p) i j ^ 2 := by
  let ε : Fin (2 * q + 1) → ℝ := fun i => if i.val % 2 = 0 then 1 else -1
  have hε : ∀ i, ε i ^ 2 = 1 := by
    intro i
    dsimp [ε]
    split_ifs <;> norm_num
  have hs := carouselSign_shuffle (K := ℝ) q
  change (orientationSign (FiniteModel.carousel (2 * q + 1)) ℝ).submatrix
    (carouselShuffle q) (carouselShuffle q) = signSwitch ε (transitiveSign (2 * q + 1) ℝ) at hs
  exact pow_frobenius_sq_eq_of_signSwitch _ _ (carouselShuffle q) ε hε hs p

theorem carousel_pow_frobenius_sq_eq_transitive_odd (n : ℕ) (hn : Odd n) (p : ℕ) :
    (∑ i, ∑ j, (orientationSign (FiniteModel.carousel n) ℝ ^ p) i j ^ 2) =
      ∑ i, ∑ j, (transitiveSign n ℝ ^ p) i j ^ 2 := by
  rcases hn with ⟨q, hq⟩
  have hnform : n = 2 * q + 1 := by omega
  subst n
  exact carousel_pow_frobenius_sq_eq_transitive q p

/-- The all-moment extremal inequality with the exact carousel reference. -/
theorem tournament_pow_frobenius_sq_le_carousel {n : ℕ} (hn : Odd n)
    (T : FiniteModel.Orientation n) (p : ℕ) :
    (∑ i, ∑ j, (orientationSign T ℝ ^ p) i j ^ 2) ≤
      ∑ i, ∑ j, (orientationSign (FiniteModel.carousel n) ℝ ^ p) i j ^ 2 := by
  rw [carousel_pow_frobenius_sq_eq_transitive_odd n hn p]
  exact tournament_pow_frobenius_sq_le_transitive T p

end
end Wormald
