import Wormald.CarouselDeterminant
import Wormald.CarouselRegular

namespace Wormald

noncomputable section
open Matrix
open FiniteModel

/-- The same tournament sign convention, over any coefficient ring. -/
def orientationSign {n : ℕ} (T : Orientation n) (K : Type*) [Zero K] [One K] [Neg K] :
    Matrix (Fin n) (Fin n) K :=
  fun i j => if i = j then 0 else if arc T i j then 1 else -1

@[simp] theorem orientationSign_self {n : ℕ} (T : Orientation n)
    {K : Type*} [Zero K] [One K] [Neg K] (i : Fin n) : orientationSign T K i i = 0 := by
  simp [orientationSign]

theorem orientationSign_reverse {n : ℕ} (T : Orientation n)
    {K : Type*} [Ring K] (i j : Fin n) (h : i ≠ j) :
    orientationSign T K i j = -orientationSign T K j i := by
  have harc := arc_reverse T i j h
  simp only [orientationSign, ite_eq_right h, ite_eq_right (Ne.symm h), harc]
  cases arc T j i <;> simp

/-- A direct parity shuffle implementing multiplication by q+1 modulo 2q+1. -/
def carouselShuffle (q : ℕ) : Equiv.Perm (Fin (2 * q + 1)) where
  toFun i := ⟨if i.val % 2 = 0 then i.val / 2 else q + 1 + i.val / 2, by
    have hi := i.isLt
    split_ifs <;> omega⟩
  invFun j := ⟨if j.val ≤ q then 2 * j.val else 2 * (j.val - q - 1) + 1, by
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

private theorem carouselShuffle_val (q : ℕ) (i : Fin (2 * q + 1)) :
    (carouselShuffle q i).val =
      if i.val % 2 = 0 then i.val / 2 else q + 1 + i.val / 2 := rfl

private theorem carouselShuffle_arc_upper (q : ℕ) (i j : Fin (2 * q + 1))
    (hij : i < j) :
    arc (carousel (2 * q + 1)) (carouselShuffle q i) (carouselShuffle q j) = true ↔
      i.val % 2 = j.val % 2 := by
  rw [carousel_arc_iff (show Odd (2 * q + 1) from ⟨q, by omega⟩)]
  have hi := i.isLt
  have hj := j.isLt
  have hijval : i.val < j.val := hij
  simp only [clockwiseDistance, Fin.le_def, carouselShuffle_val]
  split_ifs <;> omega

private def alternatingSign {K : Type*} [One K] [Neg K] {n : ℕ} (i : Fin n) : K :=
  if i.val % 2 = 0 then 1 else -1

private theorem alternatingSign_mul {K : Type*} [Ring K] {n : ℕ} (i j : Fin n) :
    alternatingSign (K := K) i * alternatingSign j =
      if i.val % 2 = j.val % 2 then 1 else -1 := by
  unfold alternatingSign
  split_ifs <;> norm_num <;> omega

private theorem carouselSign_shuffle_upper {K : Type*} [Field K]
    (q : ℕ) (i j : Fin (2 * q + 1)) (hij : i < j) :
    orientationSign (carousel (2 * q + 1)) K (carouselShuffle q i) (carouselShuffle q j) =
      alternatingSign (K := K) i * alternatingSign j := by
  have hne : carouselShuffle q i ≠ carouselShuffle q j :=
    (carouselShuffle q).injective.ne (ne_of_lt hij)
  rw [alternatingSign_mul]
  by_cases hpar : i.val % 2 = j.val % 2
  · have ha := (carouselShuffle_arc_upper q i j hij).mpr hpar
    simp [orientationSign, hne, hpar, ha]
  · have ha : arc (carousel (2 * q + 1)) (carouselShuffle q i) (carouselShuffle q j) = false := by
      cases hval : arc (carousel (2 * q + 1)) (carouselShuffle q i) (carouselShuffle q j)
      · rfl
      · exact False.elim (hpar ((carouselShuffle_arc_upper q i j hij).mp hval))
    simp [orientationSign, hne, hpar, ha]

/-- Reindexing the odd carousel is precisely alternating sign switching of the transitive matrix. -/
theorem carouselSign_shuffle {K : Type*} [Field K] (q : ℕ) :
    (orientationSign (carousel (2 * q + 1)) K).submatrix (carouselShuffle q) (carouselShuffle q) =
      Matrix.diagonal (alternatingSign (K := K)) * transitiveSign (2 * q + 1) K *
        Matrix.diagonal (alternatingSign (K := K)) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases lt_trichotomy i j with hij | heq | hji
  · rw [carouselSign_shuffle_upper q i j hij]
    simp [transitiveSign, hij]
  · subst j
    simp [transitiveSign]
  · have hne : carouselShuffle q i ≠ carouselShuffle q j :=
      (carouselShuffle q).injective.ne (ne_of_gt hji)
    rw [orientationSign_reverse _ _ _ hne, carouselSign_shuffle_upper q j i hji]
    simp [transitiveSign, hji, not_lt_of_gt hji]
    ring

/-- Diagonal sign switching preserves the full determinant polynomial. -/
theorem det_one_add_smul_carouselSign {K : Type*} [Field K] [CharZero K]
    (q : ℕ) (t : K) :
    (1 + t • orientationSign (carousel (2 * q + 1)) K).det =
      ((1 + t) ^ (2 * q + 1) + (1 - t) ^ (2 * q + 1)) / 2 := by
  let D : Matrix (Fin (2 * q + 1)) (Fin (2 * q + 1)) K :=
    Matrix.diagonal (alternatingSign (K := K))
  have hε : (fun i : Fin (2 * q + 1) =>
      alternatingSign (K := K) i * alternatingSign i) = (fun _ => (1 : K)) := by
    funext i
    unfold alternatingSign
    split_ifs <;> ring
  have hDsquare : D * D = 1 := by
    dsimp [D]
    rw [Matrix.diagonal_mul_diagonal, hε, Matrix.diagonal_one]
  have hDdet : D.det * D.det = 1 := by
    rw [← Matrix.det_mul, hDsquare, Matrix.det_one]
  have hsub : (1 + t • orientationSign (carousel (2 * q + 1)) K).submatrix
      (carouselShuffle q) (carouselShuffle q) =
      D * (1 + t • transitiveSign (2 * q + 1) K) * D := by
    have hs := carouselSign_shuffle (K := K) q
    have hsub' : (1 + t • orientationSign (carousel (2 * q + 1)) K).submatrix
        (carouselShuffle q) (carouselShuffle q) =
        1 + t • (D * transitiveSign (2 * q + 1) K * D) := by
      rw [← hs]
      ext i j
      simp [Matrix.submatrix_apply, Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply,
        (carouselShuffle q).injective.eq_iff]
    rw [hsub']
    simp [Matrix.mul_add, Matrix.add_mul, hDsquare]
  calc
    (1 + t • orientationSign (carousel (2 * q + 1)) K).det =
        ((1 + t • orientationSign (carousel (2 * q + 1)) K).submatrix
          (carouselShuffle q) (carouselShuffle q)).det :=
      (Matrix.det_submatrix_equiv_self _ _).symm
    _ = (D * (1 + t • transitiveSign (2 * q + 1) K) * D).det := by rw [hsub]
    _ = (1 + t • transitiveSign (2 * q + 1) K).det := by
      rw [Matrix.det_mul, Matrix.det_mul]
      calc
        D.det * (1 + t • transitiveSign (2 * q + 1) K).det * D.det =
            (D.det * D.det) * (1 + t • transitiveSign (2 * q + 1) K).det := by ring
        _ = _ := by rw [hDdet, one_mul]
    _ = _ := det_one_add_smul_transitiveSign (2 * q + 1) t

/-- The same polynomial for arbitrary odd order, with no fixed-size substitution. -/
theorem det_one_add_smul_carouselSign_odd {K : Type*} [Field K] [CharZero K]
    (n : ℕ) (hn : Odd n) (t : K) :
    (1 + t • orientationSign (carousel n) K).det =
      ((1 + t) ^ n + (1 - t) ^ n) / 2 := by
  rcases hn with ⟨q, hq⟩
  have heq : n = 2 * q + 1 := by omega
  subst n
  exact det_one_add_smul_carouselSign q t

/-- The Boolean sign is exactly the manuscript's rational tournament sign. -/
theorem orientationSign_rat_eq_sign {n : ℕ} (T : Orientation n) :
    orientationSign T ℚ = (toTournament T).sign := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Tournament.sign, orientationSign, toTournament]
  · cases harc : arc T i j <;>
      norm_num [Tournament.sign, toTournament, orientationSign, hij, harc]

/-- Changing coefficient field preserves the encoded tournament signs. -/
theorem orientationSign_map {n : ℕ} (T : Orientation n)
    {K : Type*} [Ring K] (f : ℚ →+* K) :
    (orientationSign T ℚ).map f = orientationSign T K := by
  ext i j
  simp only [Matrix.map_apply, orientationSign]
  split_ifs <;> simp

/-- The actual normalized rational sign matrix maps to (1/n) times the sign matrix. -/
theorem carouselNormalizedSign_map {K : Type*} [Field K] [CharZero K]
    (n : ℕ) :
    ((toTournament (carousel n)).normalizedSign).map (Rat.castHom K) =
      (1 / (n : K)) • orientationSign (carousel n) K := by
  have hs := orientationSign_map (carousel n) (Rat.castHom K)
  rw [orientationSign_rat_eq_sign] at hs
  ext i j
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j) hs
  simp only [Matrix.map_apply] at hentry
  simp only [Tournament.normalizedSign, Matrix.map_apply, map_div₀, map_natCast,
    Matrix.smul_apply, smul_eq_mul]
  rw [hentry]
  ring

/-- Closed determinant formula for the actual normalized carousel sign used in the paper. -/
theorem det_one_add_smul_carouselNormalizedSign {K : Type*} [Field K] [CharZero K]
    (n : ℕ) (hn : Odd n) (t : K) :
    (1 + t • ((toTournament (carousel n)).normalizedSign).map (Rat.castHom K)).det =
      ((1 + t / (n : K)) ^ n + (1 - t / (n : K)) ^ n) / 2 := by
  rw [carouselNormalizedSign_map, smul_smul]
  simpa [div_eq_mul_inv] using det_one_add_smul_carouselSign_odd n hn (t / (n : K))

end
end Wormald
