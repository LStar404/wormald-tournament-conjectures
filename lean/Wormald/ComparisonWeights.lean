import Wormald.PairDistance

namespace Wormald

open Finset
noncomputable section

private def extremesPermutation (r : ℕ) : Equiv.Perm (Fin r) where
  toFun i := ⟨if i.val % 2 = 0 then i.val / 2 else r - 1 - i.val / 2, by
    have hi := i.isLt
    split_ifs <;> omega⟩
  invFun j := ⟨if 2 * j.val < r then 2 * j.val else 2 * (r - 1 - j.val) + 1, by
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

private theorem extremesPermutation_val (r : ℕ) (i : Fin r) :
    (extremesPermutation r i).val =
      if i.val % 2 = 0 then i.val / 2 else r - 1 - i.val / 2 := rfl

private theorem abs_pair_raw_extremes (r : ℕ) (i : Fin r) :
    |(r : ℝ) - 1 - 2 * (extremesPermutation r i).val| =
      (r : ℝ) - 1 - 2 * (i.val / 2 : ℕ) := by
  have hi := i.isLt
  have hnat : 2 * (i.val / 2) + 1 ≤ r := by omega
  have hreal : 2 * (i.val / 2 : ℕ) + (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hnat
  rw [extremesPermutation_val]
  by_cases hpar : i.val % 2 = 0
  · rw [ite_eq_left hpar]
    exact abs_of_nonneg (by linarith)
  · rw [ite_eq_right hpar]
    have h₁ : 1 ≤ r := by omega
    have h₂ : i.val / 2 ≤ r - 1 := by omega
    rw [Nat.cast_sub h₂, Nat.cast_sub h₁]
    push_cast
    rw [abs_of_nonpos (by linarith : (r : ℝ) - 1 - 2 * ((r : ℝ) - 1 - (i.val / 2 : ℕ)) ≤ 0)]
    ring

/-- Explicit source coefficients: r−1,r−1,r−3,r−3,… . -/
theorem pairCoefficients_eq (r : ℕ) (i : Fin r) :
    pairCoefficients r i = (r : ℝ) - 1 - 2 * (i.val / 2 : ℕ) := by
  let raw : Fin r → ℝ := fun i => (r : ℝ) - 1 - 2 * i.val
  have hp : Antitone (fun i => |raw (extremesPermutation r i)|) := by
    intro i j hij
    simp only [raw, abs_pair_raw_extremes]
    have hnat : i.val / 2 ≤ j.val / 2 := by omega
    have hreal : (i.val / 2 : ℕ) ≤ (j.val / 2 : ℕ) := hnat
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left (by exact_mod_cast hreal) (by norm_num)) _
  have hs := sortedAbs_antitone raw
  have heq := Tuple.unique_antitone (f := fun i => |raw i|)
    (σ := descendingPermutation (fun i => |raw i|)) (τ := extremesPermutation r) hs hp
  calc
    pairCoefficients r i = |raw (extremesPermutation r i)| := congrFun heq i
    _ = _ := abs_pair_raw_extremes r i

/-- Prefix weights for the source comparison matrix, with zero-based columns. -/
def comparisonWeights (n r : ℕ) (j : Fin n) : ℝ :=
  if j.val < n - r then (r : ℝ)
  else (r : ℝ) - 1 - 2 * ((j.val - (n - r)) / 2 : ℕ)

theorem comparisonWeights_antitone (n r : ℕ) : Antitone (comparisonWeights n r) := by
  intro i j hij
  have hval : i.val ≤ j.val := hij
  by_cases hi : i.val < n - r
  · by_cases hj : j.val < n - r
    · simp [comparisonWeights, hi, hj]
    · simp only [comparisonWeights, ite_eq_left hi, ite_eq_right hj]
      have hnn : 0 ≤ (((j.val - (n - r)) / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  · by_cases hj : j.val < n - r
    · omega
    · simp only [comparisonWeights, ite_eq_right hi, ite_eq_right hj]
      have hnat : (i.val - (n - r)) / 2 ≤ (j.val - (n - r)) / 2 := by omega
      have hreal : (((i.val - (n - r)) / 2 : ℕ) : ℝ) ≤
          (((j.val - (n - r)) / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
      linarith

theorem comparisonWeights_nonneg (n r : ℕ) (hr : r ≤ n) (j : Fin n) :
    0 ≤ comparisonWeights n r j := by
  unfold comparisonWeights
  split_ifs with hj
  · exact Nat.cast_nonneg _
  · have hjlt := j.isLt
    have hnat : 2 * ((j.val - (n - r)) / 2) + 1 ≤ r := by omega
    have hreal : 2 * (((j.val - (n - r)) / 2 : ℕ) : ℝ) + 1 ≤ (r : ℝ) := by
      exact_mod_cast hnat
    linarith

end
end Wormald
