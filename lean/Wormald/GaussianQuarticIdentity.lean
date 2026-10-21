import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-! Exact complete-graph quadratic and quartic identities. These are finite
algebraic tools for the growing-dimensional regular-tournament integral. -/

namespace Wormald
noncomputable section
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def completeSquareEnergy (x : ι → ℝ) : ℝ :=
  (∑ i, ∑ j, (x i - x j) ^ 2) / 2

def completeQuarticEnergy (x : ι → ℝ) : ℝ :=
  (∑ i, ∑ j, (x i - x j) ^ 4) / 2

theorem sum_pair_difference_sq (x : ι → ℝ) :
    (∑ i, ∑ j, (x i - x j) ^ 2) =
      2 * Fintype.card ι * (∑ i, x i ^ 2) - 2 * (∑ i, x i) ^ 2 := by
  have he : ∀ i j, (x i - x j) ^ 2 = x i ^ 2 + x j ^ 2 - 2 * x i * x j := by
    intro i j
    ring
  simp only [he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem sum_pair_difference_four (x : ι → ℝ) :
    (∑ i, ∑ j, (x i - x j) ^ 4) =
      2 * Fintype.card ι * (∑ i, x i ^ 4) -
        8 * (∑ i, x i ^ 3) * (∑ i, x i) + 6 * (∑ i, x i ^ 2) ^ 2 := by
  have he : ∀ i j, (x i - x j) ^ 4 = x i ^ 4 - 4 * x i ^ 3 * x j +
      6 * x i ^ 2 * x j ^ 2 - 4 * x i * x j ^ 3 + x j ^ 4 := by
    intro i j
    ring
  simp only [he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem completeSquareEnergy_eq (x : ι → ℝ) :
    completeSquareEnergy x = Fintype.card ι * (∑ i, x i ^ 2) - (∑ i, x i) ^ 2 := by
  rw [completeSquareEnergy, sum_pair_difference_sq]
  ring

theorem completeQuarticEnergy_eq (x : ι → ℝ) :
    completeQuarticEnergy x = Fintype.card ι * (∑ i, x i ^ 4) -
      4 * (∑ i, x i ^ 3) * (∑ i, x i) + 3 * (∑ i, x i ^ 2) ^ 2 := by
  rw [completeQuarticEnergy, sum_pair_difference_four]
  ring

theorem completeQuarticEnergy_eq_of_sum_zero (x : ι → ℝ) (hx : ∑ i, x i = 0) :
    completeQuarticEnergy x = Fintype.card ι * (∑ i, x i ^ 4) +
      3 * (∑ i, x i ^ 2) ^ 2 := by
  rw [completeQuarticEnergy_eq, hx]
  ring

theorem completeSquareEnergy_sub_const (x : ι → ℝ) (a : ℝ) :
    completeSquareEnergy (fun i => x i - a) = completeSquareEnergy x := by
  unfold completeSquareEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

theorem completeQuarticEnergy_sub_const (x : ι → ℝ) (a : ℝ) :
    completeQuarticEnergy (fun i => x i - a) = completeQuarticEnergy x := by
  unfold completeQuarticEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

theorem half_symmetric_sum_eq_sum_lt [LinearOrder ι] (f : ι → ι → ℝ)
    (hsym : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) / 2 = ∑ i, ∑ j, if i < j then f i j else 0 := by
  have hp : ∀ i j, f i j = (if i < j then f i j else 0) +
      (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, not_lt_of_gt hij]
    · subst j
      simp [hdiag]
    · simp [hij, not_lt_of_gt hij]
  have hswap : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    simp_rw [hsym]
  have he : (∑ i, ∑ j, f i j) =
      2 * ∑ i, ∑ j, if i < j then f i j else 0 := by
    calc
      _ = ∑ i, ∑ j, ((if i < j then f i j else 0) +
          (if j < i then f i j else 0)) := by simp only [← hp]
      _ = _ := by simp only [Finset.sum_add_distrib, hswap]; ring
  rw [he]
  ring

theorem completeSquareEnergy_eq_sum_lt [LinearOrder ι] (x : ι → ℝ) :
    completeSquareEnergy x = ∑ i, ∑ j, if i < j then (x i - x j) ^ 2 else 0 := by
  apply half_symmetric_sum_eq_sum_lt
  · intro i j; ring
  · intro i; simp

theorem completeQuarticEnergy_eq_sum_lt [LinearOrder ι] (x : ι → ℝ) :
    completeQuarticEnergy x = ∑ i, ∑ j, if i < j then (x i - x j) ^ 4 else 0 := by
  apply half_symmetric_sum_eq_sum_lt
  · intro i j; ring
  · intro i; simp

end
end Wormald
