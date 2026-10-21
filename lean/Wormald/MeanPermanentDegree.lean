import Wormald.MeanPermanent
import Wormald.NonregularDegree

/-! The independent mean bound expressed in the original normalized degrees. -/

namespace Wormald.FiniteModel
noncomputable section
open scoped BigOperators

theorem weightedBase_entry_eq_adjacency {d : ℕ} (base : Orientation d) (i j : Fin d) :
    weightedBase base i j = ((toTournament base).adjacency i j : ℝ) +
      if i = j then 1 / 2 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [weightedBase, toTournament]
  · cases h : arc base i j <;> simp [weightedBase, toTournament, hij, h]

theorem weightedBase_rowSum {d : ℕ} (base : Orientation d) (i : Fin d) :
    (∑ j, weightedBase base i j) = ((∑ j, (toTournament base).adjacency i j : ℚ) : ℝ) + 1 / 2 := by
  simp only [weightedBase_entry_eq_adjacency, Finset.sum_add_distrib, Rat.cast_sum]
  simp

theorem weightedBase_rowSum_eq_degreeFactor {d : ℕ} (base : Orientation d)
    (hd : d ≠ 0) (i : Fin d) :
    (∑ j, weightedBase base i j) = (d : ℝ) / 2 * (toTournament base).degreeFactor i := by
  rw [weightedBase_rowSum]
  unfold Tournament.degreeFactor
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  field_simp

theorem weightedBase_rowProduct_eq_degreeProduct {d : ℕ} (base : Orientation d)
    (hd : d ≠ 0) (m : ℕ) :
    (∏ i, (∑ j, weightedBase base i j) ^ m) =
      ((d : ℝ) / 2) ^ (d * m) * (∏ i, (toTournament base).degreeFactor i) ^ m := by
  simp only [weightedBase_rowSum_eq_degreeFactor base hd, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.prod_pow, ← pow_mul]
  rw [Nat.mul_comm m d]

/-- A direct bound on the actual independent mean by its strict degree product. -/
theorem expectedCycles_le_factorial_degreeProduct {d : ℕ} (base : Orientation d)
    (hd : d ≠ 0) (m : ℕ) :
    (expectedCycles base m : ℝ) ≤
      (Nat.factorial m : ℝ) ^ d * ((d : ℝ) / 2) ^ (d * m) *
        (∏ i, (toTournament base).degreeFactor i) ^ m := by
  have h := expectedCycles_le_factorial_rowSum base m
  rw [weightedBase_rowProduct_eq_degreeProduct base hd, ← mul_assoc] at h
  exact h

end
end Wormald.FiniteModel
