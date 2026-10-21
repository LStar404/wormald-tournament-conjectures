import Wormald.ComparisonPowers
import Wormald.ComparisonGram
import Wormald.TransitiveMoments

namespace Wormald

noncomputable section
open Matrix Finset

theorem sortedAbs_basisVector {n : ℕ} (hn : 0 < n) (j : Fin n) :
    sortedAbs (Pi.single j (1 : ℝ)) = Pi.single ⟨0, hn⟩ 1 := by
  let z : Fin n := ⟨0, hn⟩
  have hcomp : (fun i : Fin n => (Pi.single j (1 : ℝ) : Fin n → ℝ) (Equiv.swap j z i)) =
      (Pi.single z 1 : Fin n → ℝ) := by
    funext i
    simp only [Pi.single_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  have hs := sortedAbs_comp_perm (Pi.single j (1 : ℝ)) (Equiv.swap j z)
  rw [hcomp] at hs
  have hzanti : Antitone (Pi.single z (1 : ℝ)) := by
    intro i k hik
    have hiv := i.isLt
    have hkv := k.isLt
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
    simp_all [z, Fin.ext_iff, Fin.le_def]
  have hz0 : ∀ i : Fin n, 0 ≤ (Pi.single z (1 : ℝ) : Fin n → ℝ) i := by
    intro i
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  rw [sortedAbs_eq_self_of_antitone_nonneg _ hzanti hz0] at hs
  exact hs.symm

/-- A sharp column bound for every power of an actual real skew matrix in [-1,1].
The reference is the genuine transitive sign matrix, not an arbitrary comparison family. -/
theorem pow_column_energy_le_transitive_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A j i = -A i j) (hbound : ∀ i j, |A i j| ≤ 1)
    (hn : 0 < n) (p : ℕ) (j : Fin n) :
    (∑ i, (A ^ p) i j ^ 2) ≤
      ∑ i, (transitiveSign n ℝ ^ p) i ⟨0, hn⟩ ^ 2 := by
  have h := pow_mulVec_sum_sq_le_comparison A hskew hbound (Pi.single j 1) p
  rw [sortedAbs_basisVector hn j, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  change (∑ i, (A ^ p) i j ^ 2) ≤ ∑ i, (comparisonMatrix n ^ p) i ⟨0, hn⟩ ^ 2 at h
  rwa [comparison_column_energy_zero n hn p] at h

theorem pow_column_energy_le_transitive {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A j i = -A i j) (hbound : ∀ i j, |A i j| ≤ 1)
    (p : ℕ) (j : Fin n) :
    (∑ i, (A ^ p) i j ^ 2) ≤ ∑ i, (transitiveSign n ℝ ^ p) i j ^ 2 := by
  have hn : 0 < n := by have := j.isLt; omega
  exact (pow_column_energy_le_transitive_zero A hskew hbound hn p j).trans_eq
    (transitive_pow_column_energy_eq n p ⟨0, hn⟩ j)

/-- All power moments of an actual bounded real skew matrix are bounded by the
transitive tournament. This theorem has no majorization or moment assumptions. -/
theorem pow_frobenius_sq_le_transitive {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A j i = -A i j) (hbound : ∀ i j, |A i j| ≤ 1)
    (p : ℕ) :
    (∑ i, ∑ j, (A ^ p) i j ^ 2) ≤
      ∑ i, ∑ j, (transitiveSign n ℝ ^ p) i j ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
    calc
      _ = ∑ j, ∑ i, (A ^ p) i j ^ 2 := Finset.sum_comm
      _ ≤ ∑ j : Fin n, ∑ i, (transitiveSign n ℝ ^ p) i ⟨0, hn0⟩ ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        exact pow_column_energy_le_transitive_zero A hskew hbound hn0 p j
      _ = ∑ j : Fin n, ∑ i, (transitiveSign n ℝ ^ p) i j ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact transitive_pow_column_energy_eq n p ⟨0, hn0⟩ j
      _ = _ := Finset.sum_comm

/-- The all-moment inequality specialized to the faithful finite tournament model. -/
theorem tournament_pow_frobenius_sq_le_transitive {n : ℕ} (T : FiniteModel.Orientation n)
    (p : ℕ) :
    (∑ i, ∑ j, (orientationSign T ℝ ^ p) i j ^ 2) ≤
      ∑ i, ∑ j, (transitiveSign n ℝ ^ p) i j ^ 2 :=
  pow_frobenius_sq_le_transitive _ (orientationSign_skew T) (orientationSign_bound T) p

end
end Wormald
