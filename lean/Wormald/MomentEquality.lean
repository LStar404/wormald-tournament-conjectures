import Wormald.MomentBound
import Wormald.ComparisonEquality

namespace Wormald

noncomputable section
open Matrix Finset

/-- A column attaining an upper moment bound attains every smaller moment bound. -/
theorem pow_column_energy_eq_descends {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A j i = -A i j) (hbound : ∀ i j, |A i j| ≤ 1)
    (p q : ℕ) (hqp : q ≤ p) (j : Fin n)
    (heq : (∑ i, (A ^ p) i j ^ 2) = ∑ i, (transitiveSign n ℝ ^ p) i j ^ 2) :
    (∑ i, (A ^ q) i j ^ 2) = ∑ i, (transitiveSign n ℝ ^ q) i j ^ 2 := by
  have hn0 : 0 < n := by omega
  have heqK : (∑ i, (A ^ p *ᵥ Pi.single j 1) i ^ 2) =
      ∑ i, (comparisonMatrix n ^ p *ᵥ sortedAbs (Pi.single j 1)) i ^ 2 := by
    rw [sortedAbs_basisVector hn0 j, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
    change (∑ i, (A ^ p) i j ^ 2) = ∑ i, (comparisonMatrix n ^ p) i ⟨0, hn0⟩ ^ 2
    rw [heq, comparison_column_energy_zero]
    exact transitive_pow_column_energy_eq n p j ⟨0, hn0⟩
  have hsorted := sortedAbs_pow_mulVec_eq_of_sum_sq_eq A hskew hbound (Pi.single j 1) p heqK
  have htail := sortedAbs_pow_mulVec_eq_descends hn A hskew hbound (Pi.single j 1) p q hqp hsorted
  have hnorm := congrArg (fun y : Fin n → ℝ => ∑ i, y i ^ 2) htail
  rw [sum_sortedAbs_sq, sortedAbs_basisVector hn0 j,
    Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hnorm
  change (∑ i, (A ^ q) i j ^ 2) = ∑ i, (comparisonMatrix n ^ q) i ⟨0, hn0⟩ ^ 2 at hnorm
  rw [comparison_column_energy_zero] at hnorm
  exact hnorm.trans (transitive_pow_column_energy_eq n q ⟨0, hn0⟩ j)

/-- Equality in the full Frobenius moment bound forces equality at every lower
moment. In particular any maximizing p≥2 forces the fourth-trace equality. -/
theorem pow_frobenius_sq_eq_descends {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A j i = -A i j) (hbound : ∀ i j, |A i j| ≤ 1)
    (p q : ℕ) (hqp : q ≤ p)
    (heq : (∑ i, ∑ j, (A ^ p) i j ^ 2) =
      ∑ i, ∑ j, (transitiveSign n ℝ ^ p) i j ^ 2) :
    (∑ i, ∑ j, (A ^ q) i j ^ 2) =
      ∑ i, ∑ j, (transitiveSign n ℝ ^ q) i j ^ 2 := by
  have heqcol : (∑ j, ∑ i, (A ^ p) i j ^ 2) =
      ∑ j, ∑ i, (transitiveSign n ℝ ^ p) i j ^ 2 := by
    calc
      _ = ∑ i, ∑ j, (A ^ p) i j ^ 2 := Finset.sum_comm
      _ = _ := heq
      _ = _ := Finset.sum_comm
  have hgap0 : (∑ j : Fin n, ((∑ i, (transitiveSign n ℝ ^ p) i j ^ 2) -
      ∑ i, (A ^ p) i j ^ 2)) = 0 := by
    rw [Finset.sum_sub_distrib, heqcol, sub_self]
  have hgap_nonneg : ∀ j : Fin n, 0 ≤ (∑ i, (transitiveSign n ℝ ^ p) i j ^ 2) -
      ∑ i, (A ^ p) i j ^ 2 := fun j =>
    sub_nonneg.mpr (pow_column_energy_le_transitive A hskew hbound p j)
  have hcolumns : ∀ j : Fin n, (∑ i, (A ^ p) i j ^ 2) =
      ∑ i, (transitiveSign n ℝ ^ p) i j ^ 2 := by
    intro j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hgap_nonneg j)).mp hgap0 j (by simp)
    linarith
  calc
    _ = ∑ j, ∑ i, (A ^ q) i j ^ 2 := Finset.sum_comm
    _ = ∑ j, ∑ i, (transitiveSign n ℝ ^ q) i j ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact pow_column_energy_eq_descends hn A hskew hbound p q hqp j (hcolumns j)
    _ = _ := Finset.sum_comm

theorem trace_pow_four_eq_frobenius_sq_pow_two {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hskew : ∀ i j, A j i = -A i j) :
    (A ^ 4).trace = ∑ i, ∑ j, (A ^ 2) i j ^ 2 := by
  have htranspose : A.transpose = -A := by ext i j; exact hskew i j
  have hsym : (A ^ 2).transpose = A ^ 2 := by
    rw [Matrix.transpose_pow, htranspose, neg_sq]
  have hpow : A ^ 4 = A ^ 2 * A ^ 2 := by rw [← pow_add]
  rw [hpow]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hij := congrFun (congrFun hsym i) j
  change (A ^ 2) j i = (A ^ 2) i j at hij
  rw [hij]
  ring

/-- Any equality at a power moment p≥2 forces the precise fourth-trace equality
used by the switching classification. -/
theorem trace_four_eq_of_pow_frobenius_sq_eq {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A j i = -A i j) (hbound : ∀ i j, |A i j| ≤ 1)
    (p : ℕ) (hp : 2 ≤ p)
    (heq : (∑ i, ∑ j, (A ^ p) i j ^ 2) =
      ∑ i, ∑ j, (transitiveSign n ℝ ^ p) i j ^ 2) :
    (A ^ 4).trace = (transitiveSign n ℝ ^ 4).trace := by
  have hT : ∀ i j, transitiveSign n ℝ j i = -transitiveSign n ℝ i j := by
    intro i j
    exact congrFun (congrFun (transitiveSign_transpose n) i) j
  rw [trace_pow_four_eq_frobenius_sq_pow_two A hskew,
    trace_pow_four_eq_frobenius_sq_pow_two _ hT]
  exact pow_frobenius_sq_eq_descends hn A hskew hbound p 2 hp heq

end
end Wormald
