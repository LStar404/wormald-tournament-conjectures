import Wormald.ComparisonWeights

namespace Wormald

noncomputable section
open Finset

/-- Merging the r selected weights with n−r outside weights and applying
rearrangement is exactly the final optimization in Fang–Huang Lemma 3.3. -/
theorem concat_pairCoefficients_le {n a r : ℕ} (hcard : a + r = n)
    (e : Fin a ⊕ Fin r ≃ Fin n) (x : Fin n → ℝ) :
    (r : ℝ) * (∑ i : Fin a, x (e (Sum.inl i))) +
      (∑ i : Fin r, pairCoefficients r i * x (e (Sum.inr i))) ≤
      ∑ j : Fin n, comparisonWeights n r j * sortedAbs x j := by
  let E : Fin a ⊕ Fin r ≃ Fin n := finSumFinEquiv.trans (finCongr hcard)
  let p : Equiv.Perm (Fin n) := E.symm.trans e
  have hr : r ≤ n := by omega
  have hna : n - r = a := by omega
  have hweight_left : ∀ i : Fin a, comparisonWeights n r (E (Sum.inl i)) = (r : ℝ) := by
    intro i
    have hv : (E (Sum.inl i)).val = i.val := by simp [E]
    simp only [comparisonWeights, hv, hna]
    rw [ite_eq_left i.isLt]
  have hweight_right : ∀ i : Fin r, comparisonWeights n r (E (Sum.inr i)) = pairCoefficients r i := by
    intro i
    have hv : (E (Sum.inr i)).val = a + i.val := by simp [E]
    simp only [comparisonWeights, hv, hna, Nat.add_sub_cancel_left]
    rw [ite_eq_right (by omega), pairCoefficients_eq]
  have hsum : (∑ j : Fin n, comparisonWeights n r j * x (p j)) =
      (r : ℝ) * (∑ i : Fin a, x (e (Sum.inl i))) +
      (∑ i : Fin r, pairCoefficients r i * x (e (Sum.inr i))) := by
    rw [← Equiv.sum_comp E (fun j => comparisonWeights n r j * x (p j))]
    rw [Fintype.sum_sum_type]
    simp only [p, Equiv.trans_apply, Equiv.symm_apply_apply, hweight_left, hweight_right,
      ← Finset.mul_sum]
  have hbound := dot_le_sortedAbs_dot (comparisonWeights n r) (fun j => x (p j))
  rw [sortedAbs_comp_perm x p,
    sortedAbs_eq_self_of_antitone_nonneg _ (comparisonWeights_antitone n r)
      (comparisonWeights_nonneg n r hr)] at hbound
  rw [hsum] at hbound
  exact hbound

end
end Wormald
