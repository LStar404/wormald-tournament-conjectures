import Wormald.OneStepComparison
import Wormald.PrefixDominated

namespace Wormald

noncomputable section
open Matrix Finset

/-- Fang–Huang's comparison matrix, defined by its exact column-prefix sums.
The definition makes the relation to the sharp subset weights explicit. -/
def comparisonMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  comparisonWeights n (i.val + 1) j - comparisonWeights n i.val j

@[simp] theorem comparisonWeights_zero (n : ℕ) (j : Fin n) :
    comparisonWeights n 0 j = 0 := by
  simp [comparisonWeights, j.isLt]

/-- Column-prefix sums of the actual comparison operator are exactly the weights
proved in the one-step rearrangement inequality. -/
theorem prefixSum_comparisonMatrix_mulVec {n : ℕ} (x : Fin n → ℝ)
    (r : ℕ) (hr : r ≤ n) :
    prefixSum (comparisonMatrix n *ᵥ x) r =
      ∑ j : Fin n, comparisonWeights n r j * x j := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [prefixSum_succ _ r (by omega), ih (by omega)]
    simp only [Matrix.mulVec, dotProduct, comparisonMatrix]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring

private theorem card_prefixSet (n r : ℕ) (hr : r ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < r)).card = r := by
  by_cases heq : r = n
  · subst r
    simp
  · have hlt : r < n := by omega
    have hset : Finset.univ.filter (fun i : Fin n => i.val < r) = Finset.Iio ⟨r, hlt⟩ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
      rfl
    rw [hset, Fin.card_Iio]

/-- Fang–Huang Lemma 3.3, now as a complete general weak-majorization theorem.
It holds for every real skew matrix with entries in [-1,1], not merely sign matrices. -/
theorem sortedAbs_mulVec_prefixDominated {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A j i = -A i j) (hbound : ∀ i j, |A i j| ≤ 1)
    (x : Fin n → ℝ) :
    PrefixDominated (sortedAbs (A *ᵥ x)) (comparisonMatrix n *ᵥ sortedAbs x) := by
  intro r hr
  let p := descendingPermutation (fun i => |(A *ᵥ x) i|)
  let P := Finset.univ.filter (fun i : Fin n => i.val < r)
  let S := P.image p
  have hcard : S.card = r := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ p.injective]
    exact card_prefixSet n r hr
  have hsum : prefixSum (sortedAbs (A *ᵥ x)) r = ∑ i ∈ S, |(A *ᵥ x) i| := by
    dsimp [S]
    rw [Finset.sum_image (fun i hi j hj hij => p.injective hij)]
    rfl
  rw [hsum, prefixSum_comparisonMatrix_mulVec _ r hr]
  have h := subset_abs_mulVec_le_comparisonWeights A hskew hbound S x
  rwa [hcard] at h

/-- The comparison operator preserves prefix domination. The hypothesis on its
input is only the prefix order itself; no desired matrix-power inequality is assumed. -/
theorem comparisonMatrix_preserves_prefixDominated {n : ℕ} (x y : Fin n → ℝ)
    (hxy : PrefixDominated x y) :
    PrefixDominated (comparisonMatrix n *ᵥ x) (comparisonMatrix n *ᵥ y) := by
  intro r hr
  rw [prefixSum_comparisonMatrix_mulVec _ r hr, prefixSum_comparisonMatrix_mulVec _ r hr]
  exact prefixDominated_weighted_sum_le x y (comparisonWeights n r) hxy
    (comparisonWeights_antitone n r) (comparisonWeights_nonneg n r hr)

end
end Wormald
