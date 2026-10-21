import Wormald.CarouselSwitching
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Rearrangement

/-!
# Concrete finite inequalities underlying Fang–Huang's one-step comparison

The source is Fang–Huang, arXiv:2608.06238v1, Lemma 3.3. The inequalities below
are proved from actual skew-symmetry and entry bounds; the desired majorization
or moment inequality is not included as a hypothesis.
-/

namespace Wormald

open Matrix Finset

/-- Sharp signed-subset cancellation estimate. It holds even for real skew
matrices with entries in [-1,1], so in particular for every tournament sign matrix.
The half double sum is precisely the unordered internal-pair sum in Lemma 3.3. -/
theorem signed_subset_mulVec_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A j i = -A i j) (hbound : ∀ i j, |A i j| ≤ 1)
    (S : Finset (Fin n)) (ε x : Fin n → ℝ)
    (hε : ∀ i, |ε i| ≤ 1) (hx : ∀ i, 0 ≤ x i) :
    (∑ i ∈ S, ε i * (A *ᵥ x) i) ≤
      (S.card : ℝ) * (∑ j ∈ Sᶜ, x j) +
        (∑ i ∈ S, ∑ j ∈ S, |ε i * x j - ε j * x i|) / 2 := by
  let I : ℝ := ∑ i ∈ S, ∑ j ∈ S, ε i * A i j * x j
  let E : ℝ := ∑ i ∈ S, ∑ j ∈ Sᶜ, ε i * A i j * x j
  let J : ℝ := ∑ i ∈ S, ∑ j ∈ S, A i j * (ε i * x j - ε j * x i)
  have hsplit : (∑ i ∈ S, ε i * (A *ᵥ x) i) = I + E := by
    dsimp [I, E]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    exact (Finset.sum_add_sum_compl S (fun j => ε i * (A i j * x j))).symm
  have hswap : (∑ i ∈ S, ∑ j ∈ S, A i j * (ε j * x i)) = -I := by
    calc
      (∑ i ∈ S, ∑ j ∈ S, A i j * (ε j * x i)) =
          ∑ i ∈ S, ∑ j ∈ S, A j i * (ε i * x j) := Finset.sum_comm
      _ = ∑ i ∈ S, ∑ j ∈ S, -(ε i * A i j * x j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hskew]
        ring
      _ = -I := by simp only [I, Finset.sum_neg_distrib]
  have hdouble : J = 2 * I := by
    calc
      J = I - (∑ i ∈ S, ∑ j ∈ S, A i j * (ε j * x i)) := by
        dsimp [J, I]
        simp only [mul_sub, Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 2 * I := by rw [hswap]; ring
  have hcrossTerm : ∀ i j, ε i * A i j * x j ≤ x j := by
    intro i j
    have hab : |ε i * A i j| ≤ 1 := by
      rw [abs_mul]
      calc
        |ε i| * |A i j| ≤ 1 * 1 := mul_le_mul (hε i) (hbound i j) (abs_nonneg _) (by norm_num)
        _ = 1 := by ring
    calc
      ε i * A i j * x j ≤ |ε i * A i j| * x j :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (hx j)
      _ ≤ 1 * x j := mul_le_mul_of_nonneg_right hab (hx j)
      _ = x j := one_mul _
  have hcross : E ≤ (S.card : ℝ) * (∑ j ∈ Sᶜ, x j) := by
    calc
      E ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, x j := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hcrossTerm i j
      _ = _ := by simp [nsmul_eq_mul]
  have hinternal : J ≤ ∑ i ∈ S, ∑ j ∈ S, |ε i * x j - ε j * x i| := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    calc
      A i j * (ε i * x j - ε j * x i) ≤ |A i j * (ε i * x j - ε j * x i)| := le_abs_self _
      _ = |A i j| * |ε i * x j - ε j * x i| := abs_mul _ _
      _ ≤ 1 * |ε i * x j - ε j * x i| :=
        mul_le_mul_of_nonneg_right (hbound i j) (abs_nonneg _)
      _ = _ := one_mul _
  rw [hsplit]
  linarith

/-- Every encoded tournament supplies exactly the concrete hypotheses above. -/
theorem orientationSign_bound {n : ℕ} (T : FiniteModel.Orientation n) (i j : Fin n) :
    |orientationSign T ℝ i j| ≤ 1 := by
  unfold orientationSign
  split_ifs <;> norm_num

theorem orientationSign_skew {n : ℕ} (T : FiniteModel.Orientation n) (i j : Fin n) :
    orientationSign T ℝ j i = -orientationSign T ℝ i j := by
  by_cases h : i = j
  · subst j
    simp
  · exact orientationSign_reverse T j i (Ne.symm h)

/-- The signed-subset estimate specialized to actual tournament orientations. -/
theorem tournament_signed_subset_mulVec_le {n : ℕ} (T : FiniteModel.Orientation n)
    (S : Finset (Fin n)) (ε x : Fin n → ℝ)
    (hε : ∀ i, |ε i| ≤ 1) (hx : ∀ i, 0 ≤ x i) :
    (∑ i ∈ S, ε i * (orientationSign T ℝ *ᵥ x) i) ≤
      (S.card : ℝ) * (∑ j ∈ Sᶜ, x j) +
        (∑ i ∈ S, ∑ j ∈ S, |ε i * x j - ε j * x i|) / 2 :=
  signed_subset_mulVec_le (orientationSign T ℝ) (orientationSign_skew T)
    (orientationSign_bound T) S ε x hε hx

end Wormald
