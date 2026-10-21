import Wormald.FourthMomentIdentity
import Wormald.SignClassification
import Wormald.MomentComparison
import Mathlib.Data.Finset.Sort

namespace Wormald
noncomputable section
open scoped BigOperators
open Matrix FiniteModel

def FourDistinct {ι : Type*} (a b c d : ι) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

instance {ι : Type*} [DecidableEq ι] (a b c d : ι) : Decidable (FourDistinct a b c d) := by
  unfold FourDistinct
  infer_instance

private theorem pfaffianFour_transitive_sq_le {n : ℕ} (a b c d : Fin n) :
    pfaffianFour (transitiveSign n ℝ) a b c d ^ 2 ≤ 1 := by
  simp only [pfaffianFour, transitiveSign]
  split_ifs <;> first | omega | norm_num

private theorem pfaffianFour_eq_zero_of_not_distinct {ι : Type*}
    (A : Matrix ι ι ℝ) (hdiag : ∀ i, A i i = 0)
    (hskew : ∀ i j, A j i = -A i j)
    (a b c d : ι) (hd : ¬FourDistinct a b c d) :
    pfaffianFour A a b c d = 0 := by
  simp only [FourDistinct, not_and_or, not_not] at hd
  rcases hd with hab | hac | had | hbc | hbd | hcd
  · subst b; simp [pfaffianFour, hdiag]; ring
  · subst c; simp only [pfaffianFour, hdiag, zero_mul, sub_zero]
    rw [hskew a b]; ring
  · subst d; simp only [pfaffianFour, hdiag, zero_mul, add_zero]
    rw [hskew a c, hskew a b]; ring
  · subst c; simp [pfaffianFour, hdiag]
  · subst d; simp only [pfaffianFour, hdiag, mul_zero, sub_zero]
    rw [hskew b c]; ring
  · subst d; simp [pfaffianFour, hdiag]

theorem pfaffianFour_sq_ge_one {n : ℕ} (T : Orientation n)
    (a b c d : Fin n) (hd : FourDistinct a b c d) :
    1 ≤ pfaffianFour (orientationSign T ℝ) a b c d ^ 2 := by
  rcases hd with ⟨hab,hac,had,hbc,hbd,hcd⟩
  simp only [pfaffianFour, orientationSign, ite_eq_right hab, ite_eq_right hac,
    ite_eq_right had, ite_eq_right hbc, ite_eq_right hbd, ite_eq_right hcd]
  cases arc T a b <;> cases arc T a c <;> cases arc T a d <;>
    cases arc T b c <;> cases arc T b d <;> cases arc T c d <;> norm_num

private theorem transitiveSign_eq_orientationSign (n : ℕ) :
    transitiveSign n ℝ = orientationSign (fun _ => true : Orientation n) ℝ := by
  ext i j
  simp only [transitiveSign, orientationSign, arc]
  split_ifs <;> first | omega | simp_all

private theorem transitiveSign_skew (n : ℕ) (i j : Fin n) :
    transitiveSign n ℝ j i = -transitiveSign n ℝ i j := by
  simp only [transitiveSign]
  split_ifs <;> first | omega | norm_num

theorem pfaffianFour_transitive_sq {n : ℕ} (a b c d : Fin n) :
    pfaffianFour (transitiveSign n ℝ) a b c d ^ 2 =
      if FourDistinct a b c d then 1 else 0 := by
  by_cases hd : FourDistinct a b c d
  · rw [ite_eq_left hd]
    apply le_antisymm (pfaffianFour_transitive_sq_le a b c d)
    rw [transitiveSign_eq_orientationSign]
    exact pfaffianFour_sq_ge_one _ a b c d hd
  · rw [ite_eq_right hd, pfaffianFour_eq_zero_of_not_distinct _
      (fun i => by simp [transitiveSign]) (transitiveSign_skew n) a b c d hd]
    norm_num

theorem pfaffianFour_sq_ge_transitive {n : ℕ} (T : Orientation n)
    (a b c d : Fin n) :
    pfaffianFour (transitiveSign n ℝ) a b c d ^ 2 ≤
      pfaffianFour (orientationSign T ℝ) a b c d ^ 2 := by
  rw [pfaffianFour_transitive_sq]
  split_ifs with hd
  · exact pfaffianFour_sq_ge_one T a b c d hd
  · exact sq_nonneg _

private theorem orientationSign_sq_eq_transitive {n : ℕ} (T : Orientation n)
    (i j : Fin n) : orientationSign T ℝ i j ^ 2 = transitiveSign n ℝ i j ^ 2 := by
  by_cases hij : i = j
  · subst j; simp [transitiveSign]
  · simp only [orientationSign, ite_eq_right hij, transitiveSign]
    split_ifs <;> first | omega | norm_num

/-- Equality of fourth traces forces every ordered four-vertex Pfaffian square
to equal the transitive value. In particular no four-vertex diamond survives. -/
theorem pfaffianFour_sq_eq_transitive_of_trace_eq {n : ℕ} (T : Orientation n)
    (heq : ((orientationSign T ℝ) ^ 4).trace = ((transitiveSign n ℝ) ^ 4).trace)
    (a b c d : Fin n) :
    pfaffianFour (orientationSign T ℝ) a b c d ^ 2 =
      pfaffianFour (transitiveSign n ℝ) a b c d ^ 2 := by
  have henergy : (∑ i, ∑ j, orientationSign T ℝ i j ^ 2) =
      ∑ i, ∑ j, transitiveSign n ℝ i j ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_congr rfl (fun j _ => orientationSign_sq_eq_transitive T i j)
  have hsum :
      (∑ v : Fin n × Fin n × Fin n × Fin n,
        pfaffianFour (transitiveSign n ℝ) v.1 v.2.1 v.2.2.1 v.2.2.2 ^ 2) =
      ∑ v : Fin n × Fin n × Fin n × Fin n,
        pfaffianFour (orientationSign T ℝ) v.1 v.2.1 v.2.2.1 v.2.2.2 ^ 2 := by
    rw [pfaffianFour_sum_sq _ (transitiveSign_skew n),
      pfaffianFour_sum_sq _ (orientationSign_skew T), henergy, heq]
  have hall := (Finset.sum_eq_sum_iff_of_le
    (fun v (_ : v ∈ (Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n))) =>
      pfaffianFour_sq_ge_transitive T v.1 v.2.1 v.2.2.1 v.2.2.2)).mp hsum
  exact (hall (a,b,c,d) (Finset.mem_univ _)).symm

/-- Fourth-moment equality has the exact structural conclusion: the actual
tournament is a signed permutation of the transitive tournament. -/
theorem signed_permutation_of_fourth_trace_eq {n : ℕ} (T : Orientation n)
    (heq : ((orientationSign T ℝ) ^ 4).trace = ((transitiveSign n ℝ) ^ 4).trace) :
    ∃ (σ : Equiv.Perm (Fin n)) (ε : Fin n → ℝ),
      (∀ i, ε i ^ 2 = 1) ∧ ∀ i j,
        orientationSign T ℝ (σ i) (σ j) = ε i * transitiveSign n ℝ i j * ε j := by
  apply signed_permutation_of_pfaffian_bound T
  intro a b c d
  rw [pfaffianFour_sq_eq_transitive_of_trace_eq T heq,
    pfaffianFour_transitive_sq]
  split_ifs <;> norm_num

end
end Wormald
