import Wormald.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The strict degree-product loss for a nonregular base

This is the arithmetic part of the nonregular argument in Appendix A.3.
It does not assert the separate permanent bound on Hamilton counts.
-/

namespace Wormald
noncomputable section
open scoped BigOperators

def Tournament.degreeFactor {d : ℕ} (T : Tournament d) (i : Fin d) : ℝ :=
  (2 * ((∑ j, T.adjacency i j : ℚ) : ℝ) + 1) / (d : ℝ)

theorem Tournament.sum_sign_eq_zero {d : ℕ} (T : Tournament d) :
    ∑ i, ∑ j, T.sign i j = 0 := by
  have hswap : (∑ i, ∑ j, T.sign i j) = -(∑ i, ∑ j, T.sign i j) := by
    calc
      (∑ i, ∑ j, T.sign i j) = ∑ i, ∑ j, T.sign j i := Finset.sum_comm
      _ = -(∑ i, ∑ j, T.sign i j) := by
        have hentry (i j : Fin d) : T.sign j i = -T.sign i j :=
          congrArg (fun M : Matrix (Fin d) (Fin d) ℚ => M i j) T.sign_skew
        calc
          (∑ i, ∑ j, T.sign j i) = ∑ i, ∑ j, -T.sign i j := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            exact hentry i j
          _ = _ := by simp only [Finset.sum_neg_distrib]
  linarith

theorem Tournament.sum_adjacency {d : ℕ} (T : Tournament d) :
    2 * (∑ i, ∑ j, T.adjacency i j) = (d : ℚ) * ((d : ℚ) - 1) := by
  have h := T.sum_sign_eq_zero
  simp only [Tournament.sign, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum] at h
  have hdiag : (∑ i : Fin d, ∑ j : Fin d, if i = j then (1 : ℚ) else 0) = d := by
    simp
  rw [hdiag] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  nlinarith

theorem Tournament.degreeFactor_pos {d : ℕ} (T : Tournament d) (hd : d ≠ 0)
    (i : Fin d) : 0 < T.degreeFactor i := by
  have hnonneg : (0 : ℚ) ≤ ∑ j, T.adjacency i j := by
    apply Finset.sum_nonneg
    intro j _
    rcases T.zero_or_one i j with h | h <;> simp [h]
  have hnR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hrow : (0 : ℝ) ≤ ((∑ j, T.adjacency i j : ℚ) : ℝ) := by exact_mod_cast hnonneg
  unfold Tournament.degreeFactor
  exact div_pos (by linarith) hnR

theorem Tournament.sum_degreeFactor {d : ℕ} (T : Tournament d) (hd : d ≠ 0) :
    ∑ i, T.degreeFactor i = (d : ℝ) := by
  have htotal : 2 * (∑ i, ((∑ j, T.adjacency i j : ℚ) : ℝ)) =
      (d : ℝ) * ((d : ℝ) - 1) := by exact_mod_cast T.sum_adjacency
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  simp only [Tournament.degreeFactor, ← Finset.sum_div, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  apply (div_eq_iff hdR).mpr
  nlinarith

theorem Tournament.degreeFactor_eq_one_iff {d : ℕ} (T : Tournament d)
    (hd : d ≠ 0) : (∀ i, T.degreeFactor i = 1) ↔ T.Regular := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  constructor
  · intro h i
    have hi := (div_eq_one_iff_eq hdR).mp (h i)
    have hrow : ((∑ j, T.adjacency i j : ℚ) : ℝ) = ((d : ℝ) - 1) / 2 := by
      linarith
    exact_mod_cast hrow
  · intro h i
    unfold Tournament.degreeFactor
    rw [h i]
    push_cast
    field_simp
    ring

/-- Strict AM–GM in the exact degree normalization used by the manuscript. -/
theorem Tournament.degreeProduct_lt_one {d : ℕ} (T : Tournament d)
    (hd : d ≠ 0) (hnreg : ¬ T.Regular) :
    ∏ i, T.degreeFactor i < 1 := by
  have hp (i : Fin d) := T.degreeFactor_pos hd i
  have hnot : ∃ i, T.degreeFactor i ≠ 1 := by
    by_contra h
    push Not at h
    exact hnreg ((T.degreeFactor_eq_one_iff hd).mp h)
  obtain ⟨i, hi⟩ := hnot
  have hlog : (∑ j, Real.log (T.degreeFactor j)) < ∑ j, (T.degreeFactor j - 1) := by
    apply Finset.sum_lt_sum
    · intro j _
      exact Real.log_le_sub_one_of_pos (hp j)
    · exact ⟨i, Finset.mem_univ i, Real.log_lt_sub_one_of_pos (hp i) hi⟩
  have hsum : (∑ j, (T.degreeFactor j - 1)) = 0 := by
    simp [Finset.sum_sub_distrib, T.sum_degreeFactor hd]
  rw [hsum] at hlog
  have hprod : 0 < ∏ j, T.degreeFactor j := Finset.prod_pos (fun j _ => hp j)
  apply (Real.log_neg_iff hprod).mp
  rwa [Real.log_prod (fun j _ => (hp j).ne')]

/-- The geometric-mean degree loss κ of Appendix A.3, written using exp/log. -/
def Tournament.degreeLoss {d : ℕ} (T : Tournament d) : ℝ :=
  Real.exp (Real.log (∏ i, T.degreeFactor i) / (d : ℝ))

theorem Tournament.degreeLoss_pos {d : ℕ} (T : Tournament d) :
    0 < T.degreeLoss := Real.exp_pos _

theorem Tournament.degreeLoss_lt_one {d : ℕ} (T : Tournament d)
    (hd : d ≠ 0) (hnreg : ¬ T.Regular) : T.degreeLoss < 1 := by
  apply Real.exp_lt_one_iff.mpr
  apply div_neg_of_neg_of_pos
  · exact Real.log_neg (Finset.prod_pos (fun i _ => T.degreeFactor_pos hd i))
      (T.degreeProduct_lt_one hd hnreg)
  · exact_mod_cast Nat.pos_of_ne_zero hd

/-- Every fixed polynomial factor is absorbed by this actual strict loss.
The separate Hamilton-count upper bound is not assumed to have been proved here. -/
theorem Tournament.tendsto_polynomial_degreeLoss {d : ℕ} (T : Tournament d)
    (hd : d ≠ 0) (hnreg : ¬ T.Regular) (k : ℕ) :
    Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ k * T.degreeLoss ^ N)
      Filter.atTop (nhds 0) :=
  tendsto_pow_const_mul_const_pow_of_lt_one k T.degreeLoss_pos.le
    (T.degreeLoss_lt_one hd hnreg)

end
end Wormald
