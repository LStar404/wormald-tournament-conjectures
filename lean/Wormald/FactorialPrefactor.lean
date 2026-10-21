import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! The factorial normalization of a fixed number of equal blocks has only
polynomial cost. This estimate will combine the actual block permanent bound
with the strict nonregular degree-product loss. -/

namespace Wormald
noncomputable section

def factorialPrefactor (d m : ℕ) : ℝ :=
  (Nat.factorial m : ℝ) ^ d * (d : ℝ) ^ (d * m) / (Nat.factorial (d * m) : ℝ)

theorem factorialPrefactor_eq_stirling (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    factorialPrefactor d m =
      (Stirling.stirlingSeq m ^ d / Stirling.stirlingSeq (d * m)) *
        (Real.sqrt (2 * (m : ℝ)) ^ d / Real.sqrt (2 * ((d * m : ℕ) : ℝ))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : Real.sqrt (2 * (m : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hN : ((d * m : ℕ) : ℝ) ≠ 0 := by positivity
  have hsN : Real.sqrt (2 * ((d * m : ℕ) : ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have he := (Real.exp_pos (1 : ℝ)).ne'
  have hf : (Nat.factorial (d * m) : ℝ) ≠ 0 := by positivity
  have hpow : (((m : ℝ) / Real.exp 1) ^ m) ^ d * (d : ℝ) ^ (d * m) =
      (((d * m : ℕ) : ℝ) / Real.exp 1) ^ (d * m) := by
    rw [← pow_mul, Nat.mul_comm m d, ← mul_pow]
    congr 1
    push_cast
    ring
  unfold factorialPrefactor Stirling.stirlingSeq
  rw [div_pow, mul_pow]
  field_simp
  simpa only [mul_comm] using hpow

/-- For every positive fixed number of blocks, the normalization ratio is
bounded by a constant times m^d, uniformly for positive block orders. -/
theorem factorialPrefactor_polynomial_bound (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m →
      factorialPrefactor d m ≤ C * (m : ℝ) ^ d := by
  obtain ⟨a, ha, hlower⟩ := Stirling.stirlingSeq'_bounded_by_pos_constant
  let B := Stirling.stirlingSeq 1
  have hB : 0 < B := by dsimp [B]; rw [Stirling.stirlingSeq_one]; positivity
  refine ⟨B ^ d / a * (2 : ℝ) ^ d, by positivity, ?_⟩
  intro m hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hdm : 0 < d * m := Nat.mul_pos hd hm
  have hupper : Stirling.stirlingSeq m ≤ B := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    exact Stirling.stirlingSeq'_antitone (Nat.zero_le k)
  have hlow : a ≤ Stirling.stirlingSeq (d * m) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdm)
    rw [hk]
    exact hlower k
  have hratio : Stirling.stirlingSeq m ^ d / Stirling.stirlingSeq (d * m) ≤ B ^ d / a := by
    apply div_le_div₀ (by positivity) (pow_le_pow_left₀ (by
      unfold Stirling.stirlingSeq; positivity) hupper d) ha hlow
  have hs : Real.sqrt (2 * (m : ℝ)) ≤ 2 * (m : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hsN : 1 ≤ Real.sqrt (2 * ((d * m : ℕ) : ℝ)) := by
    apply Real.one_le_sqrt.mpr
    have hN : (1 : ℝ) ≤ (d * m : ℕ) := by exact_mod_cast hdm
    linarith
  have hsratio : Real.sqrt (2 * (m : ℝ)) ^ d /
      Real.sqrt (2 * ((d * m : ℕ) : ℝ)) ≤ (2 * (m : ℝ)) ^ d := by
    calc
      _ ≤ Real.sqrt (2 * (m : ℝ)) ^ d / 1 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hsN
      _ ≤ (2 * (m : ℝ)) ^ d := by
        simpa using pow_le_pow_left₀ (Real.sqrt_nonneg _) hs d
  rw [factorialPrefactor_eq_stirling d m hd hm]
  calc
    _ ≤ (B ^ d / a) * (2 * (m : ℝ)) ^ d :=
      mul_le_mul hratio hsratio (by positivity) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- The factorial prefactor and any further fixed polynomial factor are
absorbed by a strict exponential loss. This is sufficient for the original
fixed-base limit; no uniformity in the base order is asserted. -/
theorem tendsto_factorialPrefactor_mul_pow (d k : ℕ) (hd : 0 < d)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Filter.Tendsto (fun m : ℕ => (m : ℝ) ^ k * factorialPrefactor d m * r ^ m)
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ := factorialPrefactor_polynomial_bound d hd
  apply squeeze_zero'
  · apply Filter.Eventually.of_forall
    intro m
    unfold factorialPrefactor
    positivity
  · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    calc
      _ ≤ ((m : ℝ) ^ k * (C * (m : ℝ) ^ d)) * r ^ m :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hbound m hm) (by positivity)) (pow_nonneg hr m)
      _ = C * ((m : ℝ) ^ (k + d) * r ^ m) := by rw [pow_add]; ring
  · simpa using (tendsto_pow_const_mul_const_pow_of_lt_one (k + d) hr hr1).const_mul C

end
end Wormald
