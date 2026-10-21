import Wormald.FactorialPrefactor

/-! The exact Stirling scaling for the fixed-dimensional cycle asymptotic. -/

namespace Wormald
noncomputable section
open Filter Topology

theorem factorialPrefactor_div_sqrt_eq (k m : ℕ) (hm : 0 < m) :
    factorialPrefactor (k + 1) m / Real.sqrt (m : ℝ) ^ k =
      (Stirling.stirlingSeq m ^ (k + 1) / Stirling.stirlingSeq ((k + 1) * m)) *
        (Real.sqrt 2 ^ k / Real.sqrt ((k + 1 : ℕ) : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsM : Real.sqrt (m : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hmR)
  have hs2 : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hsD : Real.sqrt ((k + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hsN : Real.sqrt (2 * (((k + 1) * m : ℕ) : ℝ)) =
      Real.sqrt ((k + 1 : ℕ) : ℝ) * Real.sqrt 2 * Real.sqrt (m : ℝ) := by
    push_cast
    rw [show (2 : ℝ) * (((k : ℝ) + 1) * m) = ((k : ℝ) + 1) * (2 * m) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hpow : (Real.sqrt 2 * Real.sqrt (m : ℝ)) ^ (k + 1) =
      Real.sqrt 2 ^ k * Real.sqrt (m : ℝ) ^ k * Real.sqrt 2 * Real.sqrt (m : ℝ) := by
    rw [pow_succ, mul_pow]
    ring
  rw [factorialPrefactor_eq_stirling (k + 1) m (Nat.succ_pos _) hm, hsN,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ = (Stirling.stirlingSeq m ^ (k + 1) / Stirling.stirlingSeq ((k + 1) * m)) *
        (((Real.sqrt 2 * Real.sqrt (m : ℝ)) ^ (k + 1) /
          (Real.sqrt ((k + 1 : ℕ) : ℝ) * Real.sqrt 2 * Real.sqrt (m : ℝ))) /
          Real.sqrt (m : ℝ) ^ k) := by ring
    _ = _ := by
      congr 1
      rw [hpow]
      field_simp

/-- The factorial normalization supplies the Gaussian volume constant.
Writing the dimension as k avoids fractional real powers in the statement. -/
theorem tendsto_factorialPrefactor_div_sqrt (k : ℕ) :
    Tendsto (fun m : ℕ => factorialPrefactor (k + 1) m / Real.sqrt (m : ℝ) ^ k)
      atTop (𝓝 (Real.sqrt (2 * Real.pi) ^ k / Real.sqrt ((k + 1 : ℕ) : ℝ))) := by
  have hpi : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hmul : Tendsto (fun m : ℕ => (k + 1) * m) atTop atTop :=
    tendsto_id.const_mul_atTop' (Nat.succ_pos k)
  have hlim := ((Stirling.tendsto_stirlingSeq_sqrt_pi.pow (k + 1)).div
    (Stirling.tendsto_stirlingSeq_sqrt_pi.comp hmul) hpi).mul_const
      (Real.sqrt 2 ^ k / Real.sqrt ((k + 1 : ℕ) : ℝ))
  have hconstant : Real.sqrt Real.pi ^ (k + 1) / Real.sqrt Real.pi *
      (Real.sqrt 2 ^ k / Real.sqrt ((k + 1 : ℕ) : ℝ)) =
      Real.sqrt (2 * Real.pi) ^ k / Real.sqrt ((k + 1 : ℕ) : ℝ) := by
    rw [pow_succ, mul_div_cancel_right₀ _ hpi,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_pow]
    ring
  rw [hconstant] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact (factorialPrefactor_div_sqrt_eq k m (by omega)).symm

end
end Wormald
