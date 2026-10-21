import Wormald.GaussianMatrixIntegral

/-! Integrability of Gaussian domination in the actual finite coordinate
space, whose default norm is the supremum norm. -/

namespace Wormald
noncomputable section
open MeasureTheory
open scoped BigOperators

theorem sum_sq_le_card_mul_norm_sq {k : ℕ} (x : Fin k → ℝ) :
    (∑ i, x i ^ 2) ≤ (k : ℝ) * ‖x‖ ^ 2 := by
  calc
    _ ≤ ∑ _i : Fin k, ‖x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at hi
      nlinarith [abs_nonneg (x i), norm_nonneg x, sq_abs (x i)]
    _ = _ := by simp

theorem integrable_exp_neg_norm_sq_pi {k : ℕ} (hk : 0 < k)
    {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Fin k → ℝ => Real.exp (-c * ‖x‖ ^ 2)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let g : (Fin k → ℝ) → ℝ := fun x => ∏ i, Real.exp (-(c / k) * x i ^ 2)
  have hg : Integrable g := Integrable.fintype_prod
    (f := fun _ : Fin k => fun t : ℝ => Real.exp (-(c / k) * t ^ 2))
    (fun _ => integrable_exp_neg_mul_sq (div_pos hc hkR))
  apply hg.mono' (by fun_prop)
  apply ae_of_all
  intro x
  have hs := mul_le_mul_of_nonneg_left (sum_sq_le_card_mul_norm_sq x)
    (div_nonneg hc.le hkR.le)
  have he : (c / (k : ℝ)) * ((k : ℝ) * ‖x‖ ^ 2) = c * ‖x‖ ^ 2 := by
    field_simp
  rw [he] at hs
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  change Real.exp _ ≤ ∏ i, Real.exp (-(c / k) * x i ^ 2)
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  calc
    -c * ‖x‖ ^ 2 = -(c * ‖x‖ ^ 2) := by ring
    _ ≤ -(c / k * ∑ i, x i ^ 2) := neg_le_neg hs
    _ = ∑ i, -(c / k) * x i ^ 2 := by rw [← Finset.mul_sum]; ring

end
end Wormald
