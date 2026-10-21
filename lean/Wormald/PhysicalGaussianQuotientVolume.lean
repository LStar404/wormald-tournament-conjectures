import Wormald.GaussianQuotientVolume

/-! The Gaussian quotient volume with the physical-angle Haar Jacobian.
Keeping the square-root 2π factor gives the exact fixed cost per removed
vertex used in the cluster decomposition. -/

namespace Wormald
noncomputable section

def physicalGaussianQuotientVolume (m : ℕ) : ℝ :=
  quotientGaussianVolume m / Real.pi ^ (m - 1)

theorem physicalGaussianQuotientVolume_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < physicalGaussianQuotientVolume m :=
  div_pos (quotientGaussianVolume_pos hm) (pow_pos Real.pi_pos _)

/-- The factor sqrt(2π) per removed coordinate is retained here. -/
theorem quotientGaussianVolume_ratio_le_exp_sharp {g m : ℕ} (hg : 2 ≤ g) (hgm : g ≤ m) :
    quotientGaussianVolume g / quotientGaussianVolume m ≤
      Real.exp (((m - g : ℕ) : ℝ) / 2 *
        (Real.log (m : ℝ) + 1 - Real.log (2 * Real.pi))) := by
  have hm : 2 ≤ m := hg.trans hgm
  have hgR : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hgmR : (g : ℝ) ≤ m := by exact_mod_cast hgm
  have hg2 : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hlog := Real.log_le_sub_one_of_pos (div_pos hmR hgR)
  rw [Real.log_div hmR.ne' hgR.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ ((g : ℝ) - 2) / 2 by linarith)
  have hfrac : (((g : ℝ) - 2) / 2) * ((m : ℝ) / g - 1) ≤ ((m : ℝ) - g) / 2 := by
    apply (mul_le_mul_iff_right₀ hgR).mp
    field_simp
    nlinarith
  rw [← Real.exp_log (div_pos (quotientGaussianVolume_pos hg) (quotientGaussianVolume_pos hm))]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div (quotientGaussianVolume_pos hg).ne' (quotientGaussianVolume_pos hm).ne',
    log_quotientGaussianVolume hg, log_quotientGaussianVolume hm, Nat.cast_sub hgm]
  nlinarith

theorem physicalGaussianQuotientVolume_ratio {g m : ℕ} (hg : 2 ≤ g) (hgm : g ≤ m) :
    physicalGaussianQuotientVolume g / physicalGaussianQuotientVolume m =
      (quotientGaussianVolume g / quotientGaussianVolume m) * Real.pi ^ (m - g) := by
  have hVm := (quotientGaussianVolume_pos (hg.trans hgm)).ne'
  have hpi := Real.pi_ne_zero
  have he : m - 1 = (g - 1) + (m - g) := by omega
  rw [physicalGaussianQuotientVolume, physicalGaussianQuotientVolume, he, pow_add]
  field_simp

theorem gaussianPhysicalRemovalConstant :
    Real.pi * Real.exp (1 / 2) / Real.sqrt (2 * Real.pi) =
      Real.sqrt (Real.pi * Real.exp 1 / 2) := by
  have he : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hs : (Real.pi * Real.exp (1 / 2) / Real.sqrt (2 * Real.pi)) ^ 2 =
      Real.pi * Real.exp 1 / 2 := by
    rw [div_pow, mul_pow, he, Real.sq_sqrt (by positivity)]
    field_simp
  rw [← hs, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

/-- Relative to the m-dimensional physical Gaussian normalization,
removing r vertices costs at most (sqrt(π e / 2) sqrt(m))^r. -/
theorem physicalGaussianQuotientVolume_ratio_le {g m : ℕ} (hg : 2 ≤ g) (hgm : g ≤ m) :
    physicalGaussianQuotientVolume g / physicalGaussianQuotientVolume m ≤
      (Real.sqrt (Real.pi * Real.exp 1 / 2) * Real.sqrt (m : ℝ)) ^ (m - g) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hroot : Real.exp (Real.log (m : ℝ) / 2) = Real.sqrt (m : ℝ) := by
    rw [← Real.log_sqrt hmR.le, Real.exp_log (Real.sqrt_pos.mpr hmR)]
  have hpRoot : Real.exp (Real.log (2 * Real.pi) / 2) = Real.sqrt (2 * Real.pi) := by
    rw [← Real.log_sqrt (by positivity), Real.exp_log (by positivity)]
  have hb : Real.exp ((Real.log (m : ℝ) + 1 - Real.log (2 * Real.pi)) / 2) =
      Real.sqrt (m : ℝ) * Real.exp (1 / 2) / Real.sqrt (2 * Real.pi) := by
    rw [show (Real.log (m : ℝ) + 1 - Real.log (2 * Real.pi)) / 2 =
      Real.log (m : ℝ) / 2 + 1 / 2 - Real.log (2 * Real.pi) / 2 by ring,
      Real.exp_sub, Real.exp_add, hroot, hpRoot]
  rw [physicalGaussianQuotientVolume_ratio hg hgm]
  apply (mul_le_mul_of_nonneg_right (quotientGaussianVolume_ratio_le_exp_sharp hg hgm)
    (pow_nonneg Real.pi_pos.le _)).trans_eq
  rw [show ((m - g : ℕ) : ℝ) / 2 *
      (Real.log (m : ℝ) + 1 - Real.log (2 * Real.pi)) =
      ((m - g : ℕ) : ℝ) * ((Real.log (m : ℝ) + 1 - Real.log (2 * Real.pi)) / 2) by ring,
    Real.exp_nat_mul, hb, ← mul_pow]
  congr 1
  rw [← gaussianPhysicalRemovalConstant]
  ring

end
end Wormald
