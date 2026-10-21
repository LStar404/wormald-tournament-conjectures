import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! The exact complete-graph Gaussian quotient volume and a bound uniform
when vertices are removed. This keeps the main Gaussian normalization in
the outlier decomposition of the regular-tournament Fourier integral. -/

namespace Wormald
noncomputable section

def quotientGaussianVolume (k : ℕ) : ℝ :=
  Real.sqrt (2 * Real.pi) ^ (k - 1) / Real.sqrt (k : ℝ) ^ (k - 2)

theorem quotientGaussianVolume_pos {k : ℕ} (hk : 2 ≤ k) :
    0 < quotientGaussianVolume k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  exact div_pos (pow_pos (Real.sqrt_pos.mpr (by positivity)) _)
    (pow_pos (Real.sqrt_pos.mpr hkR) _)

theorem log_quotientGaussianVolume {k : ℕ} (hk : 2 ≤ k) :
    Real.log (quotientGaussianVolume k) =
      ((k : ℝ) - 1) / 2 * Real.log (2 * Real.pi) -
        ((k : ℝ) - 2) / 2 * Real.log (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [quotientGaussianVolume, Real.log_div (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_sqrt (by positivity), Real.log_sqrt hkR.le,
    Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub hk]
  norm_num
  ring

/-- Removing r vertices costs at most m^(r/2) exp(r/2) in Gaussian volume;
there is no exponential loss in the number of vertices left in the core. -/
theorem quotientGaussianVolume_ratio_le_exp {g m : ℕ} (hg : 2 ≤ g) (hgm : g ≤ m) :
    quotientGaussianVolume g / quotientGaussianVolume m ≤
      Real.exp (((m - g : ℕ) : ℝ) / 2 * (Real.log (m : ℝ) + 1)) := by
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
  have hlogc : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.two_le_pi])
  have hcost : 0 ≤ ((m : ℝ) - g) / 2 * Real.log (2 * Real.pi) :=
    mul_nonneg (by linarith) hlogc
  rw [← Real.exp_log (div_pos (quotientGaussianVolume_pos hg) (quotientGaussianVolume_pos hm))]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div (quotientGaussianVolume_pos hg).ne' (quotientGaussianVolume_pos hm).ne',
    log_quotientGaussianVolume hg, log_quotientGaussianVolume hm,
    Nat.cast_sub hgm]
  nlinarith

theorem quotientGaussianVolume_ratio_le {g m : ℕ} (hg : 2 ≤ g) (hgm : g ≤ m) :
    quotientGaussianVolume g / quotientGaussianVolume m ≤
      (Real.sqrt (m : ℝ) * Real.exp (1 / 2)) ^ (m - g) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hroot : Real.exp (Real.log (m : ℝ) / 2) = Real.sqrt (m : ℝ) := by
    rw [← Real.log_sqrt hmR.le, Real.exp_log (Real.sqrt_pos.mpr hmR)]
  have heq : Real.exp (((m - g : ℕ) : ℝ) / 2 * (Real.log (m : ℝ) + 1)) =
      (Real.sqrt (m : ℝ) * Real.exp (1 / 2)) ^ (m - g) := by
    rw [← hroot, ← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [← heq]
  exact quotientGaussianVolume_ratio_le_exp hg hgm

end
end Wormald
