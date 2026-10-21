import Wormald.ScaledSpectralLaplace
import Wormald.SkewMomentSeries
import Wormald.FactorialPrefactorLimit

/-! The Gaussian and Stirling constants multiply to the literal tournament
spectral ratio, including all dimension and unit-period scaling factors. -/

namespace Wormald
noncomputable section
open Matrix

theorem Tournament.spectralRatio_sq_mul_covarianceAnchor_det {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    T.spectralRatio.re ^ 2 * ((n : ℝ) + 1) * T.covarianceAnchor.det = 1 := by
  have ha := (T.posDef_one_add_realNormalizedSign_square (Nat.succ_ne_zero n)).det_pos
  have hb := (posDef_one_sub_square T.realNormalizedSign T.realNormalizedSign_skew).det_pos
  have hd : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [T.spectralRatio_re_sq (Nat.succ_ne_zero n), T.covarianceAnchor_det hT]
  simp only [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  field_simp

def Tournament.gaussianStirlingProduct {n : ℕ} (T : Tournament (n + 1)) : ℝ :=
  (Real.sqrt (2 * Real.pi) ^ n / Real.sqrt ((n : ℝ) + 1)) *
    (Real.sqrt (2 * Real.pi) ^ n / Real.sqrt T.periodicCovariance.det)

theorem Tournament.gaussianStirlingProduct_pos {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) : 0 < T.gaussianStirlingProduct := by
  unfold Tournament.gaussianStirlingProduct
  exact mul_pos (div_pos (pow_pos (Real.sqrt_pos.mpr (by positivity)) _) (by positivity))
    (div_pos (pow_pos (Real.sqrt_pos.mpr (by positivity)) _)
      (Real.sqrt_pos.mpr (T.periodicCovariance_posDef hT).det_pos))

theorem Tournament.gaussianStirlingProduct_sq_mul_covarianceAnchor_det {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    T.gaussianStirlingProduct ^ 2 * ((n : ℝ) + 1) * T.covarianceAnchor.det = 1 := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hr := (T.covarianceAnchor_posDef hT).det_pos
  have hd : (n : ℝ) + 1 ≠ 0 := by positivity
  have hdet : T.periodicCovariance.det = ((2 * Real.pi) ^ n) ^ 2 * T.covarianceAnchor.det := by
    simp only [Tournament.periodicCovariance, Matrix.det_smul, Fintype.card_fin,
      pow_right_comm (2 * Real.pi) 2 n]
  unfold Tournament.gaussianStirlingProduct
  rw [mul_pow, div_pow, div_pow, pow_right_comm (Real.sqrt (2 * Real.pi)) n 2,
    Real.sq_sqrt hp.le, Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity),
    Real.sq_sqrt (T.periodicCovariance_posDef hT).det_pos.le, hdet]
  field_simp

/-- The proposed limiting constant is exactly the original determinant ratio. -/
theorem Tournament.gaussianStirlingProduct_eq_spectralRatio {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    T.gaussianStirlingProduct = T.spectralRatio.re := by
  have hr := (T.covarianceAnchor_posDef hT).det_pos
  have hd : 0 < (n : ℝ) + 1 := by positivity
  have hs := T.spectralRatio_sq_mul_covarianceAnchor_det hT
  have hg := T.gaussianStirlingProduct_sq_mul_covarianceAnchor_det hT
  have heq : T.gaussianStirlingProduct ^ 2 = T.spectralRatio.re ^ 2 := by
    apply mul_right_cancel₀ (ne_of_gt hr)
    apply mul_right_cancel₀ (ne_of_gt hd)
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hg.trans hs.symm
  nlinarith [T.gaussianStirlingProduct_pos hT, T.spectralRatio_re_pos (Nat.succ_ne_zero n)]

end
end Wormald
