import Wormald.SpectralPhase
import Wormald.CovarianceAnchor

/-! Identification of the actual logarithmic spectral-phase Hessian with
the real positive covariance matrix used in the Gaussian integral. -/

namespace Wormald
noncomputable section
open Matrix

theorem Tournament.complexResolventCore_sub_eq_covarianceAnchor {n : ℕ}
    (T : Tournament (n + 1)) (j k : Fin n) :
    T.complexResolventCore j.castSucc k.castSucc - 1 / ((n + 1 : ℕ) : ℂ) =
      (T.covarianceAnchor j k : ℂ) := by
  have he := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ =>
    M j.castSucc k.castSucc) T.criticalResolvent_sum_eq_realCore
  change T.complexResolventCore j.castSucc k.castSucc = _ at he
  rw [he]
  change _ = ((anchoredCovariance ((1 + T.realNormalizedSign * T.realNormalizedSign) *
    (1 - T.realNormalizedSign * T.realNormalizedSign)⁻¹)) j k : ℂ)
  simp only [anchoredCovariance, Complex.ofReal_sub, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_add, Complex.ofReal_natCast, Nat.cast_add, Nat.cast_one]
  rfl

theorem Tournament.second_fderiv_centeredSpectralPhase_eq_covarianceAnchor {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) (j k : Fin n) :
    fderiv ℝ (fun θ => fderiv ℝ (T.centeredSpectralPhase hT) θ (Pi.single j 1)) 0
      (Pi.single k 1) = -(T.covarianceAnchor j k : ℂ) := by
  rw [T.second_fderiv_centeredSpectralPhase_zero_single hT j k,
    T.complexResolventCore_sub_eq_covarianceAnchor]

end
end Wormald
