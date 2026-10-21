import Wormald.ActualResidualDecay
import Wormald.ScaledSpectralLaplace

/-! The exact local Fourier integrand is the exponential of the actual
centered eigenvalue phase, plus the actual contracting spectral remainder. -/

namespace Wormald
noncomputable section
open Matrix Filter
open scoped BigOperators Topology

theorem scaledRealAngle_eq_complexify {n : ℕ} (t : Fin n → ℝ) :
    scaledRealAngle t = complexifyAngles n ((2 * Real.pi) • t) := by
  ext j
  rfl

theorem meanPhaseLinear_apply {n : ℕ} (t : Fin n → ℝ) :
    meanPhaseLinear n t = Complex.I * ∑ j, (t j : ℂ) := by
  simp [meanPhaseLinear]

theorem Tournament.centered_branch_power_eq_periodicPhase {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) (m : ℕ) (t : Fin n → ℝ) :
    Complex.exp (-(m : ℂ) * Complex.I * ∑ i, scaledRealAngle t i) *
      T.spectralBranch hT (scaledRealAngle t) ^ ((n + 1) * m) =
        Complex.exp ((m : ℂ) * T.periodicSpectralPhase hT t) := by
  rw [Tournament.spectralBranch, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  rw [Tournament.periodicSpectralPhase, Tournament.centeredSpectralPhase,
    Tournament.realLogSpectralBranch, ← scaledRealAngle_eq_complexify,
    meanPhaseLinear_apply]
  change -(m : ℂ) * Complex.I * ∑ i, scaledRealAngle t i +
    (((n + 1) * m : ℕ) : ℂ) * T.logSpectralBranch hT (scaledRealAngle t) =
    (m : ℂ) * (((n + 1 : ℕ) : ℂ) * T.logSpectralBranch hT (scaledRealAngle t) -
      Complex.I * ∑ i, scaledRealAngle t i)
  push_cast
  ring

/-- The same neighborhood works for every positive block size. Thus replacing
the Fourier integrand by the local exponential produces exactly the remainder
whose local integral has already been proved negligible. -/
theorem Tournament.eventually_anchored_integrand_eq_peak_add_residual {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    ∀ᶠ t : Fin n → ℝ in 𝓝 0, ∀ m : ℕ, 0 < m →
      anchoredRealCycleIntegrand T m t =
        Complex.exp ((m : ℂ) * T.periodicSpectralPhase hT t) +
          anchoredResidualCycleIntegrand T hT m t := by
  have ht : Tendsto (@scaledRealAngle n) (𝓝 0) (𝓝 0) := by
    simpa only [scaledRealAngle_zero] using
      (continuous_scaledRealAngle n).continuousAt.tendsto (x := (0 : Fin n → ℝ))
  filter_upwards [ht.eventually (T.trace_phase_pow_eq_branch_add_residual hT)] with t htrace
  intro m hm
  rw [anchoredRealCycleIntegrand_eq_scaled_phase]
  change Complex.exp _ * (T.complexPhaseTransition (scaledRealAngle t) ^ ((n + 1) * m)).trace = _
  rw [htrace _ (Nat.mul_pos (Nat.succ_pos n) hm), mul_add,
    T.centered_branch_power_eq_periodicPhase hT]
  rw [anchoredResidualCycleIntegrand, anchored_character_eq_exp]
  rfl

end
end Wormald
