import Wormald.AnchoredRealFourier

namespace Wormald

noncomputable section
open Matrix
open scoped BigOperators

/-- Unit-period Fourier coordinates correspond to radian angles 2πt. -/
def scaledRealAngle {d : ℕ} (t : Fin d → ℝ) : Fin d → ℂ :=
  fun i => ((2 * Real.pi * t i : ℝ) : ℂ)

theorem anchoredRealPhase_eq_exp_scaledRealAngle {d : ℕ} (t : Fin d → ℝ) :
    anchoredRealPhase t = fun j => Complex.exp (Complex.I * appendLast (scaledRealAngle t) 0 j) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [anchoredRealPhase, appendLast]
  · simp only [anchoredRealPhase, anchoredFourierPhase_castSucc, fourier_coe_apply]
    congr 1
    simp [appendLast, scaledRealAngle]
    ring

theorem anchored_character_eq_exp {d : ℕ} (m : ℕ) (t : Fin d → ℝ) :
    UnitAddTorus.mFourier (fun _ => -(m : ℤ)) (fun i => (t i : UnitAddCircle)) =
      Complex.exp (-(m : ℂ) * Complex.I * ∑ i, scaledRealAngle t i) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [scaledRealAngle]
  ring

/-- The exact Fourier integrand has the same radian-scaled phase matrix as the
local analytic eigenvalue branch, including the occupation centering factor. -/
theorem anchoredRealCycleIntegrand_eq_scaled_phase {d : ℕ} (T : Tournament (d + 1))
    (m : ℕ) (t : Fin d → ℝ) :
    anchoredRealCycleIntegrand T m t =
      Complex.exp (-(m : ℂ) * Complex.I * ∑ i, scaledRealAngle t i) *
        ((T.criticalTransition * Matrix.diagonal
          (fun j => Complex.exp (Complex.I * appendLast (scaledRealAngle t) 0 j))) ^ ((d + 1) * m)).trace := by
  rw [anchoredRealCycleIntegrand, anchored_character_eq_exp,
    anchoredRealPhase_eq_exp_scaledRealAngle]

end
end Wormald
