import Wormald.ResidualPowerDecay
import Wormald.LocalSpectralProjector
import Wormald.AnchoredPhaseScaling

namespace Wormald

noncomputable section
open Matrix MeasureTheory Filter
open scoped Topology BigOperators

/-- The actual local spectral remainder in the unit-period real Fourier
coordinates of the exact Hamilton-cycle integral. -/
def Tournament.realSpectralResidual {d : ℕ} (T : Tournament (d + 1)) (hT : T.Regular)
    (t : Fin d → ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  T.spectralResidual hT (scaledRealAngle t)

theorem continuous_scaledRealAngle (d : ℕ) : Continuous (@scaledRealAngle d) := by
  unfold scaledRealAngle
  fun_prop

@[simp] theorem scaledRealAngle_zero (d : ℕ) : scaledRealAngle (0 : Fin d → ℝ) = 0 := by
  ext i
  simp [scaledRealAngle]

theorem Tournament.continuousAt_realSpectralResidual {d : ℕ}
    (T : Tournament (d + 1)) (hT : T.Regular) :
    ContinuousAt (T.realSpectralResidual hT) 0 := by
  exact (T.continuousAt_spectralResidual hT).comp_of_eq
    (continuous_scaledRealAngle d).continuousAt (scaledRealAngle_zero d)

@[simp] theorem Tournament.realSpectralResidual_zero {d : ℕ}
    (T : Tournament (d + 1)) (hT : T.Regular) :
    T.realSpectralResidual hT 0 = T.complexNormalizedSign := by
  simp [Tournament.realSpectralResidual, T.spectralResidual_zero hT]

def anchoredResidualCycleIntegrand {d : ℕ} (T : Tournament (d + 1)) (hT : T.Regular)
    (m : ℕ) (t : Fin d → ℝ) : ℂ :=
  UnitAddTorus.mFourier (fun _ => -(m : ℤ)) (fun i => (t i : UnitAddCircle)) *
    (T.realSpectralResidual hT t ^ ((d + 1) * m)).trace

/-- The actual rank-one spectral remainder is negligible on every sufficiently
small local ball, under every Gaussian polynomial normalization. -/
theorem Tournament.exists_anchoredResidual_local_integral_decay {d : ℕ}
    (T : Tournament (d + 1)) (hT : T.Regular) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, 0 < a → a ≤ δ → ∀ k : ℕ,
      Tendsto (fun m : ℕ => (Real.sqrt (m : ℝ) : ℂ) ^ k *
        ∫ t in Metric.ball 0 a, anchoredResidualCycleIntegrand T hT m t) atTop (𝓝 0) := by
  have hcenter : complexFrobeniusSq (T.realSpectralResidual hT 0) < 1 := by
    rw [T.realSpectralResidual_zero hT]
    exact T.complexNormalizedSign_frobenius_lt_one (by omega)
  obtain ⟨δ, hδ, hlocal⟩ := exists_local_residual_integral_decay
    (T.realSpectralResidual hT) (T.continuousAt_realSpectralResidual hT) hcenter
    (fun m t => UnitAddTorus.mFourier (fun _ => -(m : ℤ))
      (fun i => (t i : UnitAddCircle))) (fun m t => (norm_mFourier_apply _ _).le)
  exact ⟨δ, hδ, fun a ha haδ k => hlocal a ha haδ (d + 1) (by omega) k⟩

end
end Wormald
