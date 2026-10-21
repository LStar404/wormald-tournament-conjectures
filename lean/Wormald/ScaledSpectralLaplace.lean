import Wormald.SpectralPhaseTaylor

/-! The local Gaussian integral for the actual spectral phase in unit-period
Fourier coordinates. The factor 2π is part of the proved quadratic matrix. -/

namespace Wormald
noncomputable section
open Matrix MeasureTheory Filter Topology

def Tournament.periodicSpectralPhase {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) (t : Fin n → ℝ) : ℂ :=
  T.centeredSpectralPhase hT ((2 * Real.pi) • t)

def Tournament.periodicCovariance {n : ℕ} (T : Tournament (n + 1)) :
    Matrix (Fin n) (Fin n) ℝ := (2 * Real.pi) ^ 2 • T.covarianceAnchor

theorem matrixHalfQuadratic_smul_matrix {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (a : ℝ) (x : Fin n → ℝ) :
    matrixHalfQuadratic (a • S) x = a * matrixHalfQuadratic S x := by
  simp only [matrixHalfQuadratic, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  ring

theorem Tournament.periodicCovariance_posDef {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : T.periodicCovariance.PosDef :=
  (T.covarianceAnchor_posDef hT).smul (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))

theorem Tournament.contDiffAt_periodicSpectralPhase {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    ContDiffAt ℝ 2 (T.periodicSpectralPhase hT) 0 := by
  have houter : ContDiffAt ℝ 2 (T.centeredSpectralPhase hT)
      ((2 * Real.pi) • (0 : Fin n → ℝ)) := by
    simpa only [smul_zero] using T.contDiffAt_centeredSpectralPhase hT
  exact houter.comp (0 : Fin n → ℝ)
    (show ContDiffAt ℝ 2 (fun t : Fin n → ℝ => (2 * Real.pi) • t) 0 from by fun_prop)

theorem Tournament.periodicSpectralPhase_quadratic_remainder {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    (fun t => T.periodicSpectralPhase hT t + (matrixHalfQuadratic T.periodicCovariance t : ℂ))
      =o[𝓝 0] (fun t => ((‖t‖ ^ 2 : ℝ) : ℂ)) := by
  let a : ℝ := 2 * Real.pi
  have ht : Tendsto (fun t : Fin n → ℝ => a • t) (𝓝 0) (𝓝 0) := by
    simpa only [smul_zero] using
      (show Continuous (fun t : Fin n → ℝ => a • t) from
        by fun_prop).continuousAt.tendsto (x := (0 : Fin n → ℝ))
  have hh := (T.centeredSpectralPhase_quadratic_remainder hT).comp_tendsto ht
  have hb : (fun t : Fin n → ℝ => ((‖a • t‖ ^ 2 : ℝ) : ℂ)) =O[𝓝 0]
      (fun t => ((‖t‖ ^ 2 : ℝ) : ℂ)) := by
    apply Asymptotics.IsBigO.of_bound (‖a‖ ^ 2)
    exact Eventually.of_forall fun t => by
      simp only [Complex.norm_real, norm_smul, mul_pow, Real.norm_eq_abs,
        abs_mul, abs_pow, sq_abs]
      exact le_rfl
  have h := hh.trans_isBigO hb
  apply h.congr_left
  intro t
  change T.centeredSpectralPhase hT (a • t) + (matrixHalfQuadratic T.covarianceAnchor (a • t) : ℂ) = _
  rw [matrixHalfQuadratic_smul]
  change _ = T.centeredSpectralPhase hT (a • t) +
    (matrixHalfQuadratic (a ^ 2 • T.covarianceAnchor) t : ℂ)
  rw [matrixHalfQuadratic_smul_matrix]

/-- A local Laplace limit for the genuine model phase and its genuine positive
covariance matrix. Only the base tournament's original regularity is assumed. -/
theorem Tournament.exists_periodicSpectralLaplace_radius {n : ℕ} (hn : 0 < n)
    (T : Tournament (n + 1)) (hT : T.Regular) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      Tendsto (fun m : ℕ => Real.sqrt (m : ℝ) ^ n •
        ∫ t : Fin n → ℝ, localComplexPeak (T.periodicSpectralPhase hT) δ m t) atTop
          (𝓝 ((Real.sqrt (2 * Real.pi) ^ n / Real.sqrt T.periodicCovariance.det : ℝ) : ℂ)) := by
  have hf := T.contDiffAt_periodicSpectralPhase hT
  have hc : ∀ᶠ t in 𝓝 (0 : Fin n → ℝ), ContinuousAt (T.periodicSpectralPhase hT) t :=
    (hf.eventually (by norm_num)).mono fun _ ht => ht.continuousAt
  obtain ⟨r, hr, hrc⟩ := Metric.mem_nhds_iff.mp hc
  exact exists_matrixLaplace_radius hn T.periodicCovariance (T.periodicCovariance_posDef hT)
    (T.periodicSpectralPhase hT) r hr
    (fun t ht => (hrc (by simpa [Metric.mem_ball, dist_zero_right] using ht)).continuousWithinAt)
    (T.periodicSpectralPhase_quadratic_remainder hT)

end
end Wormald
