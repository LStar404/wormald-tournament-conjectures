import Wormald.SpectralPhaseCovariance
import Wormald.MatrixQuadraticJets
import Wormald.FiniteJetRemainder

/-! The genuine centered spectral phase has the positive covariance quadratic
term and an actual little-o remainder. No Taylor equation is assumed. -/

namespace Wormald
noncomputable section
open Matrix Filter Topology

theorem Tournament.centeredSpectralPhase_quadratic_remainder {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    (fun θ => T.centeredSpectralPhase hT θ + (matrixHalfQuadratic T.covarianceAnchor θ : ℂ))
      =o[𝓝 0] (fun θ => ((‖θ‖ ^ 2 : ℝ) : ℂ)) := by
  let f := T.centeredSpectralPhase hT
  let q := complexMatrixHalfQuadratic T.covarianceAnchor
  have hf : ContDiffAt ℝ 2 f 0 := T.contDiffAt_centeredSpectralPhase hT
  have hq : ContDiffAt ℝ 2 q 0 :=
    (contDiff_complexMatrixHalfQuadratic T.covarianceAnchor 2).contDiffAt
  have hsum : ContDiffAt ℝ 2 (fun θ => f θ + q θ) 0 := hf.add hq
  have hzero : f 0 + q 0 = 0 := by simp [f, q]
  have hfirst : fderiv ℝ (fun θ => f θ + q θ) 0 = 0 := by
    rw [fderiv_fun_add (hf.differentiableAt (by norm_num)) (hq.differentiableAt (by norm_num))]
    simp only [f, q, T.fderiv_centeredSpectralPhase_zero hT,
      fderiv_complexMatrixHalfQuadratic_zero, add_zero]
  have hsecond : ∀ j k : Fin n,
      fderiv ℝ (fun θ => fderiv ℝ (fun y => f y + q y) θ (Pi.single j 1)) 0
        (Pi.single k 1) = 0 := by
    intro j k
    have heq : (fun θ => fderiv ℝ (fun y => f y + q y) θ (Pi.single j 1)) =ᶠ[𝓝 0]
        (fun θ => fderiv ℝ f θ (Pi.single j 1) + fderiv ℝ q θ (Pi.single j 1)) := by
      filter_upwards [hf.eventually (by norm_num), hq.eventually (by norm_num)] with θ hθf hθq
      rw [fderiv_fun_add (hθf.differentiableAt (by norm_num))
        (hθq.differentiableAt (by norm_num))]
      rfl
    have hdf : DifferentiableAt ℝ (fun θ => fderiv ℝ f θ (Pi.single j 1)) 0 :=
      ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
        (by norm_num)
    have hdq : DifferentiableAt ℝ (fun θ => fderiv ℝ q θ (Pi.single j 1)) 0 :=
      ((hq.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
        (by norm_num)
    rw [heq.fderiv_eq, fderiv_fun_add hdf hdq]
    simp only [_root_.add_apply]
    change fderiv ℝ (fun θ => fderiv ℝ (T.centeredSpectralPhase hT) θ (Pi.single j 1)) 0
      (Pi.single k 1) + fderiv ℝ (fun θ =>
        fderiv ℝ (complexMatrixHalfQuadratic T.covarianceAnchor) θ (Pi.single j 1)) 0
          (Pi.single k 1) = 0
    rw [T.second_fderiv_centeredSpectralPhase_eq_covarianceAnchor hT j k,
      second_fderiv_complexMatrixHalfQuadratic_basis_of_symmetric T.covarianceAnchor
        (Matrix.isHermitian_iff_isSymm.mp (T.covarianceAnchor_posDef hT).isHermitian) j k]
    simp
  have h := isLittleO_norm_sq_of_zero_coordinate_jets (fun θ => f θ + q θ)
    hsum hzero hfirst hsecond
  rw [← Asymptotics.isLittleO_norm_right] at h ⊢
  simpa only [f, q, complexMatrixHalfQuadratic, Complex.norm_real] using h

end
end Wormald
