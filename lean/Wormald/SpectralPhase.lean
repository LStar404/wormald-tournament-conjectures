import Wormald.SpectralBranchJets

/-! The centered phase used by the coefficient integral, with exponent `m`.
Its first derivative vanishes and its negative Hessian is the anchored
resolvent covariance before conversion from radians to unit-period angles. -/

namespace Wormald
noncomputable section
open scoped BigOperators Topology
open Matrix Filter

theorem clm_apply_eq_sum_single {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : (Fin n → ℝ) →L[ℝ] F) (v : Fin n → ℝ) :
    L v = ∑ j, v j • L (Pi.single j 1) := by
  have hv : v = ∑ j, v j • Pi.single j 1 := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul]

def meanPhaseLinear (n : ℕ) : (Fin n → ℝ) →L[ℝ] ℂ :=
  Complex.I • ∑ j : Fin n, Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)

@[simp] theorem meanPhaseLinear_single {n : ℕ} (j : Fin n) :
    meanPhaseLinear n (Pi.single j 1) = Complex.I := by
  simp [meanPhaseLinear, Pi.single_apply, apply_ite]

def Tournament.centeredSpectralPhase {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) (θ : Fin n → ℝ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) * T.realLogSpectralBranch hT θ - meanPhaseLinear n θ

@[simp] theorem Tournament.centeredSpectralPhase_zero {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) : T.centeredSpectralPhase hT 0 = 0 := by
  simp [Tournament.centeredSpectralPhase]

theorem Tournament.contDiffAt_centeredSpectralPhase {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    ContDiffAt ℝ 2 (T.centeredSpectralPhase hT) 0 :=
  (contDiffAt_const.mul (T.contDiffAt_realLogSpectralBranch hT)).sub
    (meanPhaseLinear n).contDiff.contDiffAt

theorem Tournament.fderiv_centeredSpectralPhase_apply {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) (θ v : Fin n → ℝ)
    (hs : DifferentiableAt ℝ (T.realLogSpectralBranch hT) θ) :
    fderiv ℝ (T.centeredSpectralPhase hT) θ v =
      ((n + 1 : ℕ) : ℂ) * fderiv ℝ (T.realLogSpectralBranch hT) θ v - meanPhaseLinear n v := by
  have h := (hs.hasFDerivAt.const_mul ((n + 1 : ℕ) : ℂ)).sub
    (meanPhaseLinear n).hasFDerivAt
  rw [show fderiv ℝ (T.centeredSpectralPhase hT) θ = _ from h.fderiv]
  simp

theorem Tournament.fderiv_centeredSpectralPhase_zero {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    fderiv ℝ (T.centeredSpectralPhase hT) 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [clm_apply_eq_sum_single]
  have heq : ∀ j : Fin n, fderiv ℝ (T.centeredSpectralPhase hT) 0 (Pi.single j 1) = 0 := by
    intro j
    rw [T.fderiv_centeredSpectralPhase_apply hT 0 (Pi.single j 1)
      ((T.contDiffAt_realLogSpectralBranch hT).differentiableAt (by norm_num)),
      T.fderiv_realLogSpectralBranch_zero_single hT j, meanPhaseLinear_single]
    have hd : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp
    ring
  simp only [heq, smul_zero, Finset.sum_const_zero, _root_.zero_apply]

theorem Tournament.second_fderiv_centeredSpectralPhase_zero_single {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) (j k : Fin n) :
    fderiv ℝ (fun θ => fderiv ℝ (T.centeredSpectralPhase hT) θ (Pi.single j 1)) 0
      (Pi.single k 1) =
      -(T.complexResolventCore j.castSucc k.castSucc - 1 / ((n + 1 : ℕ) : ℂ)) := by
  have hs := T.contDiffAt_realLogSpectralBranch hT
  have heq : (fun θ => fderiv ℝ (T.centeredSpectralPhase hT) θ (Pi.single j 1)) =ᶠ[𝓝 0]
      (fun θ => ((n + 1 : ℕ) : ℂ) * fderiv ℝ (T.realLogSpectralBranch hT) θ
        (Pi.single j 1) - meanPhaseLinear n (Pi.single j 1)) := by
    filter_upwards [hs.eventually (by norm_num)] with θ hθ
    exact T.fderiv_centeredSpectralPhase_apply hT θ _ (hθ.differentiableAt (by norm_num))
  have hds : DifferentiableAt ℝ
      (fun θ => fderiv ℝ (T.realLogSpectralBranch hT) θ (Pi.single j 1)) 0 :=
    ((hs.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  rw [heq.fderiv_eq, ((hds.hasFDerivAt.const_mul ((n + 1 : ℕ) : ℂ)).sub_const _).fderiv]
  simp only [_root_.smul_apply, smul_eq_mul]
  rw [T.second_fderiv_realLogSpectralBranch_zero_single hT j k]
  have hd : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

end
end Wormald
