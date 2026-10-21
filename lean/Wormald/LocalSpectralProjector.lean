import Wormald.LocalSpectralBranch
import Wormald.ResolventEigenvectors
import Mathlib.Topology.Instances.Matrix

/-! The actual phase matrix is a rank-one perturbation of `C diag(u)`.
Its resolvent constructs left and right eigenvectors and hence an exact
rank-one spectral decomposition, without continuity of unordered spectra. -/

namespace Wormald
noncomputable section
open scoped BigOperators Topology
open Matrix Filter

def Tournament.spectralPhaseVector {n : ℕ} (_T : Tournament (n + 1))
    (θ : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  fun j => Complex.exp (Complex.I * appendLast θ 0 j)

def Tournament.spectralBasePart {n : ℕ} (T : Tournament (n + 1))
    (θ : Fin n → ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  T.complexNormalizedSign * Matrix.diagonal (T.spectralPhaseVector θ)

def Tournament.spectralRankRow {n : ℕ} (T : Tournament (n + 1))
    (θ : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  fun j => T.spectralPhaseVector θ j / ((n + 1 : ℕ) : ℂ)

def Tournament.spectralResolventMatrix {n : ℕ} (T : Tournament (n + 1)) (hT : T.Regular)
    (θ : Fin n → ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  T.spectralBranch hT θ • 1 - T.spectralBasePart θ

def Tournament.spectralRightVector {n : ℕ} (T : Tournament (n + 1)) (hT : T.Regular)
    (θ : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  (T.spectralResolventMatrix hT θ)⁻¹ *ᵥ (fun _ => 1)

def Tournament.spectralLeftVector {n : ℕ} (T : Tournament (n + 1)) (hT : T.Regular)
    (θ : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  T.spectralRankRow θ ᵥ* (T.spectralResolventMatrix hT θ)⁻¹

def Tournament.spectralProjector {n : ℕ} (T : Tournament (n + 1)) (hT : T.Regular)
    (θ : Fin n → ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  rankOneProjection (T.spectralRightVector hT θ) (T.spectralLeftVector hT θ)

def Tournament.spectralResidual {n : ℕ} (T : Tournament (n + 1)) (hT : T.Regular)
    (θ : Fin n → ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  T.complexPhaseTransition θ - T.spectralBranch hT θ • T.spectralProjector hT θ

theorem Tournament.complexPhaseTransition_eq_rankOne {n : ℕ} (T : Tournament (n + 1))
    (θ : Fin n → ℂ) :
    T.complexPhaseTransition θ = T.spectralBasePart θ +
      Matrix.vecMulVec (fun _ => 1) (T.spectralRankRow θ) := by
  ext i j
  simp only [Tournament.complexPhaseTransition, Tournament.spectralBasePart,
    Tournament.spectralRankRow, Tournament.spectralPhaseVector, Tournament.criticalTransition,
    Tournament.constantProjection, Matrix.mul_diagonal, Matrix.of_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply]
  ring

@[simp] theorem Tournament.spectralPhaseVector_zero {n : ℕ} (T : Tournament (n + 1)) :
    T.spectralPhaseVector 0 = (fun _ => 1) := by
  ext j
  refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [Tournament.spectralPhaseVector, appendLast]

@[simp] theorem Tournament.spectralBasePart_zero {n : ℕ} (T : Tournament (n + 1)) :
    T.spectralBasePart 0 = T.complexNormalizedSign := by
  simp [Tournament.spectralBasePart]

@[simp] theorem Tournament.spectralResolventMatrix_zero {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : T.spectralResolventMatrix hT 0 = 1 - T.complexNormalizedSign := by
  simp [Tournament.spectralResolventMatrix]

@[simp] theorem Tournament.spectralRightVector_zero {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : T.spectralRightVector hT 0 = (fun _ => 1) := by
  simp only [Tournament.spectralRightVector, T.spectralResolventMatrix_zero hT]
  exact T.criticalResolvent_mulVec_one hT

@[simp] theorem Tournament.spectralLeftVector_zero {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : T.spectralLeftVector hT 0 = (fun _ => 1 / ((n + 1 : ℕ) : ℂ)) := by
  have hc : ∀ j, ∑ i, T.criticalResolvent i j = 1 := by
    intro j
    simpa [Matrix.vecMul, dotProduct] using congrFun (T.one_vecMul_criticalResolvent hT) j
  ext j
  simp only [Tournament.spectralLeftVector, Tournament.spectralRankRow,
    T.spectralPhaseVector_zero, T.spectralResolventMatrix_zero hT,
    Matrix.vecMul, dotProduct]
  change (∑ i, (1 / ((n + 1 : ℕ) : ℂ)) * T.criticalResolvent i j) = _
  rw [← Finset.mul_sum, hc, mul_one]

theorem Tournament.spectralPairing_zero {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : T.spectralLeftVector hT 0 ⬝ᵥ T.spectralRightVector hT 0 = 1 := by
  simp only [T.spectralLeftVector_zero hT, T.spectralRightVector_zero hT, dotProduct,
    mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

@[simp] theorem Tournament.spectralProjector_zero {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : T.spectralProjector hT 0 = T.constantProjection := by
  unfold Tournament.spectralProjector rankOneProjection
  rw [T.spectralPairing_zero hT]
  ext i j
  simp [Tournament.constantProjection, Matrix.vecMulVec_apply]

@[simp] theorem Tournament.spectralResidual_zero {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : T.spectralResidual hT 0 = T.complexNormalizedSign := by
  have hphase : T.complexPhaseTransition 0 = T.criticalTransition := by
    change T.criticalTransition * Matrix.diagonal (T.spectralPhaseVector 0) = _
    rw [T.spectralPhaseVector_zero]
    simp
  simp [Tournament.spectralResidual, hphase, Tournament.criticalTransition]

theorem Tournament.continuous_spectralPhaseVector {n : ℕ} (T : Tournament (n + 1)) :
    Continuous T.spectralPhaseVector := by
  apply continuous_pi
  intro j
  refine Fin.lastCases ?_ (fun k => ?_) j <;> simp only [Tournament.spectralPhaseVector,
    appendLast, Fin.lastCases_last, Fin.lastCases_castSucc] <;> fun_prop

theorem Tournament.continuousAt_spectralResolventMatrix {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : ContinuousAt (T.spectralResolventMatrix hT) 0 := by
  have hb : Continuous T.spectralBasePart :=
    continuous_const.matrix_mul (T.continuous_spectralPhaseVector.matrix_diagonal)
  exact ((T.contDiffAt_spectralBranch hT).continuousAt.smul continuousAt_const).sub hb.continuousAt

theorem Tournament.continuousAt_spectralResolventInverse {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : ContinuousAt (fun θ => (T.spectralResolventMatrix hT θ)⁻¹) 0 := by
  have hdet : (T.spectralResolventMatrix hT 0).det ≠ 0 := by
    rw [T.spectralResolventMatrix_zero hT]
    exact T.criticalDet_ne_zero
  have hi := continuousAt_matrix_inv (T.spectralResolventMatrix hT 0)
    (by simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet)
  exact hi.comp (T.continuousAt_spectralResolventMatrix hT)

theorem Tournament.continuousAt_spectralRightVector {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : ContinuousAt (T.spectralRightVector hT) 0 := by
  apply continuousAt_pi.mpr
  intro i
  change ContinuousAt (fun θ => ∑ j, (T.spectralResolventMatrix hT θ)⁻¹ i j * 1) 0
  apply tendsto_finsetSum
  intro j _
  exact (continuousAt_pi.mp (continuousAt_pi.mp
    (T.continuousAt_spectralResolventInverse hT) i) j).mul continuousAt_const

theorem Tournament.continuous_spectralRankRow {n : ℕ} (T : Tournament (n + 1)) :
    Continuous T.spectralRankRow := by
  apply continuous_pi
  intro j
  exact ((continuous_apply j).comp T.continuous_spectralPhaseVector).div_const _

theorem Tournament.continuousAt_spectralLeftVector {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : ContinuousAt (T.spectralLeftVector hT) 0 := by
  apply continuousAt_pi.mpr
  intro j
  change ContinuousAt (fun θ => ∑ i, T.spectralRankRow θ i *
    (T.spectralResolventMatrix hT θ)⁻¹ i j) 0
  apply tendsto_finsetSum
  intro i _
  exact (continuousAt_pi.mp T.continuous_spectralRankRow.continuousAt i).mul
    (continuousAt_pi.mp (continuousAt_pi.mp
      (T.continuousAt_spectralResolventInverse hT) i) j)

theorem Tournament.continuousAt_spectralPairing {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : ContinuousAt
      (fun θ => T.spectralLeftVector hT θ ⬝ᵥ T.spectralRightVector hT θ) 0 := by
  unfold dotProduct
  apply tendsto_finsetSum
  intro i _
  exact (continuousAt_pi.mp (T.continuousAt_spectralLeftVector hT) i).mul
    (continuousAt_pi.mp (T.continuousAt_spectralRightVector hT) i)

theorem Tournament.continuousAt_spectralProjector {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : ContinuousAt (T.spectralProjector hT) 0 := by
  have hne : T.spectralLeftVector hT 0 ⬝ᵥ T.spectralRightVector hT 0 ≠ 0 := by
    rw [T.spectralPairing_zero hT]
    exact one_ne_zero
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  exact ((T.continuousAt_spectralPairing hT).inv₀ hne).mul
    ((continuousAt_pi.mp (T.continuousAt_spectralRightVector hT) i).mul
      (continuousAt_pi.mp (T.continuousAt_spectralLeftVector hT) j))

theorem Tournament.continuousAt_spectralResidual {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : ContinuousAt (T.spectralResidual hT) 0 := by
  have hA : Continuous T.complexPhaseTransition :=
    continuous_const.matrix_mul (T.continuous_spectralPhaseVector.matrix_diagonal)
  exact hA.continuousAt.sub ((T.contDiffAt_spectralBranch hT).continuousAt.smul
    (T.continuousAt_spectralProjector hT))

/-- The local trace is the single smooth eigenvalue contribution plus powers
of a continuous residual matrix whose central value is the strict contraction C. -/
theorem Tournament.trace_phase_pow_eq_branch_add_residual {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    ∀ᶠ θ in 𝓝 0, ∀ N : ℕ, 0 < N →
      (T.complexPhaseTransition θ ^ N).trace = T.spectralBranch hT θ ^ N +
        (T.spectralResidual hT θ ^ N).trace := by
  have hdet : (T.spectralResolventMatrix hT 0).det ≠ 0 := by
    rw [T.spectralResolventMatrix_zero hT]
    exact T.criticalDet_ne_zero
  have hcDet : ContinuousAt (fun θ => (T.spectralResolventMatrix hT θ).det) 0 :=
    (continuous_id.matrix_det : Continuous
      (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => M.det)).continuousAt.comp
        (T.continuousAt_spectralResolventMatrix hT)
  have hpair : T.spectralLeftVector hT 0 ⬝ᵥ T.spectralRightVector hT 0 ≠ 0 := by
    rw [T.spectralPairing_zero hT]
    exact one_ne_zero
  filter_upwards [hcDet.eventually_ne hdet,
    (T.continuousAt_spectralPairing hT).eventually_ne hpair,
    T.spectralBranch_characteristic_zero hT] with θ hG hp hchar
  have hchar' : (T.spectralBranch hT θ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) -
      (T.spectralBasePart θ + Matrix.vecMulVec (fun _ => 1) (T.spectralRankRow θ))).det = 0 := by
    rw [← T.complexPhaseTransition_eq_rankOne]
    exact hchar
  obtain ⟨_, hr, hl⟩ := resolvent_rankOne_eigenvectors (T.spectralBasePart θ)
    (fun _ => 1) (T.spectralRankRow θ) (T.spectralBranch hT θ)
    (isUnit_iff_ne_zero.mpr hG) hchar'
  have hr' : T.complexPhaseTransition θ *ᵥ T.spectralRightVector hT θ =
      T.spectralBranch hT θ • T.spectralRightVector hT θ := by
    rw [T.complexPhaseTransition_eq_rankOne]
    exact hr
  have hl' : T.spectralLeftVector hT θ ᵥ* T.complexPhaseTransition θ =
      T.spectralBranch hT θ • T.spectralLeftVector hT θ := by
    rw [T.complexPhaseTransition_eq_rankOne]
    exact hl
  intro N hN
  exact trace_pow_eq_rankOne_add_residual (T.complexPhaseTransition θ)
    (T.spectralRightVector hT θ) (T.spectralLeftVector hT θ) (T.spectralBranch hT θ)
      hp hr' hl' N hN

end
end Wormald
