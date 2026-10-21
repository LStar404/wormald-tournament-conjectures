import Wormald.AnalyticImplicit
import Wormald.CriticalGradient
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The actual local logarithmic eigenvalue branch

Using the logarithm of the eigenvalue as the implicit variable avoids a reciprocal
singularity. The defining equation is Wormald's original determinant evaluated at
`zc * exp(i θ - s)`, and its derivative in `s` is the proved nonzero critical
determinant. Thus the branch is obtained from the genuine implicit function theorem.
-/

namespace Wormald
noncomputable section
open scoped BigOperators Topology
open Matrix MvPolynomial Filter

def radialAngleCoordinates {n : ℕ} (z : ℂ) (u : (Fin n → ℂ) × ℂ) :
    Fin (n + 1) → ℂ :=
  fun j => z * Complex.exp (Complex.I * appendLast u.1 0 j - u.2)

@[simp] theorem radialAngleCoordinates_zero {n : ℕ} (z : ℂ) :
    radialAngleCoordinates (n := n) z (0, 0) = fun _ => z := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [radialAngleCoordinates, appendLast]

theorem contDiff_radialAngleCoordinates {n : ℕ} (z : ℂ) (r : WithTop ℕ∞) :
    ContDiff ℂ r (radialAngleCoordinates (n := n) z) := by
  apply contDiff_pi.mpr
  intro j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [radialAngleCoordinates, appendLast, Fin.lastCases_last]
    fun_prop
  · simp only [radialAngleCoordinates, appendLast, Fin.lastCases_castSucc]
    fun_prop

def Tournament.radialCriticalEquation {n : ℕ} (T : Tournament (n + 1))
    (u : (Fin n → ℂ) × ℂ) : ℂ :=
  evalPolynomialComplex (definingPolynomial T.adjacency)
    (radialAngleCoordinates (2 / ((n + 1 : ℕ) : ℂ)) u)

theorem Tournament.contDiff_radialCriticalEquation {n : ℕ} (T : Tournament (n + 1))
    (r : WithTop ℕ∞) : ContDiff ℂ r T.radialCriticalEquation :=
  (contDiff_evalPolynomialComplex _ r).comp (contDiff_radialAngleCoordinates _ r)

theorem Tournament.radialCriticalEquation_zero {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : T.radialCriticalEquation (0, 0) = 0 := by
  simp only [Tournament.radialCriticalEquation, radialAngleCoordinates_zero,
    evalPolynomialComplex]
  rw [originalDeterminant_eq_polynomial_eval]
  exact originalDeterminant_critical T hT

theorem hasDerivAt_radialAngleCoordinates_scalar {n : ℕ} (z : ℂ) :
    HasDerivAt (fun s : ℂ => radialAngleCoordinates (n := n) z (0, s))
      (fun _ => -z) 0 := by
  apply hasDerivAt_pi.mpr
  intro j
  have heq : (fun s : ℂ => radialAngleCoordinates (n := n) z (0, s) j) =
      (fun s => z * Complex.exp (-s)) := by
    funext s
    refine Fin.lastCases ?_ (fun k => ?_) j <;>
      simp [radialAngleCoordinates, appendLast]
  rw [heq]
  simpa using (((hasDerivAt_id (0 : ℂ)).neg).cexp.const_mul z)

theorem Tournament.polynomialGradient_radial_zero {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    polynomialGradient (definingPolynomial T.adjacency)
      (fun _ => 2 / ((n + 1 : ℕ) : ℂ))
      (fun _ => -(2 / ((n + 1 : ℕ) : ℂ))) = T.criticalDet := by
  simp only [polynomialGradient, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, ContinuousLinearMap.proj_apply, evalPolynomialComplex]
  simp only [eval_first_pderiv_critical T hT (Nat.succ_ne_zero n),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

theorem Tournament.hasDerivAt_radialCriticalEquation_zero {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    HasDerivAt (fun s : ℂ => T.radialCriticalEquation (0, s)) T.criticalDet 0 := by
  let z : ℂ := 2 / ((n + 1 : ℕ) : ℂ)
  have hp : HasFDerivAt (evalPolynomialComplex (definingPolynomial T.adjacency))
      (polynomialGradient (definingPolynomial T.adjacency) (fun _ => z))
      (radialAngleCoordinates z ((0 : Fin n → ℂ), 0)) := by
    rw [radialAngleCoordinates_zero]
    exact hasFDerivAt_evalPolynomialComplex _ _
  have h := hp.comp_hasDerivAt 0 (hasDerivAt_radialAngleCoordinates_scalar (n := n) z)
  rw [T.polynomialGradient_radial_zero hT] at h
  exact h

theorem Tournament.radialCriticalEquation_partial_invertible {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    (fderiv ℂ T.radialCriticalEquation (0, 0) ∘L
      ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ).IsInvertible := by
  have hc := (T.contDiff_radialCriticalEquation 2).differentiable (by norm_num)
  have hcomp := hc.differentiableAt.hasFDerivAt.comp 0
    (ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ).hasFDerivAt
  have heq : fderiv ℂ T.radialCriticalEquation (0, 0) ∘L
      ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ =
      T.criticalDet • ContinuousLinearMap.id ℂ ℂ := by
    have h := hcomp.unique (T.hasDerivAt_radialCriticalEquation_zero hT).hasFDerivAt
    simp only [map_zero] at h
    change fderiv ℂ T.radialCriticalEquation (0, 0) ∘L
      ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ =
      ContinuousLinearMap.toSpanSingleton ℂ T.criticalDet at h
    rw [h]
    apply ContinuousLinearMap.ext
    intro v
    simp [mul_comm]
  rw [heq]
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := T.criticalDet⁻¹ • ContinuousLinearMap.id ℂ ℂ)
  · apply ContinuousLinearMap.ext
    intro v
    simp [T.criticalDet_ne_zero]
  · apply ContinuousLinearMap.ext
    intro v
    simp [T.criticalDet_ne_zero]

/-- A smooth local branch of the actual determinant equation, together with
its local uniqueness. No eigenvalue or Hessian formula is a premise. -/
theorem Tournament.exists_local_logSpectralBranch {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    ∃ s : (Fin n → ℂ) → ℂ,
      s 0 = 0 ∧ ContDiffAt ℂ 2 s 0 ∧
      (∀ᶠ θ in 𝓝 0, T.radialCriticalEquation (θ, s θ) = 0) ∧
      (∀ᶠ u in 𝓝 ((0 : Fin n → ℂ), (0 : ℂ)),
        T.radialCriticalEquation u = 0 ↔ s u.1 = u.2) := by
  have hc := (T.contDiff_radialCriticalEquation 2).contDiffAt (x := (0, 0))
  have hi := T.radialCriticalEquation_partial_invertible hT
  let s := hc.implicitFunction (by norm_num) hi
  refine ⟨s, hc.implicitFunction_apply_self (by norm_num) hi,
    hc.contDiffAt_implicitFunction (by norm_num) hi, ?_, ?_⟩
  · simpa only [T.radialCriticalEquation_zero hT] using
      hc.eventually_apply_implicitFunction (by norm_num) hi
  · simpa only [T.radialCriticalEquation_zero hT] using
      hc.eventually_apply_eq_iff_implicitFunction (by norm_num) hi

def Tournament.logSpectralBranch {n : ℕ} (T : Tournament (n + 1)) (hT : T.Regular) :
    (Fin n → ℂ) → ℂ := (T.exists_local_logSpectralBranch hT).choose

theorem Tournament.logSpectralBranch_zero {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : T.logSpectralBranch hT 0 = 0 :=
  (T.exists_local_logSpectralBranch hT).choose_spec.1

theorem Tournament.contDiffAt_logSpectralBranch {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : ContDiffAt ℂ 2 (T.logSpectralBranch hT) 0 :=
  (T.exists_local_logSpectralBranch hT).choose_spec.2.1

theorem Tournament.logSpectralBranch_solves {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) :
    ∀ᶠ θ in 𝓝 0, T.radialCriticalEquation (θ, T.logSpectralBranch hT θ) = 0 :=
  (T.exists_local_logSpectralBranch hT).choose_spec.2.2.1

theorem Tournament.logSpectralBranch_unique {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : ∀ᶠ u in 𝓝 ((0 : Fin n → ℂ), (0 : ℂ)),
      T.radialCriticalEquation u = 0 ↔ T.logSpectralBranch hT u.1 = u.2 :=
  (T.exists_local_logSpectralBranch hT).choose_spec.2.2.2

def Tournament.complexPhaseTransition {n : ℕ} (T : Tournament (n + 1))
    (θ : Fin n → ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  T.criticalTransition * Matrix.diagonal (fun j => Complex.exp (Complex.I * appendLast θ 0 j))

theorem Tournament.radialCriticalEquation_eq_det {n : ℕ} (T : Tournament (n + 1))
    (u : (Fin n → ℂ) × ℂ) :
    T.radialCriticalEquation u =
      (1 - Complex.exp (-u.2) • T.complexPhaseTransition u.1).det := by
  unfold Tournament.radialCriticalEquation evalPolynomialComplex
  rw [originalDeterminant_eq_polynomial_eval]
  unfold originalDeterminant
  congr 1
  ext i j
  simp only [originalMatrix, Tournament.complexPhaseTransition, Matrix.mul_diagonal,
    T.criticalTransition_entry (Nat.succ_ne_zero n), Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul, radialAngleCoordinates]
  simp only [sub_eq_add_neg, Complex.exp_add]
  ring

theorem Tournament.phaseCharacteristic_eq_radial {n : ℕ} (T : Tournament (n + 1))
    (θ : Fin n → ℂ) (s : ℂ) :
    (Complex.exp s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) -
      T.complexPhaseTransition θ).det =
      Complex.exp s ^ (n + 1) * T.radialCriticalEquation (θ, s) := by
  have hM : Complex.exp s • (1 - Complex.exp (-s) • T.complexPhaseTransition θ) =
      Complex.exp s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) -
        T.complexPhaseTransition θ := by
    simp [smul_sub, smul_smul, Complex.exp_neg, Complex.exp_ne_zero]
  rw [← hM, Matrix.det_smul, Fintype.card_fin, T.radialCriticalEquation_eq_det]

def Tournament.spectralBranch {n : ℕ} (T : Tournament (n + 1)) (hT : T.Regular)
    (θ : Fin n → ℂ) : ℂ := Complex.exp (T.logSpectralBranch hT θ)

@[simp] theorem Tournament.spectralBranch_zero {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : T.spectralBranch hT 0 = 1 := by
  simp [Tournament.spectralBranch, T.logSpectralBranch_zero hT]

theorem Tournament.spectralBranch_ne_zero {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) (θ : Fin n → ℂ) : T.spectralBranch hT θ ≠ 0 :=
  Complex.exp_ne_zero _

theorem Tournament.contDiffAt_spectralBranch {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : ContDiffAt ℂ 2 (T.spectralBranch hT) 0 :=
  Complex.contDiff_exp.contDiffAt.comp 0 (T.contDiffAt_logSpectralBranch hT)

/-- The constructed smooth branch is an eigenvalue of the actual phase matrix. -/
theorem Tournament.spectralBranch_characteristic_zero {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    ∀ᶠ θ in 𝓝 0,
      (T.spectralBranch hT θ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) -
        T.complexPhaseTransition θ).det = 0 := by
  filter_upwards [T.logSpectralBranch_solves hT] with θ hθ
  rw [Tournament.spectralBranch, T.phaseCharacteristic_eq_radial, hθ, mul_zero]

end
end Wormald
