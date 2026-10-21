import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Genuine real Fréchet derivatives of Wormald's complex angular coordinates.
No derivative formula is supplied as a premise. -/

namespace Wormald

noncomputable section

def angleCoordinates {n : ℕ} (z : ℂ) (θ : Fin n → ℝ) : Fin n → ℂ :=
  fun j => z * Complex.exp (Complex.I * (θ j : ℂ))

private def realCoordinateCLM {n : ℕ} (j : Fin n) : (Fin n → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)

private def angleCoordinateDerivative {n : ℕ} (z : ℂ) (θ : Fin n → ℝ) (j : Fin n) :
    (Fin n → ℝ) →L[ℝ] ℂ :=
  (angleCoordinates z θ j * Complex.I) • realCoordinateCLM j

def angleDerivative {n : ℕ} (z : ℂ) (θ : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi (angleCoordinateDerivative z θ)

@[simp] theorem angleCoordinates_zero {n : ℕ} (z : ℂ) :
    angleCoordinates (n := n) z 0 = (fun _ => z) := by
  funext j
  simp [angleCoordinates]

theorem contDiff_angleCoordinates {n : ℕ} (z : ℂ) (r : WithTop ℕ∞) :
    ContDiff ℝ r (angleCoordinates (n := n) z) := by
  apply contDiff_pi.mpr
  intro j
  have hreal : ContDiff ℝ r (fun θ : Fin n → ℝ => (θ j : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).contDiff
  have hI : ContDiff ℝ r (fun θ : Fin n → ℝ => Complex.I * (θ j : ℂ)) :=
    contDiff_const.mul hreal
  exact contDiff_const.mul hI.cexp

private theorem hasFDerivAt_angleCoordinate {n : ℕ} (z : ℂ) (θ : Fin n → ℝ) (j : Fin n) :
    HasFDerivAt (fun t : Fin n → ℝ => angleCoordinates z t j)
      (angleCoordinateDerivative z θ j) θ := by
  have hreal : HasFDerivAt (fun t : Fin n → ℝ => (t j : ℂ)) (realCoordinateCLM j) θ :=
    Complex.ofRealCLM.hasFDerivAt.comp θ
      (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt
  simpa only [angleCoordinates, angleCoordinateDerivative, smul_smul, mul_assoc] using
    (hreal.const_mul Complex.I).cexp.const_mul z

theorem hasFDerivAt_angleCoordinates {n : ℕ} (z : ℂ) (θ : Fin n → ℝ) :
    HasFDerivAt (angleCoordinates z) (angleDerivative z θ) θ :=
  hasFDerivAt_pi.mpr (hasFDerivAt_angleCoordinate z θ)

/-- First derivative in an arbitrary real direction, coordinate by coordinate. -/
theorem fderiv_angleCoordinates_apply {n : ℕ} (z : ℂ) (θ v : Fin n → ℝ) (j : Fin n) :
    (fderiv ℝ (angleCoordinates z) θ v) j =
      angleCoordinates z θ j * Complex.I * (v j : ℂ) := by
  rw [(hasFDerivAt_angleCoordinates z θ).fderiv]
  simp [angleDerivative, angleCoordinateDerivative, realCoordinateCLM]

/-- At the critical angle, the coordinate basis direction gains the factor `iz`. -/
theorem fderiv_angleCoordinates_zero_single {n : ℕ} (z : ℂ) (j : Fin n) :
    fderiv ℝ (angleCoordinates z) 0 (Pi.single j 1) = Pi.single j (Complex.I * z) := by
  funext a
  rw [fderiv_angleCoordinates_apply]
  by_cases ha : a = j
  · subst a
    simp [angleCoordinates, mul_comm]
  · simp [ha]

/-- The actual second real derivative of the angular map at zero. -/
theorem second_fderiv_angleCoordinates_zero {n : ℕ} (z : ℂ) (v w : Fin n → ℝ) :
    fderiv ℝ (fun θ => fderiv ℝ (angleCoordinates z) θ v) 0 w =
      (fun a => -z * (v a : ℂ) * (w a : ℂ)) := by
  let F : (Fin n → ℝ) → Fin n → ℂ := fun θ a =>
    angleCoordinates z θ a * (Complex.I * (v a : ℂ))
  have heq : (fun θ => fderiv ℝ (angleCoordinates z) θ v) = F := by
    funext θ a
    rw [fderiv_angleCoordinates_apply]
    exact mul_assoc _ _ _
  have hF : HasFDerivAt F
      (ContinuousLinearMap.pi fun a => (Complex.I * (v a : ℂ)) •
        angleCoordinateDerivative z 0 a) 0 := by
    apply hasFDerivAt_pi.mpr
    intro a
    exact (hasFDerivAt_angleCoordinate z 0 a).mul_const (Complex.I * (v a : ℂ))
  rw [heq, hF.fderiv]
  funext a
  simp only [ContinuousLinearMap.pi_apply, smul_apply,
    angleCoordinateDerivative, angleCoordinates_zero, smul_eq_mul,
    realCoordinateCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    Complex.ofRealCLM_apply]
  calc
    (Complex.I * (v a : ℂ)) * ((z * Complex.I) * (w a : ℂ)) =
        z * (Complex.I * Complex.I) * (v a : ℂ) * (w a : ℂ) := by ring
    _ = -z * (v a : ℂ) * (w a : ℂ) := by rw [Complex.I_mul_I]; ring

/-- Two basis directions meet only in their common coordinate. -/
theorem second_fderiv_angleCoordinates_zero_single {n : ℕ} (z : ℂ) (j k : Fin n) :
    fderiv ℝ (fun θ => fderiv ℝ (angleCoordinates z) θ (Pi.single j 1))
      0 (Pi.single k 1) =
      (fun a => if a = j ∧ a = k then -z else 0) := by
  rw [second_fderiv_angleCoordinates_zero]
  funext a
  by_cases haj : a = j
  · subst a
    by_cases hjk : j = k
    · subst k
      simp
    · simp [hjk]
  · simp [Pi.single_apply, haj]

end
end Wormald
