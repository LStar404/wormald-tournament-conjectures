import Wormald.MatrixLaplaceIntegral
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace Wormald

noncomputable section
open Matrix
open scoped BigOperators

def complexMatrixHalfQuadratic {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ)
    (x : Fin k → ℝ) : ℂ := (matrixHalfQuadratic S x : ℂ)

def complexCoordinate {k : ℕ} (i : Fin k) : (Fin k → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

@[simp] theorem complexCoordinate_apply {k : ℕ} (i : Fin k) (x : Fin k → ℝ) :
    complexCoordinate i x = (x i : ℂ) := rfl

def matrixHalfQuadraticDerivative {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ)
    (x : Fin k → ℝ) : (Fin k → ℝ) →L[ℝ] ℂ :=
  ∑ i, ∑ j, ((S i j / 2 : ℝ) : ℂ) •
    ((x i : ℂ) • complexCoordinate j + (x j : ℂ) • complexCoordinate i)

theorem complexMatrixHalfQuadratic_eq_sum {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (x : Fin k → ℝ) :
    complexMatrixHalfQuadratic S x =
      ∑ i, ∑ j, ((S i j / 2 : ℝ) : ℂ) * ((x i : ℂ) * (x j : ℂ)) := by
  simp only [complexMatrixHalfQuadratic, matrixHalfQuadratic, Matrix.mulVec, dotProduct,
    Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem hasFDerivAt_complexMatrixHalfQuadratic {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (x : Fin k → ℝ) :
    HasFDerivAt (complexMatrixHalfQuadratic S) (matrixHalfQuadraticDerivative S x) x := by
  have hterm (i j : Fin k) : HasFDerivAt
      (fun y : Fin k → ℝ => ((S i j / 2 : ℝ) : ℂ) * ((y i : ℂ) * (y j : ℂ)))
      (((S i j / 2 : ℝ) : ℂ) •
        ((x i : ℂ) • complexCoordinate j + (x j : ℂ) • complexCoordinate i)) x := by
    exact ((complexCoordinate i).hasFDerivAt.mul (complexCoordinate j).hasFDerivAt).const_mul _
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterm i j))
  simpa only [← complexMatrixHalfQuadratic_eq_sum, matrixHalfQuadraticDerivative] using hsum

theorem contDiff_complexMatrixHalfQuadratic {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ)
    (r : WithTop ℕ∞) : ContDiff ℝ r (complexMatrixHalfQuadratic S) := by
  have hreal : ContDiff ℝ r (matrixHalfQuadratic S) := by
    unfold matrixHalfQuadratic Matrix.mulVec dotProduct
    fun_prop
  exact Complex.ofRealCLM.contDiff.comp hreal

@[simp] theorem complexMatrixHalfQuadratic_zero {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) :
    complexMatrixHalfQuadratic S 0 = 0 := by simp [complexMatrixHalfQuadratic, matrixHalfQuadratic]

@[simp] theorem fderiv_complexMatrixHalfQuadratic {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (x : Fin k → ℝ) :
    fderiv ℝ (complexMatrixHalfQuadratic S) x = matrixHalfQuadraticDerivative S x :=
  (hasFDerivAt_complexMatrixHalfQuadratic S x).fderiv

@[simp] theorem fderiv_complexMatrixHalfQuadratic_zero {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) : fderiv ℝ (complexMatrixHalfQuadratic S) 0 = 0 := by
  rw [fderiv_complexMatrixHalfQuadratic]
  ext v
  simp only [matrixHalfQuadraticDerivative, _root_.sum_apply, _root_.smul_apply,
    _root_.add_apply, Pi.zero_apply, Complex.ofReal_zero, smul_eq_mul,
    zero_mul, add_zero, mul_zero, Finset.sum_const_zero, _root_.zero_apply]

private theorem complex_basis_apply {k : ℕ} (i j : Fin k) :
    (((Pi.single j (1 : ℝ) : Fin k → ℝ) i : ℝ) : ℂ) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst i
    simp
  · simp [h]

theorem fderiv_complexMatrixHalfQuadratic_basis {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (x : Fin k → ℝ) (j : Fin k) :
    fderiv ℝ (complexMatrixHalfQuadratic S) x (Pi.single j 1) =
      ∑ i, (((S i j + S j i) / 2 : ℝ) : ℂ) * (x i : ℂ) := by
  rw [fderiv_complexMatrixHalfQuadratic]
  simp only [matrixHalfQuadraticDerivative, _root_.sum_apply,
    _root_.smul_apply, _root_.add_apply,
    complexCoordinate_apply, smul_eq_mul, complex_basis_apply]
  simp only [mul_add, Finset.sum_add_distrib]
  have hfirst : (∑ i, ∑ l : Fin k, ((S i l / 2 : ℝ) : ℂ) *
      ((x i : ℂ) * (if l = j then 1 else 0))) =
      ∑ i, ((S i j / 2 : ℝ) : ℂ) * (x i : ℂ) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [mul_ite]
  have hsecond : (∑ i, ∑ l : Fin k, ((S i l / 2 : ℝ) : ℂ) *
      ((x l : ℂ) * (if i = j then 1 else 0))) =
      ∑ l, ((S j l / 2 : ℝ) : ℂ) * (x l : ℂ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    simp [mul_ite]
  rw [hfirst, hsecond, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  ring

def matrixHalfQuadraticFirstDirection {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ)
    (j : Fin k) : (Fin k → ℝ) →L[ℝ] ℂ :=
  ∑ i, (((S i j + S j i) / 2 : ℝ) : ℂ) • complexCoordinate i

/-- The genuine second derivative on two coordinate basis vectors. -/
theorem second_fderiv_complexMatrixHalfQuadratic_basis {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (j l : Fin k) :
    fderiv ℝ (fun x : Fin k → ℝ =>
      fderiv ℝ (complexMatrixHalfQuadratic S) x (Pi.single j 1)) 0 (Pi.single l 1) =
        (((S j l + S l j) / 2 : ℝ) : ℂ) := by
  have hfun : (fun x : Fin k → ℝ =>
      fderiv ℝ (complexMatrixHalfQuadratic S) x (Pi.single j 1)) =
        matrixHalfQuadraticFirstDirection S j := by
    funext x
    rw [fderiv_complexMatrixHalfQuadratic_basis]
    simp [matrixHalfQuadraticFirstDirection, smul_eq_mul]
  rw [hfun, (matrixHalfQuadraticFirstDirection S j).hasFDerivAt.fderiv]
  simp only [matrixHalfQuadraticFirstDirection, _root_.sum_apply,
    _root_.smul_apply, complexCoordinate_apply, smul_eq_mul, complex_basis_apply]
  simp [mul_ite, add_comm]

theorem second_fderiv_complexMatrixHalfQuadratic_basis_of_symmetric {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : S.transpose = S) (j l : Fin k) :
    fderiv ℝ (fun x : Fin k → ℝ =>
      fderiv ℝ (complexMatrixHalfQuadratic S) x (Pi.single j 1)) 0 (Pi.single l 1) = (S j l : ℂ) := by
  rw [second_fderiv_complexMatrixHalfQuadratic_basis]
  have hentry : S l j = S j l := congrFun (congrFun hS j) l
  rw [hentry]
  push_cast
  ring

end
end Wormald
