import Wormald.Definitions

/-! An exact certificate tied to the original defining determinant for C₃.
This proves the polynomial and its implicit angular second jet. It does not
assert that a finite example settles any conjecture for arbitrary order.
-/

namespace Wormald

noncomputable section

open Matrix MvPolynomial

def cycleThree : Tournament 3 where
  adjacency := !![0, 1, 0; 0, 0, 1; 1, 0, 0]
  diagonal := by intro i; fin_cases i <;> norm_num
  zero_or_one := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  orientation := by intro i j h; fin_cases i <;> fin_cases j <;> norm_num at *

theorem cycleThree_regular : cycleThree.Regular := by
  intro i
  fin_cases i <;> norm_num [Tournament.Regular, cycleThree, Fin.sum_univ_succ]

def cycleThreePolynomial : MvPolynomial (Fin 3) ℚ :=
  (1 - C (1 / 2) * X 0) * (1 - C (1 / 2) * X 1) * (1 - C (1 / 2) * X 2) -
    X 0 * X 1 * X 2

theorem cycleThree_definingPolynomial :
    definingPolynomial cycleThree.adjacency = cycleThreePolynomial := by
  simp [definingPolynomial, definingMatrix, cycleThree, Matrix.det_fin_three,
    cycleThreePolynomial]
  ring

theorem cycleThree_critical_point :
    eval (fun _ => (2 / 3 : ℚ)) (definingPolynomial cycleThree.adjacency) = 0 := by
  rw [cycleThree_definingPolynomial]
  norm_num [cycleThreePolynomial]

theorem cycleThree_firstLogJet (j : Fin 3) :
    firstLogJet (definingPolynomial cycleThree.adjacency) (2 / 3) j = -4 / 9 := by
  rw [cycleThree_definingPolynomial]
  fin_cases j <;>
    norm_num [firstLogJet, cycleThreePolynomial, pderiv_mul]

theorem cycleThree_secondLogJet (j k : Fin 3) :
    secondLogJet (definingPolynomial cycleThree.adjacency) (2 / 3) j k =
      if j = k then -4 / 9 else -2 / 9 := by
  rw [cycleThree_definingPolynomial]
  fin_cases j <;> fin_cases k <;>
    norm_num [secondLogJet, firstLogJet, cycleThreePolynomial, pderiv_mul]

def cycleThreeHessianJet : Matrix (Fin 2) (Fin 2) ℚ :=
  fun j k => angularHessianJet (definingPolynomial cycleThree.adjacency)
    (2 / 3) 2 j.castSucc k.castSucc

theorem cycleThreeHessianJet_eq : cycleThreeHessianJet = !![1, 1 / 2; 1 / 2, 1] := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    norm_num [cycleThreeHessianJet, angularHessianJet,
      cycleThree_secondLogJet, cycleThree_firstLogJet]

theorem cycleThreeHessianJet_det : cycleThreeHessianJet.det = 3 / 4 := by
  rw [cycleThreeHessianJet_eq]
  norm_num [Matrix.det_fin_two]

theorem cycleThree_rational_square : (3 : ℚ) / cycleThreeHessianJet.det = 2 ^ 2 := by
  rw [cycleThreeHessianJet_det]
  norm_num

end
end Wormald
