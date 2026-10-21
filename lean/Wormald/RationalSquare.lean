import Wormald.MatrixCore
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith

/-!
# The rational square in the determinant formula

For every rational skew-symmetric matrix C, det(1 + C*C) is a rational square.
This is the general algebraic rationality step of Conjecture 6; the analytic
identification with Wormald's Hessian and positivity are separate obligations.
The proof adjoins a formal square root of -1 and descends a conjugation-fixed
determinant back to the rational numbers.
-/

open Matrix
open scoped QuadraticAlgebra

namespace Wormald

abbrev GaussianRational := QuadraticAlgebra ℚ (-1) 0

private def rationalMatrix {n : Type*} [Fintype n] [DecidableEq n] (C : Matrix n n ℚ) :
    Matrix n n GaussianRational :=
  (algebraMap ℚ GaussianRational).mapMatrix C

private def gaussianMatrix {n : Type*} [Fintype n] [DecidableEq n] (C : Matrix n n ℚ) :
    Matrix n n GaussianRational :=
  1 + (QuadraticAlgebra.omega : GaussianRational) • rationalMatrix C

private theorem gaussianMatrix_hermitian {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℚ) (hC : C.transpose = -C) :
    (gaussianMatrix C).conjTranspose = gaussianMatrix C := by
  apply Matrix.ext
  intro i j
  have hji : C j i = -C i j := congrArg (fun M : Matrix n n ℚ => M i j) hC
  apply QuadraticAlgebra.ext <;>
    simp [gaussianMatrix, rationalMatrix, Matrix.conjTranspose_apply,
      Matrix.one_apply, QuadraticAlgebra.omega, hji, eq_comm]
  split_ifs <;> simp

/-- The numerator determinant of the Hessian determinant formula is a rational
square. No regularity, odd dimension, or analytic Hessian is assumed. -/
theorem det_one_add_square_rational {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℚ) (hC : C.transpose = -C) :
    ∃ q : ℚ, Matrix.det (1 + C * C) = q ^ 2 := by
  let z := Matrix.det (gaussianMatrix C)
  have hzstar : z = star z := by
    simpa [z, gaussianMatrix_hermitian C hC] using
      (Matrix.det_conjTranspose (gaussianMatrix C))
  have hzi : z.im = 0 := by
    have hi := congrArg QuadraticAlgebra.im hzstar
    simp only [QuadraticAlgebra.im_star] at hi
    linarith
  have hz : z = algebraMap ℚ GaussianRational z.re := by
    apply QuadraticAlgebra.ext <;> simp [hzi]
  have hCq : (rationalMatrix C).transpose = -(rationalMatrix C) := by
    change (C.map (algebraMap ℚ GaussianRational)).transpose =
      -(C.map (algebraMap ℚ GaussianRational))
    rw [← Matrix.transpose_map, hC]
    apply Matrix.ext
    intro i j
    change algebraMap ℚ GaussianRational (-C i j) =
      -algebraMap ℚ GaussianRational (C i j)
    exact map_neg _ _
  have homega : (QuadraticAlgebra.omega : GaussianRational) *
      QuadraticAlgebra.omega = -1 := by
    apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.omega]
  have hsq := det_one_add_square (rationalMatrix C) hCq
    (QuadraticAlgebra.omega : GaussianRational) homega
  have hmap : algebraMap ℚ GaussianRational (Matrix.det (1 + C * C)) = z ^ 2 := by
    rw [(algebraMap ℚ GaussianRational).map_det]
    change (((algebraMap ℚ GaussianRational).mapMatrix) (1 + C * C)).det = z ^ 2
    rw [map_add, map_one, map_mul]
    exact hsq
  refine ⟨z.re, ?_⟩
  apply QuadraticAlgebra.algebraMap_injective (a := (-1 : ℚ)) (b := 0)
  rw [map_pow, ← hz]
  exact hmap

/-- The precise determinant quotient occurring in `d / H` is a rational
square. Lean's total division also covers a zero denominator; applying this
to an actual Hessian additionally requires its determinant identity and
nonvanishing. -/
theorem det_quotient_rational_square {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n ℚ) (hC : C.transpose = -C) :
    ∃ q : ℚ, Matrix.det (1 - C * C) / Matrix.det (1 + C * C) = q ^ 2 := by
  obtain ⟨q, hq⟩ := det_one_add_square_rational C hC
  refine ⟨Matrix.det (1 + C) / q, ?_⟩
  rw [det_one_sub_square C hC, hq, div_pow]

#print axioms det_one_add_square_rational
#print axioms det_quotient_rational_square

end Wormald
