import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NoncommRing

/-!
# The finite algebra in the Hessian calculation

These identities formalize Part I, Sections 5 and 7 of the manuscript.
Inverse matrices are supplied with their defining equations. No analytic
Hessian, implicit-function theorem, positivity, or counting asymptotic is
assumed to have been proved by this module.
-/

open Matrix

namespace Wormald

section Resolvent

variable {A : Type*} [Ring A]

/-- Polynomial factorization underlying the two resolvents. -/
theorem one_sub_square_factor (C : A) :
    1 - C * C = (1 - C) * (1 + C) := by
  noncomm_ring

/-- The finite rational identity used after differentiating the Schur complement.
`U`, `V`, and `W` are inverse witnesses for `1-C`, `1+C`, and `1-C²`.
Only the three displayed inverse equations are required. -/
theorem resolvent_identity (C U V W : A)
    (hU : U * (1 - C) = 1)
    (hV : V * (1 + C) = 1)
    (hW : (1 - C * C) * W = 1) :
    1 + C * U - C * V = (1 + C * C) * W := by
  have hUW : U = (1 + C) * W := by
    calc
      U = U * ((1 - C * C) * W) := by rw [hW, mul_one]
      _ = (U * (1 - C)) * ((1 + C) * W) := by
        rw [one_sub_square_factor]
        simp only [mul_assoc]
      _ = (1 + C) * W := by rw [hU, one_mul]
  have hVW : V = (1 - C) * W := by
    calc
      V = V * ((1 - C * C) * W) := by rw [hW, mul_one]
      _ = (V * (1 + C)) * ((1 - C) * W) := by noncomm_ring
      _ = (1 - C) * W := by rw [hV, one_mul]
  rw [hUW, hVW]
  calc
    1 + C * ((1 + C) * W) - C * ((1 - C) * W) =
        (1 - C * C) * W + C * ((1 + C) * W) - C * ((1 - C) * W) := by rw [hW]
    _ = (1 + C * C) * W := by noncomm_ring

end Resolvent

section Determinants

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Transposition makes the two real resolvent determinants equal. -/
theorem det_one_sub_eq_det_one_add (C : Matrix n n R) (hC : C.transpose = -C) :
    Matrix.det (1 - C) = Matrix.det (1 + C) := by
  calc
    Matrix.det (1 - C) = Matrix.det ((1 - C).transpose) :=
      (Matrix.det_transpose _).symm
    _ = Matrix.det (1 + C) := by simp [hC]

/-- The denominator determinant in Part I, Section 7 is a square. -/
theorem det_one_sub_square (C : Matrix n n R) (hC : C.transpose = -C) :
    Matrix.det (1 - C * C) = Matrix.det (1 + C) ^ 2 := by
  rw [one_sub_square_factor, Matrix.det_mul, det_one_sub_eq_det_one_add C hC,
    pow_two]

/-- The corresponding numerator identity, valid over any scalar ring containing
an element whose square is `-1`. In the paper that element is the complex `i`. -/
theorem det_one_add_square (C : Matrix n n R) (hC : C.transpose = -C)
    (a : R) (ha : a * a = -1) :
    Matrix.det (1 + C * C) = Matrix.det (1 + a • C) ^ 2 := by
  have hAC : (a • C).transpose = -(a • C) := by simp [hC]
  have hsq : (a • C) * (a • C) = -(C * C) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, ha]
    simp
  simpa [hsq] using det_one_sub_square (a • C) hAC

/-- The symmetric expression produced by Schur differentiation is exactly the
rational matrix in the manuscript. All inverse assumptions are explicit. -/
theorem hessian_core_identity (C U V W : Matrix n n R)
    (hC : C.transpose = -C)
    (hU : U * (1 - C) = 1) (hUr : (1 - C) * U = 1)
    (hV : V * (1 + C) = 1) (hW : (1 - C * C) * W = 1) :
    1 + U * C + (U * C).transpose = (1 + C * C) * W := by
  have hUT : U.transpose = V := by
    have ht : (1 + C) * U.transpose = 1 := by
      simpa [Matrix.transpose_mul, hC] using congrArg Matrix.transpose hU
    calc
      U.transpose = (V * (1 + C)) * U.transpose := by rw [hV, one_mul]
      _ = V := by rw [mul_assoc, ht, mul_one]
  have hcomm : U * C = C * U := by
    have hl : U - U * C = 1 := by simpa [mul_sub] using hU
    have hr : U - C * U = 1 := by simpa [sub_mul] using hUr
    exact sub_right_inj.mp (hl.trans hr.symm)
  rw [Matrix.transpose_mul, hC, hUT, neg_mul, hcomm, ← sub_eq_add_neg]
  exact resolvent_identity C U V W hU hV hW

end Determinants

end Wormald

