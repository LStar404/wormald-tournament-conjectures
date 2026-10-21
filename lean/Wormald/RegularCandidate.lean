import Wormald.CompressionDeterminant
import Wormald.RationalSquare

/-! Exact finite determinant formula for the candidate Hessian of a regular
tournament. The analytic equality is not assumed by these declarations. -/

open Matrix
open scoped BigOperators

namespace Wormald

/-- The rational core fixes every vector in the kernel of the skew matrix. -/
theorem resolvent_mulVec_of_kernel {m : Type*} [Fintype m] [DecidableEq m]
    (C : Matrix m m ℝ) (hC : C.transpose = -C) (x : m → ℝ)
    (hx : C *ᵥ x = 0) :
    ((1 + C * C) * (1 - C * C)⁻¹) *ᵥ x = x := by
  have hA : (1 - C * C) *ᵥ x = x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hx,
      Matrix.mulVec_zero, sub_zero]
  have hunit : IsUnit (1 - C * C).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (posDef_one_sub_square C hC).isUnit
  have hinv : (1 - C * C)⁻¹ *ᵥ x = x := by
    calc
      (1 - C * C)⁻¹ *ᵥ x = (1 - C * C)⁻¹ *ᵥ ((1 - C * C) *ᵥ x) := by rw [hA]
      _ = x := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, hinv, Matrix.add_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, add_zero]

theorem Tournament.realNormalizedSign_mulVec_one {n : ℕ} (T : Tournament n)
    (hT : T.Regular) : T.realNormalizedSign *ᵥ (fun _ => 1) = 0 := by
  have hrat (i : Fin n) : ∑ j, T.normalizedSign i j = 0 := by
    simp only [Tournament.normalizedSign, ← Finset.sum_div, T.sign_row_sum hT,
      zero_div]
  funext i
  change (∑ j, (T.normalizedSign i j : ℝ) * 1) = 0
  simp only [mul_one]
  exact_mod_cast hrat i

/-- The complete determinant ratio for the candidate finite Hessian. -/
theorem Tournament.candidateHessian_det_formula {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    T.candidateHessian.det = ((n : ℝ) + 1) *
      (1 + T.realNormalizedSign * T.realNormalizedSign).det /
      (1 - T.realNormalizedSign * T.realNormalizedSign).det := by
  let C := T.realNormalizedSign
  let Q := (1 + C * C) * (1 - C * C)⁻¹
  have hsym : Q.transpose = Q := by
    exact Matrix.isHermitian_iff_isSymm.mp
      (T.posDef_realNormalizedSign_core (Nat.succ_ne_zero n)).isHermitian
  have hfix : Q *ᵥ (fun _ => 1) = (fun _ => 1) :=
    resolvent_mulVec_of_kernel C T.realNormalizedSign_skew _
      (T.realNormalizedSign_mulVec_one hT)
  change ((coordinateEmbedding n).transpose * Q * coordinateEmbedding n).det = _
  rw [det_coordinateCompression Q hsym hfix]
  dsimp [Q, C]
  simp [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', div_eq_mul_inv,
    mul_assoc]

end Wormald
