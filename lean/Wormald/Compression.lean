import Wormald.TournamentPositivity

open Matrix

namespace Wormald

/-- The columns `e_j-e_last` used to eliminate the final coordinate. -/
def coordinateEmbedding (n : ℕ) : Matrix (Fin (n + 1)) (Fin n) ℝ :=
  fun i j => if i = j.castSucc then 1 else if i = Fin.last n then -1 else 0

/-- The first coordinates of the embedded vector recover the original vector. -/
theorem coordinateEmbedding_mulVec_castSucc (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    (coordinateEmbedding n *ᵥ x) i.castSucc = x i := by
  simp [coordinateEmbedding, Matrix.mulVec, dotProduct]

/-- Thus the elimination coordinates are linearly independent. -/
theorem coordinateEmbedding_mulVec_injective (n : ℕ) :
    Function.Injective (coordinateEmbedding n).mulVec := by
  intro x y hxy
  funext i
  have hi := congrFun hxy i.castSucc
  simpa only [coordinateEmbedding_mulVec_castSucc] using hi

/-- Positive definiteness survives the exact coordinate compression in the paper. -/
theorem posDef_coordinateCompression {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hQ : Q.PosDef) :
    ((coordinateEmbedding n).transpose * Q * coordinateEmbedding n).PosDef := by
  simpa using hQ.conjTranspose_mul_mul_same (coordinateEmbedding_mulVec_injective n)

/-- The finite matrix candidate for the original angular Hessian.
No analytic identification is built into this definition. -/
noncomputable def Tournament.candidateHessian {n : ℕ} (T : Tournament (n + 1)) :
    Matrix (Fin n) (Fin n) ℝ :=
  (coordinateEmbedding n).transpose *
    ((1 + T.realNormalizedSign * T.realNormalizedSign) *
      (1 - T.realNormalizedSign * T.realNormalizedSign)⁻¹) * coordinateEmbedding n

/-- The candidate Hessian is positive definite for every tournament.
Regularity enters the remaining analytic identification, not this matrix estimate. -/
theorem Tournament.candidateHessian_posDef {n : ℕ} (T : Tournament (n + 1)) :
    T.candidateHessian.PosDef :=
  posDef_coordinateCompression _ (T.posDef_realNormalizedSign_core (Nat.succ_ne_zero n))

/-- In particular the finite candidate has strictly positive determinant. -/
theorem Tournament.candidateHessian_det_pos {n : ℕ} (T : Tournament (n + 1)) :
    0 < T.candidateHessian.det := T.candidateHessian_posDef.det_pos

end Wormald
