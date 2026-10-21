import Wormald.GaussianQuotientVolume
import Wormald.GaussianMatrixIntegral
import Wormald.ResolventEigenvectors
import Mathlib.Algebra.Order.Chebyshev

/-! The quotient Gaussian volume is the actual anchored complete-graph
Gaussian integral, including its determinant and all dimension factors. -/

namespace Wormald
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators

def completeQuotientPrecision (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  ((n + 2 : ℕ) : ℝ) • 1 - Matrix.vecMulVec (fun _ => 1) (fun _ => 1)

theorem completeQuotientPrecision_quadratic (n : ℕ) (x : Fin (n + 1) → ℝ) :
    x ⬝ᵥ (completeQuotientPrecision n *ᵥ x) =
      ((n + 2 : ℕ) : ℝ) * (∑ i, x i ^ 2) - (∑ i, x i) ^ 2 := by
  rw [completeQuotientPrecision, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    dotProduct_mulVec, Matrix.vecMul_vecMulVec, smul_dotProduct, smul_eq_mul]
  simp only [dotProduct, mul_one, one_mul, pow_two]

theorem completeQuotientPrecision_posDef (n : ℕ) : (completeQuotientPrecision n).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.isHermitian_iff_isSymm]
    change (completeQuotientPrecision n).transpose = completeQuotientPrecision n
    simp [completeQuotientPrecision, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_vecMulVec]
  · intro x hx
    simp only [star_trivial]
    rw [completeQuotientPrecision_quadratic]
    have hp : 0 < ∑ i, x i ^ 2 := by
      simpa only [dotProduct, star_trivial, pow_two] using
        (dotProduct_star_self_pos_iff (v := x)).mpr hx
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x)
    simp only [Finset.card_univ, Fintype.card_fin] at hcs
    push_cast at hcs ⊢
    nlinarith

theorem det_completeQuotientPrecision (n : ℕ) :
    (completeQuotientPrecision n).det = ((n + 2 : ℕ) : ℝ) ^ n := by
  let d : ℝ := ((n + 2 : ℕ) : ℝ)
  let G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := d • 1
  have hd : d ≠ 0 := by dsimp [d]; positivity
  have hunit : IsUnit G.det := by
    apply isUnit_iff_ne_zero.mpr
    simp [G, hd]
  have hinv : G⁻¹ = d⁻¹ • 1 := by
    apply Matrix.inv_eq_left_inv
    simp [G, smul_smul, hd]
  change (G - Matrix.vecMulVec (fun _ => 1) (fun _ => 1)).det = d ^ n
  rw [det_sub_vecMulVec G _ _ hunit, hinv]
  simp only [G, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one,
    Matrix.smul_mulVec, Matrix.one_mulVec]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_one, one_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [pow_succ]
  dsimp [d]
  push_cast
  field_simp
  ring

theorem integral_completeQuotientGaussian (n : ℕ) :
    (∫ x : Fin (n + 1) → ℝ, matrixGaussian (completeQuotientPrecision n) x) =
      quotientGaussianVolume (n + 2) := by
  have hsqrt (k : ℕ) : Real.sqrt (((n + 2 : ℕ) : ℝ) ^ k) =
      Real.sqrt ((n + 2 : ℕ) : ℝ) ^ k := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
  rw [integral_matrixGaussian _ (completeQuotientPrecision_posDef n),
    det_completeQuotientPrecision, hsqrt, quotientGaussianVolume]
  simp

end
end Wormald
