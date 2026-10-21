import Wormald.ForestGaussianCorrection
import Wormald.GaussianMatrixFourier

/-! Exact Gaussian evaluation for the actual path-forest Laplacian and
endpoint imbalance. This supplies the finite integral represented by the
uniform correction bounds, rather than postulating a Gaussian approximation. -/

namespace Wormald
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators

theorem integral_forestGaussian {n : ℕ} (S : Finset (Fin n))
    (r : ℝ) (hr : 0 ≤ r) (hr4 : 4 * r < 1) :
    (∫ x : Fin (n + 1) → ℝ, matrixGaussianFourier (1 - r • forestLaplacian S)
      (Real.sqrt r • forestImbalance S) x) =
        ((Real.sqrt (2 * Real.pi) ^ (n + 1) * Real.exp (forestGaussianLogFactor S r) : ℝ) : ℂ) := by
  have hM := posDef_one_sub_smul_forestLaplacian S r hr hr4
  have hquad : (Real.sqrt r • forestImbalance S) ⬝ᵥ
      ((1 - r • forestLaplacian S)⁻¹ *ᵥ (Real.sqrt r • forestImbalance S)) =
      r * (forestImbalance S ⬝ᵥ ((1 - r • forestLaplacian S)⁻¹ *ᵥ forestImbalance S)) := by
    simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt hr]
  rw [integral_matrixGaussianFourier _ hM, hquad]
  have hroot : Real.exp (Real.log (1 - r • forestLaplacian S).det / 2) =
      Real.sqrt (1 - r • forestLaplacian S).det := by
    rw [← Real.log_sqrt hM.det_pos.le, Real.exp_log (Real.sqrt_pos.mpr hM.det_pos)]
  have hexp : Real.exp (forestGaussianLogFactor S r) =
      (Real.sqrt (1 - r • forestLaplacian S).det)⁻¹ *
        Real.exp (-(r * (forestImbalance S ⬝ᵥ
          ((1 - r • forestLaplacian S)⁻¹ *ᵥ forestImbalance S))) / 2) := by
    rw [forestGaussianLogFactor, show
      -Real.log (1 - r • forestLaplacian S).det / 2 - r / 2 *
        (forestImbalance S ⬝ᵥ ((1 - r • forestLaplacian S)⁻¹ *ᵥ forestImbalance S)) =
      -(Real.log (1 - r • forestLaplacian S).det / 2) +
        -(r * (forestImbalance S ⬝ᵥ ((1 - r • forestLaplacian S)⁻¹ *ᵥ forestImbalance S))) / 2 by ring,
      Real.exp_add, Real.exp_neg, hroot]
  rw [hexp]
  push_cast
  ring

end
end Wormald
