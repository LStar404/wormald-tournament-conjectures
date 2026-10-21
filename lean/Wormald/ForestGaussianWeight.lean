import Wormald.ForestGaussianCorrection
import Wormald.GaussianMatrixIntegral

/-! A dimension-independent L² bound for the deleted-edge Gaussian weight.
This permits Cauchy--Schwarz cancellation of the common quartic factor. -/

namespace Wormald
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators

def forestQuadraticWeight {n : ℕ} (S : Finset (Fin n)) (r : ℝ)
    (x : Fin (n + 1) → ℝ) : ℝ :=
  Real.exp (r / 2 * (x ⬝ᵥ (forestLaplacian S *ᵥ x)))

theorem forestQuadraticWeight_sq_mul_gaussian {n : ℕ} (S : Finset (Fin n))
    (r : ℝ) (x : Fin (n + 1) → ℝ) :
    forestQuadraticWeight S r x ^ 2 * standardGaussian (n + 1) x =
      matrixGaussian (1 - (2 * r) • forestLaplacian S) x := by
  rw [forestQuadraticWeight, ← Real.exp_nat_mul, standardGaussian,
    ← Real.exp_add, matrixGaussian]
  congr 1
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
  simp only [smul_eq_mul, dotProduct, ← pow_two]
  ring

theorem integrable_forestQuadraticWeight_sq {n : ℕ} (S : Finset (Fin n))
    (r : ℝ) (hr : 0 ≤ r) (hr8 : 8 * r < 1) :
    Integrable (fun x => forestQuadraticWeight S r x ^ 2 * standardGaussian (n + 1) x) := by
  simp_rw [forestQuadraticWeight_sq_mul_gaussian]
  exact integrable_matrixGaussian _
    (posDef_one_sub_smul_forestLaplacian S (2 * r) (by positivity) (by linarith))

theorem integral_forestQuadraticWeight_sq {n : ℕ} (S : Finset (Fin n))
    (r : ℝ) (hr : 0 ≤ r) (hr8 : 8 * r < 1) :
    (∫ x, forestQuadraticWeight S r x ^ 2 * standardGaussian (n + 1) x) =
      Real.sqrt (2 * Real.pi) ^ (n + 1) /
        Real.sqrt (1 - (2 * r) • forestLaplacian S).det := by
  simp_rw [forestQuadraticWeight_sq_mul_gaussian]
  exact integral_matrixGaussian _
    (posDef_one_sub_smul_forestLaplacian S (2 * r) (by positivity) (by linarith))

/-- A single absolute L² bound holds for every forest and every sufficiently
large number of vertices. No relation between the forests at different sizes
is needed. -/
theorem forestQuadraticWeight_gaussian_L2_le {n : ℕ} (hn : 16 ≤ n + 1)
    (S : Finset (Fin n)) :
    (∫ x, forestQuadraticWeight S (1 / ((n + 1 : ℕ) : ℝ)) x ^ 2 *
      standardGaussian (n + 1) x) ≤
        Real.exp 4 * Real.sqrt (2 * Real.pi) ^ (n + 1) := by
  let m : ℝ := ((n + 1 : ℕ) : ℝ)
  have hm16 : 16 ≤ m := by dsimp [m]; exact_mod_cast hn
  have hm : 0 < m := by linarith
  have hr : 0 ≤ 1 / m := le_of_lt (one_div_pos.mpr hm)
  have h2r : 0 ≤ 2 * (1 / m) := by positivity
  have h2r8 : 2 * (1 / m) ≤ 1 / 8 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    calc
      2 * (1 / m) * 8 = 16 / m := by ring
      _ ≤ 1 := (div_le_iff₀ hm).mpr (by linarith)
  have hc : (S.card : ℝ) ≤ m := by
    have h := S.card_le_univ
    simp only [Fintype.card_fin] at h
    have hcast : (S.card : ℝ) ≤ n := by exact_mod_cast h
    dsimp [m]
    push_cast
    linarith
  have hP := posDef_one_sub_smul_forestLaplacian S (2 * (1 / m)) h2r (by linarith)
  have hdet := forest_logdet_quadratic_error S (2 * (1 / m)) h2r h2r8
  have hexponent : -Real.log (1 - (2 * (1 / m)) • forestLaplacian S).det / 2 ≤ 4 := by
    have he := (abs_le.mp hdet).1
    have hlead : (2 * (1 / m)) * S.card ≤ 2 := by
      have hh := mul_le_mul_of_nonneg_left hc h2r
      have heq : 2 * (1 / m) * m = 2 := by field_simp
      linarith
    have herr : 8 * (2 * (1 / m)) ^ 2 * S.card ≤ 2 := by
      have hh := mul_le_mul_of_nonneg_left hc
        (show 0 ≤ 8 * (2 * (1 / m)) ^ 2 by positivity)
      have heq : 8 * (2 * (1 / m)) ^ 2 * m = 32 / m := by field_simp; ring
      rw [heq] at hh
      have h32 : 32 / m ≤ 2 := (div_le_iff₀ hm).mpr (by linarith)
      exact hh.trans h32
    linarith
  have hroot : (Real.sqrt (1 - (2 * (1 / m)) • forestLaplacian S).det)⁻¹ =
      Real.exp (-Real.log (1 - (2 * (1 / m)) • forestLaplacian S).det / 2) := by
    rw [show -Real.log (1 - (2 * (1 / m)) • forestLaplacian S).det / 2 =
      -(Real.log (1 - (2 * (1 / m)) • forestLaplacian S).det / 2) by ring,
      Real.exp_neg, ← Real.log_sqrt hP.det_pos.le, Real.exp_log (Real.sqrt_pos.mpr hP.det_pos)]
  change (∫ x, forestQuadraticWeight S (1 / m) x ^ 2 * standardGaussian (n + 1) x) ≤ _
  rw [integral_forestQuadraticWeight_sq S (1 / m) hr (by linarith), div_eq_mul_inv, hroot, mul_comm]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexponent) (by positivity)

end
end Wormald
