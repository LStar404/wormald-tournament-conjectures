import Wormald.GaussianGraphIntegral

namespace Wormald
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem integral_graphGaussianFourier {m : ℕ} (G : GaussianGraphData m)
    (r : ℝ) (hr : 0 ≤ r) (hr4 : 4 * r < 1) :
    (∫ x : Fin m → ℝ, matrixGaussianFourier (1 - r • G.laplacian)
      (Real.sqrt r • G.imbalance) x) =
        ((Real.sqrt (2 * Real.pi) ^ m * Real.exp (graphGaussianLogFactor G r) : ℝ) : ℂ) := by
  have hM := posDef_one_sub_smul_graphLaplacian G r hr hr4
  have hquad : (Real.sqrt r • G.imbalance) ⬝ᵥ
      ((1 - r • G.laplacian)⁻¹ *ᵥ (Real.sqrt r • G.imbalance)) =
      r * (G.imbalance ⬝ᵥ ((1 - r • G.laplacian)⁻¹ *ᵥ G.imbalance)) := by
    simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt hr]
  rw [integral_matrixGaussianFourier _ hM, hquad]
  have hroot : Real.exp (Real.log (1 - r • G.laplacian).det / 2) =
      Real.sqrt (1 - r • G.laplacian).det := by
    rw [← Real.log_sqrt hM.det_pos.le, Real.exp_log (Real.sqrt_pos.mpr hM.det_pos)]
  have hexp : Real.exp (graphGaussianLogFactor G r) =
      (Real.sqrt (1 - r • G.laplacian).det)⁻¹ *
        Real.exp (-(r * (G.imbalance ⬝ᵥ
          ((1 - r • G.laplacian)⁻¹ *ᵥ G.imbalance))) / 2) := by
    rw [graphGaussianLogFactor, show
      -Real.log (1 - r • G.laplacian).det / 2 - r / 2 *
        (G.imbalance ⬝ᵥ ((1 - r • G.laplacian)⁻¹ *ᵥ G.imbalance)) =
      -(Real.log (1 - r • G.laplacian).det / 2) +
        -(r * (G.imbalance ⬝ᵥ ((1 - r • G.laplacian)⁻¹ *ᵥ G.imbalance))) / 2 by ring,
      Real.exp_add, Real.exp_neg, hroot]
  rw [hexp]
  push_cast
  ring

theorem graphGaussianWeight_mul_gaussian {m : ℕ} (G : GaussianGraphData m)
    (r : ℝ) (x : Fin m → ℝ) :
    (standardGaussian m x : ℂ) * graphGaussianWeight G r x =
      matrixGaussianFourier (1 - r • G.laplacian) (Real.sqrt r • G.imbalance) x := by
  simp only [graphGaussianWeight, graphQuadraticWeight, standardGaussian,
    Complex.ofReal_exp, ← Complex.exp_add, matrixGaussianFourier]
  congr 1
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  simp only [dotProduct, ← pow_two]
  push_cast
  ring

/-- Both the imaginary endpoint phase and the determinant correction are
evaluated in the genuine finite Gaussian product probability space. -/
theorem integral_graphGaussianWeight {m : ℕ} (G : GaussianGraphData m)
    (r : ℝ) (hr : 0 ≤ r) (hr4 : 4 * r < 1) :
    (∫ x, graphGaussianWeight G r x ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      (Real.exp (graphGaussianLogFactor G r) : ℂ) := by
  rw [integral_standardNormalProduct]
  simp only [standardNormalProductDensity_eq, Complex.real_smul, Complex.ofReal_mul,
    mul_assoc]
  simp_rw [graphGaussianWeight_mul_gaussian]
  rw [integral_const_mul, integral_graphGaussianFourier G r hr hr4]
  have hc : (Real.sqrt (2 * Real.pi) ^ m : ℂ) ≠ 0 := by
    exact_mod_cast (show Real.sqrt (2 * Real.pi) ^ m ≠ 0 by positivity)
  push_cast
  field_simp

theorem graphGaussian_relative_error_le {m : ℕ} (hmNat : 16 ≤ m)
    (G : GaussianGraphData m) :
    |Real.exp (graphGaussianLogFactor G (1 / (m : ℝ)) - G.joinCount / (m : ℝ)) - 1| ≤
      32 / (m : ℝ) := by
  have hm16 : 16 ≤ (m : ℝ) := by exact_mod_cast hmNat
  have hm : 0 < (m : ℝ) := by linarith
  have hr : 0 ≤ 1 / (m : ℝ) := by positivity
  have hr8 : 1 / (m : ℝ) ≤ 1 / 8 :=
    (div_le_div_iff₀ hm (by norm_num)).mpr (by linarith)
  have hc : (G.edgeCount : ℝ) ≤ m := by exact_mod_cast G.edges_le
  have he := graphGaussianLogFactor_error G (1 / (m : ℝ)) hr hr8
  have hbound : |graphGaussianLogFactor G (1 / (m : ℝ)) - G.joinCount / (m : ℝ)| ≤
      16 / (m : ℝ) := by
    calc
      _ = |graphGaussianLogFactor G (1 / (m : ℝ)) - (1 / (m : ℝ)) * G.joinCount| := by
        congr 1; ring
      _ ≤ 16 * (1 / (m : ℝ)) ^ 2 * G.edgeCount := he
      _ ≤ 16 * (1 / (m : ℝ)) ^ 2 * m := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 16 / (m : ℝ) := by field_simp
  have hone : 16 / (m : ℝ) ≤ 1 := (div_le_iff₀ hm).mpr (by linarith)
  calc
    _ ≤ 2 * |graphGaussianLogFactor G (1 / (m : ℝ)) - G.joinCount / (m : ℝ)| :=
      Real.abs_exp_sub_one_le (hbound.trans hone)
    _ ≤ 2 * (16 / (m : ℝ)) := mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = _ := by ring

end
end Wormald
