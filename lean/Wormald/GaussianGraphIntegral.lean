import Wormald.GaussianGraphCorrection
import Wormald.GaussianMatrixFourier
import Wormald.GaussianProductDensity
import Mathlib.MeasureTheory.Function.L2Space

/-! Exact Gaussian evaluation and uniform L² bounds for the generic
degree-two graph data. The integrals below use the actual Gaussian product law. -/

namespace Wormald
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

def graphQuadraticWeight {m : ℕ} (G : GaussianGraphData m) (r : ℝ)
    (x : Fin m → ℝ) : ℝ := Real.exp (r / 2 * (x ⬝ᵥ (G.laplacian *ᵥ x)))

def graphGaussianWeight {m : ℕ} (G : GaussianGraphData m) (r : ℝ)
    (x : Fin m → ℝ) : ℂ :=
  (graphQuadraticWeight G r x : ℂ) *
    Complex.exp (((Real.sqrt r * (G.imbalance ⬝ᵥ x) : ℝ) : ℂ) * Complex.I)

theorem continuous_graphGaussianWeight {m : ℕ} (G : GaussianGraphData m) (r : ℝ) :
    Continuous (graphGaussianWeight G r) := by
  unfold graphGaussianWeight graphQuadraticWeight dotProduct Matrix.mulVec
  fun_prop

theorem norm_graphGaussianWeight {m : ℕ} (G : GaussianGraphData m) (r : ℝ)
    (x : Fin m → ℝ) : ‖graphGaussianWeight G r x‖ = graphQuadraticWeight G r x := by
  simp [graphGaussianWeight, graphQuadraticWeight, Complex.norm_exp]

theorem graphQuadraticWeight_sq_mul_gaussian {m : ℕ} (G : GaussianGraphData m)
    (r : ℝ) (x : Fin m → ℝ) :
    graphQuadraticWeight G r x ^ 2 * standardGaussian m x =
      matrixGaussian (1 - (2 * r) • G.laplacian) x := by
  rw [graphQuadraticWeight, ← Real.exp_nat_mul, standardGaussian,
    ← Real.exp_add, matrixGaussian]
  congr 1
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
  simp only [smul_eq_mul, dotProduct, ← pow_two]
  ring

theorem integral_graphQuadraticWeight_sq {m : ℕ} (G : GaussianGraphData m)
    (r : ℝ) (hr : 0 ≤ r) (hr8 : 8 * r < 1) :
    (∫ x, graphQuadraticWeight G r x ^ 2 ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      (Real.sqrt (1 - (2 * r) • G.laplacian).det)⁻¹ := by
  rw [integral_standardNormalProduct]
  simp only [standardNormalProductDensity_eq, smul_eq_mul, mul_assoc]
  simp_rw [mul_comm (standardGaussian m _), graphQuadraticWeight_sq_mul_gaussian]
  rw [integral_const_mul, integral_matrixGaussian _
    (posDef_one_sub_smul_graphLaplacian G (2 * r) (by positivity) (by linarith))]
  have hc : Real.sqrt (2 * Real.pi) ^ m ≠ 0 := by positivity
  field_simp

theorem memLp_graphGaussianWeight {m : ℕ} (G : GaussianGraphData m)
    (r : ℝ) (hr : 0 ≤ r) (hr8 : 8 * r < 1) :
    MemLp (graphGaussianWeight G r) 2 (Measure.pi (fun _ => gaussianReal 0 1)) := by
  apply (memLp_two_iff_integrable_sq_norm
    (continuous_graphGaussianWeight G r).aestronglyMeasurable).mpr
  simp_rw [norm_graphGaussianWeight]
  rw [integrable_standardNormalProduct_iff]
  simp only [standardNormalProductDensity_eq, smul_eq_mul, mul_assoc]
  simp_rw [mul_comm (standardGaussian m _), graphQuadraticWeight_sq_mul_gaussian]
  exact (integrable_matrixGaussian _
    (posDef_one_sub_smul_graphLaplacian G (2 * r) (by positivity) (by linarith))).const_mul _

theorem graphGaussianWeight_L2_le {m : ℕ} (hmNat : 16 ≤ m) (G : GaussianGraphData m) :
    (∫ x, ‖graphGaussianWeight G (1 / (m : ℝ)) x‖ ^ 2
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤ Real.exp 4 := by
  have hm16 : 16 ≤ (m : ℝ) := by exact_mod_cast hmNat
  have hm : 0 < (m : ℝ) := by linarith
  have hr : 0 ≤ 1 / (m : ℝ) := by positivity
  have h2r : 0 ≤ 2 * (1 / (m : ℝ)) := by positivity
  have h2r8 : 2 * (1 / (m : ℝ)) ≤ 1 / 8 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    calc
      2 * (1 / (m : ℝ)) * 8 = 16 / m := by ring
      _ ≤ 1 := (div_le_iff₀ hm).mpr (by linarith)
  have hc : (G.edgeCount : ℝ) ≤ m := by exact_mod_cast G.edges_le
  have hP := posDef_one_sub_smul_graphLaplacian G (2 * (1 / (m : ℝ))) h2r (by linarith)
  have hdet := graph_logdet_quadratic_error G (2 * (1 / (m : ℝ))) h2r h2r8
  have hexponent : -Real.log (1 - (2 * (1 / (m : ℝ))) • G.laplacian).det / 2 ≤ 4 := by
    have he := (abs_le.mp hdet).1
    have hlead : (2 * (1 / (m : ℝ))) * G.edgeCount ≤ 2 := by
      have hh := mul_le_mul_of_nonneg_left hc h2r
      have heq : 2 * (1 / (m : ℝ)) * m = 2 := by field_simp
      linarith
    have herr : 8 * (2 * (1 / (m : ℝ))) ^ 2 * G.edgeCount ≤ 2 := by
      have hh := mul_le_mul_of_nonneg_left hc
        (show 0 ≤ 8 * (2 * (1 / (m : ℝ))) ^ 2 by positivity)
      have heq : 8 * (2 * (1 / (m : ℝ))) ^ 2 * m = 32 / m := by field_simp; ring
      rw [heq] at hh
      exact hh.trans ((div_le_iff₀ hm).mpr (by linarith))
    linarith
  have hroot : (Real.sqrt (1 - (2 * (1 / (m : ℝ))) • G.laplacian).det)⁻¹ =
      Real.exp (-Real.log (1 - (2 * (1 / (m : ℝ))) • G.laplacian).det / 2) := by
    rw [show -Real.log (1 - (2 * (1 / (m : ℝ))) • G.laplacian).det / 2 =
      -(Real.log (1 - (2 * (1 / (m : ℝ))) • G.laplacian).det / 2) by ring,
      Real.exp_neg, ← Real.log_sqrt hP.det_pos.le, Real.exp_log (Real.sqrt_pos.mpr hP.det_pos)]
  simp_rw [norm_graphGaussianWeight]
  rw [integral_graphQuadraticWeight_sq G (1 / (m : ℝ)) hr (by linarith), hroot]
  exact Real.exp_le_exp.mpr hexponent

end
end Wormald
