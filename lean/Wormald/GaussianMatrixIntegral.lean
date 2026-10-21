import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Matrix.Order

/-! The real multivariate Gaussian integral with its exact determinant
constant. The proof uses one-dimensional Gaussians, a genuine Lebesgue
change of variables, and the positive matrix square root. -/

namespace Wormald
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators MatrixOrder

def standardGaussian (k : ℕ) (x : Fin k → ℝ) : ℝ :=
  Real.exp (-(∑ i, x i ^ 2) / 2)

theorem standardGaussian_eq_prod (k : ℕ) (x : Fin k → ℝ) :
    standardGaussian k x = ∏ i, Real.exp (-(1 / 2 : ℝ) * x i ^ 2) := by
  unfold standardGaussian
  rw [← Real.exp_sum]
  congr 1
  simp only [← Finset.mul_sum]
  ring

theorem integrable_standardGaussian (k : ℕ) : Integrable (standardGaussian k) := by
  have hfun : standardGaussian k = fun x => ∏ i, Real.exp (-(1 / 2 : ℝ) * x i ^ 2) :=
    funext (standardGaussian_eq_prod k)
  rw [hfun]
  exact Integrable.fintype_prod (f := fun _ : Fin k => fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t ^ 2))
    (fun _ => integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2))

theorem integral_standardGaussian (k : ℕ) :
    (∫ x : Fin k → ℝ, standardGaussian k x) = Real.sqrt (2 * Real.pi) ^ k := by
  simp_rw [standardGaussian_eq_prod]
  rw [integral_fintype_prod_volume_eq_prod
    (f := fun _ : Fin k => fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t ^ 2))]
  simp only [integral_gaussian, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 2
  ring

theorem continuous_standardGaussian (k : ℕ) : Continuous (standardGaussian k) := by
  unfold standardGaussian
  fun_prop

theorem integrable_standardGaussian_mulVec {k : ℕ} (L : Matrix (Fin k) (Fin k) ℝ)
    (hL : L.det ≠ 0) : Integrable (fun x => standardGaussian k (L *ᵥ x)) := by
  have hmeas : Measurable (Matrix.toLin' L) :=
    (Matrix.toLin' L).continuous_of_finiteDimensional.measurable
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hL
  have hg : Integrable (standardGaussian k) (Measure.map (Matrix.toLin' L) volume) := by
    rw [hmap]
    exact (integrable_standardGaussian k).smul_measure ENNReal.ofReal_ne_top
  exact hg.comp_measurable hmeas

theorem integral_standardGaussian_mulVec {k : ℕ} (L : Matrix (Fin k) (Fin k) ℝ)
    (hL : L.det ≠ 0) :
    (∫ x : Fin k → ℝ, standardGaussian k (L *ᵥ x)) =
      Real.sqrt (2 * Real.pi) ^ k / |L.det| := by
  have hmeas : Measurable (Matrix.toLin' L) :=
    (Matrix.toLin' L).continuous_of_finiteDimensional.measurable
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hL
  change (∫ x : Fin k → ℝ, standardGaussian k ((Matrix.toLin' L) x)) = _
  rw [← integral_map hmeas.aemeasurable (continuous_standardGaussian k).aestronglyMeasurable,
    hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul,
    integral_standardGaussian, abs_inv]
  ring

def matrixGaussian {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) (x : Fin k → ℝ) : ℝ :=
  Real.exp (-(x ⬝ᵥ (S *ᵥ x)) / 2)

private theorem matrixGaussian_eq_sqrt {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ)
    (hS : S.PosDef) (x : Fin k → ℝ) :
    matrixGaussian S x = standardGaussian k ((CFC.sqrt S) *ᵥ x) := by
  have hroot : (CFC.sqrt S).transpose = CFC.sqrt S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg S).posSemidef.isHermitian.eq
  have hsq : (CFC.sqrt S).transpose * CFC.sqrt S = S := by
    rw [hroot, ← pow_two]
    exact CFC.sq_sqrt S hS.posSemidef.nonneg
  have hquad : (x ⬝ᵥ (S *ᵥ x)) = ∑ i, ((CFC.sqrt S) *ᵥ x) i ^ 2 := by
    calc
      _ = x ⬝ᵥ ((CFC.sqrt S).transpose *ᵥ ((CFC.sqrt S) *ᵥ x)) := by
        rw [Matrix.mulVec_mulVec, hsq]
      _ = ((CFC.sqrt S) *ᵥ x) ⬝ᵥ ((CFC.sqrt S) *ᵥ x) :=
        Matrix.dotProduct_transpose_mulVec _ _ _
      _ = _ := by simp only [dotProduct, pow_two]
  simp only [matrixGaussian, standardGaussian, hquad]

theorem integrable_matrixGaussian {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ)
    (hS : S.PosDef) : Integrable (matrixGaussian S) := by
  have hdet : (CFC.sqrt S).det = Real.sqrt S.det := by
    simpa only [RCLike.sqrt_real] using hS.posSemidef.det_sqrt
  have hne : (CFC.sqrt S).det ≠ 0 := by
    rw [hdet]
    exact ne_of_gt (Real.sqrt_pos.mpr hS.det_pos)
  have hfun : matrixGaussian S = fun x => standardGaussian k ((CFC.sqrt S) *ᵥ x) :=
    funext (matrixGaussian_eq_sqrt S hS)
  rw [hfun]
  exact integrable_standardGaussian_mulVec (CFC.sqrt S) hne

/-- The exact real Gaussian constant, including the zero-dimensional case. -/
theorem integral_matrixGaussian {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ)
    (hS : S.PosDef) :
    (∫ x : Fin k → ℝ, matrixGaussian S x) =
      Real.sqrt (2 * Real.pi) ^ k / Real.sqrt S.det := by
  have hdet : (CFC.sqrt S).det = Real.sqrt S.det := by
    simpa only [RCLike.sqrt_real] using hS.posSemidef.det_sqrt
  have hne : (CFC.sqrt S).det ≠ 0 := by
    rw [hdet]
    exact ne_of_gt (Real.sqrt_pos.mpr hS.det_pos)
  simp_rw [matrixGaussian_eq_sqrt S hS]
  rw [integral_standardGaussian_mulVec _ hne, hdet, abs_of_nonneg (Real.sqrt_nonneg _)]

end
end Wormald
