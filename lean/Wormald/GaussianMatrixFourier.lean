import Wormald.GaussianMatrixIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! The exact Fourier transform of a positive definite real matrix Gaussian.
The proof reduces to independent one-dimensional complex Gaussians and uses
the actual positive matrix square root in a Lebesgue change of variables. -/

namespace Wormald
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators MatrixOrder

def standardGaussianFourier {k : ℕ} (b x : Fin k → ℝ) : ℂ :=
  Complex.exp (-((∑ i, x i ^ 2 : ℝ) : ℂ) / 2 + ((b ⬝ᵥ x : ℝ) : ℂ) * Complex.I)

theorem norm_standardGaussianFourier {k : ℕ} (b x : Fin k → ℝ) :
    ‖standardGaussianFourier b x‖ = standardGaussian k x := by
  simp [standardGaussianFourier, standardGaussian, Complex.norm_exp, pow_two, Complex.mul_re]

theorem continuous_standardGaussianFourier {k : ℕ} (b : Fin k → ℝ) :
    Continuous (standardGaussianFourier b) := by
  unfold standardGaussianFourier dotProduct
  fun_prop

theorem integrable_standardGaussianFourier {k : ℕ} (b : Fin k → ℝ) :
    Integrable (standardGaussianFourier b) :=
  (integrable_standardGaussian k).mono'
    (continuous_standardGaussianFourier b).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (norm_standardGaussianFourier b x).le)

private theorem complex_halfGaussian_constant :
    ((Real.pi : ℂ) / (1 / 2 : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt (2 * Real.pi) : ℂ) := by
  calc
    _ = (((Real.pi / (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by positivity : 0 ≤ Real.pi / (1 / 2 : ℝ))]
      norm_num
    _ = _ := by
      rw [← Real.sqrt_eq_rpow]
      congr 1
      congr 1
      ring

theorem integral_standardGaussianFourier {k : ℕ} (b : Fin k → ℝ) :
    (∫ x : Fin k → ℝ, standardGaussianFourier b x) =
      (Real.sqrt (2 * Real.pi) ^ k : ℂ) * Complex.exp (-((b ⬝ᵥ b : ℝ) : ℂ) / 2) := by
  have hfun : standardGaussianFourier b = fun x : Fin k → ℝ =>
      Complex.exp (-(∑ i, (1 / 2 : ℂ) * (x i : ℂ) ^ 2) +
        ∑ i, ((b i : ℂ) * Complex.I) * (x i : ℂ)) := by
    funext x
    unfold standardGaussianFourier dotProduct
    congr 1
    push_cast
    simp only [mul_right_comm _ Complex.I _, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [hfun, GaussianFourier.integral_cexp_neg_sum_mul_add (fun _ => by norm_num : ∀ _ : Fin k,
    0 < (1 / 2 : ℂ).re)]
  simp_rw [complex_halfGaussian_constant]
  have hexp (i : Fin k) :
      Complex.exp (((b i : ℂ) * Complex.I) ^ 2 / (4 * (1 / 2 : ℂ))) =
        Complex.exp (-((b i ^ 2 : ℝ) : ℂ) / 2) := by
    congr 1
    simp only [mul_pow, Complex.I_sq, Complex.ofReal_pow]
    ring
  simp_rw [hexp]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Complex.exp_sum]
  congr 1
  congr 1
  simp only [dotProduct, Complex.ofReal_sum, ← Finset.sum_div, ← Finset.sum_neg_distrib,
    Complex.ofReal_mul, pow_two]

theorem integral_standardGaussianFourier_mulVec {k : ℕ} (L : Matrix (Fin k) (Fin k) ℝ)
    (hL : L.det ≠ 0) (b : Fin k → ℝ) :
    (∫ x : Fin k → ℝ, standardGaussianFourier b (L *ᵥ x)) =
      ((Real.sqrt (2 * Real.pi) ^ k / |L.det| : ℝ) : ℂ) *
        Complex.exp (-((b ⬝ᵥ b : ℝ) : ℂ) / 2) := by
  have hmeas : Measurable (Matrix.toLin' L) :=
    (Matrix.toLin' L).continuous_of_finiteDimensional.measurable
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hL
  change (∫ x : Fin k → ℝ, standardGaussianFourier b ((Matrix.toLin' L) x)) = _
  rw [← integral_map hmeas.aemeasurable
      (continuous_standardGaussianFourier b).aestronglyMeasurable,
    hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _),
    integral_standardGaussianFourier, abs_inv, Complex.real_smul]
  push_cast
  ring

def matrixGaussianFourier {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ)
    (b x : Fin k → ℝ) : ℂ :=
  Complex.exp (-((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) / 2 + ((b ⬝ᵥ x : ℝ) : ℂ) * Complex.I)

theorem norm_matrixGaussianFourier {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ)
    (b x : Fin k → ℝ) :
    ‖matrixGaussianFourier S b x‖ = matrixGaussian S x := by
  simp [matrixGaussianFourier, matrixGaussian, Complex.norm_exp]

theorem integrable_matrixGaussianFourier {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ)
    (hS : S.PosDef) (b : Fin k → ℝ) : Integrable (matrixGaussianFourier S b) := by
  refine (integrable_matrixGaussian S hS).mono' ?_
    (Filter.Eventually.of_forall fun x => (norm_matrixGaussianFourier S b x).le)
  apply Continuous.aestronglyMeasurable
  unfold matrixGaussianFourier dotProduct Matrix.mulVec
  fun_prop

/-- The multivariate Fourier Gaussian formula, including dimension zero. -/
theorem integral_matrixGaussianFourier {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ)
    (hS : S.PosDef) (b : Fin k → ℝ) :
    (∫ x : Fin k → ℝ, matrixGaussianFourier S b x) =
      ((Real.sqrt (2 * Real.pi) ^ k / Real.sqrt S.det : ℝ) : ℂ) *
        Complex.exp (-((b ⬝ᵥ (S⁻¹ *ᵥ b) : ℝ) : ℂ) / 2) := by
  let L := CFC.sqrt S
  have hsymm : L.transpose = L := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg S).posSemidef.isHermitian.eq
  have hsq : L * L = S := by
    rw [← pow_two]
    exact CFC.sq_sqrt S hS.posSemidef.nonneg
  have hdet : L.det = Real.sqrt S.det := by
    simpa only [RCLike.sqrt_real] using hS.posSemidef.det_sqrt
  have hne : L.det ≠ 0 := by rw [hdet]; exact ne_of_gt (Real.sqrt_pos.mpr hS.det_pos)
  have hunit : IsUnit L.det := isUnit_iff_ne_zero.mpr hne
  let c := L⁻¹ *ᵥ b
  have hquad (x : Fin k → ℝ) : x ⬝ᵥ (S *ᵥ x) = ∑ i, (L *ᵥ x) i ^ 2 := by
    calc
      _ = x ⬝ᵥ (L.transpose *ᵥ (L *ᵥ x)) := by rw [hsymm, Matrix.mulVec_mulVec, hsq]
      _ = (L *ᵥ x) ⬝ᵥ (L *ᵥ x) := Matrix.dotProduct_transpose_mulVec _ _ _
      _ = _ := by simp only [dotProduct, pow_two]
  have hlin (x : Fin k → ℝ) : c ⬝ᵥ (L *ᵥ x) = b ⬝ᵥ x := by
    change (L⁻¹ *ᵥ b) ⬝ᵥ (L *ᵥ x) = _
    rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec,
      Matrix.transpose_nonsing_inv, hsymm, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  have hc : c ⬝ᵥ c = b ⬝ᵥ (S⁻¹ *ᵥ b) := by
    change (L⁻¹ *ᵥ b) ⬝ᵥ (L⁻¹ *ᵥ b) = _
    rw [← Matrix.dotProduct_transpose_mulVec, Matrix.transpose_nonsing_inv, hsymm,
      Matrix.mulVec_mulVec, ← Matrix.mul_inv_rev, hsq]
  have hfun : matrixGaussianFourier S b = fun x => standardGaussianFourier c (L *ᵥ x) := by
    funext x
    simp only [matrixGaussianFourier, standardGaussianFourier, hquad, hlin]
  rw [hfun, integral_standardGaussianFourier_mulVec L hne c, hdet,
    abs_of_nonneg (Real.sqrt_nonneg _), hc]

end
end Wormald
