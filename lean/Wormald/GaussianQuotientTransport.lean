import Wormald.GaussianAnchoring

namespace Wormald
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

def anchorDifference {n : ℕ} (x : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun j => x j.castSucc - x (Fin.last n)

def rawAnchorPrecision (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - (1 / ((n + 1 : ℕ) : ℝ)) • Matrix.vecMulVec (fun _ => 1) (fun _ => 1)

def anchorQuotientPrecision (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  ((n + 1 : ℕ) : ℝ) • 1 - Matrix.vecMulVec (fun _ => 1) (fun _ => 1)

def scaledAnchorDifference {n : ℕ} (x : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ • anchorDifference x

theorem rawAnchorPrecision_eq_smul (n : ℕ) :
    rawAnchorPrecision n = (1 / ((n + 1 : ℕ) : ℝ)) • anchorQuotientPrecision n := by
  have hm : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [rawAnchorPrecision, anchorQuotientPrecision, smul_sub, smul_smul]
  rw [one_div, inv_mul_cancel₀ hm, one_smul]

theorem matrixGaussian_rawAnchor_eq_scaled {n : ℕ} (y : Fin n → ℝ) :
    matrixGaussian (rawAnchorPrecision n) y =
      matrixGaussian (anchorQuotientPrecision n)
        ((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ • y) := by
  rw [rawAnchorPrecision_eq_smul]
  simp only [matrixGaussian, Matrix.smul_mulVec, Matrix.mulVec_smul,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  congr 1
  rw [← mul_assoc, ← pow_two, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ))]
  ring

theorem rawAnchorPrecision_quadratic {n : ℕ} (y : Fin n → ℝ) :
    y ⬝ᵥ (rawAnchorPrecision n *ᵥ y) =
      (∑ j, y j ^ 2) - (∑ j, y j) ^ 2 / ((n + 1 : ℕ) : ℝ) := by
  rw [rawAnchorPrecision, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_mulVec,
    Matrix.vecMul_vecMulVec, smul_dotProduct, smul_eq_mul]
  simp only [dotProduct, mul_one, one_mul, ← pow_two]
  ring

theorem standardGaussian_snoc_translate {n : ℕ} (y : Fin n → ℝ) (t : ℝ) :
    standardGaussian (n + 1) (Fin.snoc (fun j => y j + t) t) =
      Real.exp (-(((n + 1 : ℕ) : ℝ) / 2) *
        (t + (∑ j, y j) / ((n + 1 : ℕ) : ℝ)) ^ 2) *
          matrixGaussian (rawAnchorPrecision n) y := by
  have hm : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hsum : (∑ j : Fin n, (y j + t) ^ 2) =
      (∑ j, y j ^ 2) + 2 * t * (∑ j, y j) + n * t ^ 2 := by
    simp only [add_sq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  rw [standardGaussian, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [hsum, matrixGaussian, rawAnchorPrecision_quadratic, ← Real.exp_add]
  congr 1
  field_simp
  push_cast
  ring

theorem integral_translated_center_gaussian {n : ℕ} (y : Fin n → ℝ) :
    (∫ t : ℝ, Real.exp (-(((n + 1 : ℕ) : ℝ) / 2) *
      (t + (∑ j, y j) / ((n + 1 : ℕ) : ℝ)) ^ 2)) =
        Real.sqrt (2 * Real.pi / ((n + 1 : ℕ) : ℝ)) := by
  rw [integral_add_right_eq_self (fun t : ℝ =>
    Real.exp (-(((n + 1 : ℕ) : ℝ) / 2) * t ^ 2)), integral_gaussian]
  congr 1
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integral_standardGaussian_anchorDifference {n : ℕ} (F : (Fin n → ℝ) → E)
    (hF : Integrable (fun x : Fin (n + 1) → ℝ =>
      standardGaussian (n + 1) x • F (anchorDifference x))) :
    (∫ x : Fin (n + 1) → ℝ, standardGaussian (n + 1) x • F (anchorDifference x)) =
      Real.sqrt (2 * Real.pi / ((n + 1 : ℕ) : ℝ)) •
        ∫ y : Fin n → ℝ, matrixGaussian (rawAnchorPrecision n) y • F y := by
  rw [integral_anchorShear_split _ hF, ← integral_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    have hd (t : ℝ) : anchorDifference (Fin.snoc (fun j => y j + t) t) = y := by
      ext j
      simp [anchorDifference]
    simp only [hd, standardGaussian_snoc_translate, mul_smul]
    rw [integral_smul_const, integral_translated_center_gaussian]

theorem integral_standardGaussian_scaledAnchorDifference {n : ℕ} (F : (Fin n → ℝ) → E)
    (hF : Integrable (fun x : Fin (n + 1) → ℝ =>
      standardGaussian (n + 1) x • F (scaledAnchorDifference x))) :
    (∫ x : Fin (n + 1) → ℝ, standardGaussian (n + 1) x • F (scaledAnchorDifference x)) =
      (Real.sqrt (2 * Real.pi / ((n + 1 : ℕ) : ℝ)) *
        Real.sqrt ((n + 1 : ℕ) : ℝ) ^ n) •
          ∫ y : Fin n → ℝ, matrixGaussian (anchorQuotientPrecision n) y • F y := by
  have h := integral_standardGaussian_anchorDifference
    (fun y => F ((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ • y)) hF
  change (∫ x : Fin (n + 1) → ℝ, standardGaussian (n + 1) x • F (scaledAnchorDifference x)) = _ at h
  rw [h]
  simp_rw [matrixGaussian_rawAnchor_eq_scaled]
  have hscale := Measure.integral_comp_inv_smul_of_nonneg volume
    (fun y : Fin n → ℝ => matrixGaussian (anchorQuotientPrecision n) y • F y)
    (Real.sqrt_nonneg ((n + 1 : ℕ) : ℝ))
  simp only [Module.finrank_pi, Fintype.card_fin] at hscale
  rw [hscale, smul_smul]

/-- The actual iid standard-normal law maps to the normalized anchored
complete-graph Gaussian under x ↦ (xᵢ−x_last)/√m. -/
theorem integral_standardNormalProduct_scaledAnchorDifference {n : ℕ}
    (F : (Fin (n + 1) → ℝ) → E)
    (hF : Integrable (fun x : Fin (n + 2) → ℝ => F (scaledAnchorDifference x))
      (Measure.pi (fun _ => gaussianReal 0 1))) :
    (∫ x : Fin (n + 2) → ℝ, F (scaledAnchorDifference x)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      (quotientGaussianVolume (n + 2))⁻¹ •
        ∫ y : Fin (n + 1) → ℝ, matrixGaussian (completeQuotientPrecision n) y • F y := by
  have ha : Real.sqrt (2 * Real.pi) ^ (n + 2) ≠ 0 := by positivity
  have hD := (integrable_standardNormalProduct_iff _).mp hF
  simp only [standardNormalProductDensity_eq, mul_smul] at hD
  have hH : Integrable (fun x : Fin (n + 2) → ℝ =>
      standardGaussian (n + 2) x • F (scaledAnchorDifference x)) := by
    apply (integrable_fun_smul_iff (inv_ne_zero ha) _).mp
    simpa only [smul_smul] using hD
  have hcoef : (Real.sqrt (2 * Real.pi) ^ (n + 2))⁻¹ *
      (Real.sqrt (2 * Real.pi / ((n + 2 : ℕ) : ℝ)) * Real.sqrt ((n + 2 : ℕ) : ℝ) ^ (n + 1)) =
        (quotientGaussianVolume (n + 2))⁻¹ := by
    have hs : Real.sqrt ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [Real.sqrt_div (by positivity), quotientGaussianVolume]
    rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega]
    simp only [pow_succ]
    field_simp
  rw [integral_standardNormalProduct]
  simp only [standardNormalProductDensity_eq, mul_smul]
  rw [integral_smul, integral_standardGaussian_scaledAnchorDifference F hH, smul_smul, hcoef]
  rfl

end
end Wormald
