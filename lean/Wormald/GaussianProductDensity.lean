import Wormald.GaussianMatrixIntegral
import Mathlib.Probability.Distributions.Gaussian.Real

/-! The actual finite standard-normal product law, with the exact Lebesgue
density and normalization. This connects probabilistic concentration estimates
to the Gaussian integrals used in regular-tournament enumeration. -/

namespace Wormald
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

def standardNormalProductDensity (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal 0 1 (x i)

theorem standardNormalProductDensity_nonneg (n : ℕ) (x : Fin n → ℝ) :
    0 ≤ standardNormalProductDensity n x :=
  Finset.prod_nonneg fun _ _ => gaussianPDFReal_nonneg _ _ _

theorem continuous_standardNormalProductDensity (n : ℕ) :
    Continuous (standardNormalProductDensity n) := by
  unfold standardNormalProductDensity gaussianPDFReal
  fun_prop

theorem standardNormalProductDensity_eq (n : ℕ) (x : Fin n → ℝ) :
    standardNormalProductDensity n x =
      (Real.sqrt (2 * Real.pi) ^ n)⁻¹ * standardGaussian n x := by
  unfold standardNormalProductDensity
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  simp_rw [show ∀ t : ℝ, -(t ^ 2) / 2 = -(1 / 2 : ℝ) * t ^ 2 by intro t; ring]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    one_div, inv_pow, standardGaussian_eq_prod]
  simp only [one_div]

theorem standardNormalProduct_eq_withDensity (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun x => ENNReal.ofReal (standardNormalProductDensity n x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hint : Integrable (standardNormalProductDensity n)
      (volume.restrict (Set.univ.pi s)) := by
    change Integrable (standardNormalProductDensity n)
      ((Measure.pi fun _ : Fin n => (volume : Measure ℝ)).restrict (Set.univ.pi s))
    rw [MeasureTheory.Measure.restrict_pi_pi]
    exact Integrable.fintype_prod (fun _ => (integrable_gaussianPDFReal 0 1).restrict)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (standardNormalProductDensity_nonneg n))]
  change ENNReal.ofReal (∫ x, (∏ i, gaussianPDFReal 0 1 (x i))
    ∂(Measure.pi fun _ : Fin n => (volume : Measure ℝ)).restrict (Set.univ.pi s)) = _
  rw [MeasureTheory.Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  calc
    _ = ∏ i, ENNReal.ofReal (∫ x in s i, gaussianPDFReal 0 1 x) :=
      ENNReal.ofReal_prod_of_nonneg fun i _ =>
        integral_nonneg fun x => gaussianPDFReal_nonneg 0 1 x
    _ = _ := Finset.prod_congr rfl fun i _ =>
      (gaussianReal_apply_eq_integral 0 (v := 1) (by norm_num) (s i)).symm

theorem integral_standardNormalProduct {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : (Fin n → ℝ) → E) :
    (∫ x, f x ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ x, standardNormalProductDensity n x • f x := by
  rw [standardNormalProduct_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_standardNormalProductDensity n).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (standardNormalProductDensity_nonneg n _)]

theorem integrable_standardNormalProduct_iff {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : (Fin n → ℝ) → E) :
    Integrable f (Measure.pi (fun _ => gaussianReal 0 1)) ↔
      Integrable (fun x => standardNormalProductDensity n x • f x) := by
  rw [standardNormalProduct_eq_withDensity,
    integrable_withDensity_iff_integrable_smul'
      (continuous_standardNormalProductDensity n).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (standardNormalProductDensity_nonneg n _)]

end
end Wormald
