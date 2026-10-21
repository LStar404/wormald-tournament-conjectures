import Wormald.GaussianCentralWindow
import Wormald.GaussianQuotientTransport
import Wormald.RegularFourierAnchoring
import Wormald.PartialPermutationShift

/-! Exact transport of the genuine physical central integral to iid
standard Gaussians. The Fourier kernel, the common translation, the
Gaussian density, and its dimension-dependent normalization all match. -/

namespace Wormald.FiniteModel
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem normalizedRegularPhysicalIntegrand_sub_const {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (x : Fin m → ℝ) (a : ℝ) :
    normalizedRegularPhysicalIntegrand D (fun i => x i - a) =
      normalizedRegularPhysicalIntegrand D x := by
  simp only [normalizedRegularPhysicalIntegrand, normalizedRegularIntegrand_radians D hD]
  have hphase : partialImbalance D ⬝ᵥ (fun i => x i - a) = partialImbalance D ⬝ᵥ x := by
    have heq : (fun i => x i - a) = x + fun _ => -a := by ext i; simp [sub_eq_add_neg]
    rw [heq, partialImbalance_dot_add_const]
  simp only [hphase, sub_sub_sub_cancel_right]

def anchoredRegularFactor {n : ℕ}
    (D : Finset (Fin (n + 1) × Fin (n + 1))) (y : Fin n → ℝ) : ℂ :=
  (Real.exp (completeSquareEnergy (Fin.snoc y 0) / 2) : ℂ) *
    normalizedRegularPhysicalIntegrand D (Fin.snoc y 0)

theorem continuous_anchoredRegularFactor {n : ℕ}
    (D : Finset (Fin (n + 1) × Fin (n + 1)))
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) : Continuous (anchoredRegularFactor D) := by
  unfold anchoredRegularFactor
  simp only [normalizedRegularPhysicalIntegrand, normalizedRegularIntegrand_radians D hD,
    completeSquareEnergy, dotProduct]
  fun_prop

theorem snoc_scaledAnchorDifference {n : ℕ} (x : Fin (n + 1) → ℝ) :
    Fin.snoc (scaledAnchorDifference x) 0 = fun i =>
      (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * x i -
        (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ * x (Fin.last n) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp [scaledAnchorDifference, anchorDifference, Pi.smul_apply, smul_eq_mul, mul_sub]

theorem anchoredRegularFactor_scaledAnchorDifference {n : ℕ}
    (D : Finset (Fin (n + 1) × Fin (n + 1)))
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) (x : Fin (n + 1) → ℝ) :
    anchoredRegularFactor D (scaledAnchorDifference x) = scaledRegularFactor D x := by
  rw [anchoredRegularFactor, snoc_scaledAnchorDifference,
    completeSquareEnergy_sub_const, normalizedRegularPhysicalIntegrand_sub_const D hD]
  rfl

theorem scaledAnchorDifference_mem_closedBall {n : ℕ} (r : ℝ) (hr : 0 ≤ r)
    (x : Fin (n + 1) → ℝ) :
    scaledAnchorDifference x ∈ Metric.closedBall 0 (r / 2) ↔
      x ∈ gaussianCentralWindow (Fin.last n) r := by
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ r / 2)]
  simp only [scaledAnchorDifference, anchorDifference, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
  constructor
  · intro h i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [sub_self, mul_zero, abs_zero]
      linarith
    · exact h j
  · intro h i
    exact h i.castSucc

theorem matrixGaussian_completeQuotientPrecision_energy {n : ℕ} (y : Fin (n + 1) → ℝ) :
    matrixGaussian (completeQuotientPrecision n) y =
      Real.exp (-completeSquareEnergy (Fin.snoc y 0) / 2) := by
  rw [matrixGaussian, completeQuotientPrecision_quadratic, completeSquareEnergy_eq]
  simp only [Fintype.card_fin, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    zero_pow (by norm_num : 2 ≠ 0), add_zero]

/-- This is an equality of actual integrals, not an asymptotic estimate.
No integrability premise is imposed: the truncated factor is bounded on
its compact physical window and the Gaussian law is a probability law. -/
theorem physicalCentralIntegral_div_volume_eq_gaussian {n : ℕ}
    (D : Finset (Fin (n + 2) × Fin (n + 2)))
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) (r : ℝ) (hr : 0 ≤ r) :
    (∫ y : Fin (n + 1) → ℝ in Metric.closedBall 0 (r / 2),
      normalizedRegularPhysicalIntegrand D (Fin.snoc y 0)) /
        (quotientGaussianVolume (n + 2) : ℂ) =
      ∫ x : Fin (n + 2) → ℝ in gaussianCentralWindow (Fin.last (n + 1)) r,
        scaledRegularFactor D x ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  let S : Set (Fin (n + 1) → ℝ) := Metric.closedBall 0 (r / 2)
  let F : (Fin (n + 1) → ℝ) → ℂ := S.indicator (anchoredRegularFactor D)
  have hS : MeasurableSet S := Metric.isClosed_closedBall.measurableSet
  have hc := continuous_anchoredRegularFactor D hD
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin (n + 1) → ℝ) (r / 2)).exists_bound_of_continuousOn
    hc.continuousOn
  have hb (y : Fin (n + 1) → ℝ) : ‖F y‖ ≤ max C 0 := by
    by_cases hy : y ∈ S
    · have hh : ‖F y‖ ≤ C := by simpa only [F, Set.indicator_of_mem hy] using hC y hy
      exact hh.trans (le_max_left _ _)
    · simp only [F, Set.indicator_of_notMem hy, norm_zero]
      exact le_max_right _ _
  have hmeas : StronglyMeasurable (fun x : Fin (n + 2) → ℝ => F (scaledAnchorDifference x)) :=
    ((hc.measurable.indicator hS).comp (by
      unfold scaledAnchorDifference anchorDifference
      fun_prop)).stronglyMeasurable
  have hi : Integrable (fun x : Fin (n + 2) → ℝ => F (scaledAnchorDifference x))
      (Measure.pi (fun _ => gaussianReal 0 1)) :=
    (integrable_const (max C 0 : ℝ)).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hb _)
  have ht := integral_standardNormalProduct_scaledAnchorDifference F hi
  have hleft (x : Fin (n + 2) → ℝ) : F (scaledAnchorDifference x) =
      (gaussianCentralWindow (Fin.last (n + 1)) r).indicator (scaledRegularFactor D) x := by
    by_cases hx : x ∈ gaussianCentralWindow (Fin.last (n + 1)) r
    · have hy := (scaledAnchorDifference_mem_closedBall r hr x).mpr hx
      simp only [F, S, Set.indicator_of_mem hx, Set.indicator_of_mem hy,
        anchoredRegularFactor_scaledAnchorDifference D hD]
    · have hy : scaledAnchorDifference x ∉ S :=
        fun hy => hx ((scaledAnchorDifference_mem_closedBall r hr x).mp hy)
      simp only [F, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  have hright (y : Fin (n + 1) → ℝ) :
      matrixGaussian (completeQuotientPrecision n) y • F y =
        S.indicator (fun y => normalizedRegularPhysicalIntegrand D (Fin.snoc y 0)) y := by
    by_cases hy : y ∈ S
    · simp only [F, Set.indicator_of_mem hy, anchoredRegularFactor,
        matrixGaussian_completeQuotientPrecision_energy, Complex.real_smul]
      rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      simp only [neg_div, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]
    · simp only [F, Set.indicator_of_notMem hy, smul_zero]
  simp_rw [hleft, hright] at ht
  rw [integral_indicator (measurableSet_gaussianCentralWindow _ _), integral_indicator hS] at ht
  simpa only [S, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using ht.symm

end
end Wormald.FiniteModel
