import Wormald.UniformRegularFourierReduction
import Wormald.RegularCentralGaussianTransport
import Wormald.RegularCentralMainTerm
import Wormald.RegularNoncentralTail
import Wormald.AnchoredRegularWindow

/-! Assembly of the uniform growing-dimensional regular-tournament
Fourier estimate from the actual central integral and the actual tails. -/

namespace Wormald
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

theorem norm_integral_div_sub_le_central_add_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (f : Ω → ℂ)
    (hf : Integrable f μ) (A : Set Ω) (hA : MeasurableSet A)
    (v : ℝ) (hv : 0 < v) (c : ℂ) :
    ‖(∫ x, f x ∂μ) / (v : ℂ) - c‖ ≤
      ‖(∫ x in A, f x ∂μ) / (v : ℂ) - c‖ +
        (∫ x in Aᶜ, ‖f x‖ ∂μ) / v := by
  have he : (∫ x, f x ∂μ) / (v : ℂ) - c =
      ((∫ x in A, f x ∂μ) / (v : ℂ) - c) +
        (∫ x in Aᶜ, f x ∂μ) / (v : ℂ) := by
    rw [← integral_add_compl hA hf]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]
  exact div_le_div_of_nonneg_right (norm_integral_le_integral_norm _) hv.le

namespace FiniteModel

local instance finalRegularCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance finalRegularCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem norm_regularTorusMainTerm_error_le_succ {n : ℕ} (hmLarge : 256 ≤ n + 2)
    (D : Finset (Fin (n + 2) × Fin (n + 2))) (hm : Odd (n + 2))
    (hD : LegalPartialPermutationArcs D) (herror : centralGaussianError (n + 2) ≤ 1) :
    ‖normalizedRegularTorusIntegral D / (regularGaussianTorusVolume (n + 2) : ℂ) -
      ((Real.exp (-(1 / 2 : ℝ)) *
        Real.exp ((internalInOutCount D : ℝ) / (n + 2 : ℕ)) : ℝ) : ℂ)‖ ≤
      centralMainError (n + 2) + regularNoncentralError (n + 2) := by
  let r := centralGaussianRadius (n + 2)
  let A := circleAnchorWindow (Fin.last (n + 1)) (r / (2 * Real.pi))
  have hr : 0 ≤ r := centralGaussianRadius_nonneg _
  have hrpi : r < Real.pi :=
    (centralGaussianRadius_le_one (by omega)).trans_lt (by linarith [Real.two_le_pi])
  have hcentral :
      ‖(∫ x : UnitAddTorus (Fin (n + 2)) in A, normalizedRegularTorusIntegrand D x) /
          (physicalGaussianQuotientVolume (n + 2) : ℂ) -
        ((Real.exp (-(1 / 2 : ℝ)) *
          Real.exp ((internalInOutCount D : ℝ) / (n + 2 : ℕ)) : ℝ) : ℂ)‖ ≤
        centralMainError (n + 2) := by
    rw [show A = circleAnchorWindow (Fin.last (n + 1)) (r / (2 * Real.pi)) from rfl,
      integral_circleAnchorWindow_div_volume_eq_physical D hm r hr hrpi,
      physicalCentralIntegral_div_volume_eq_gaussian D hD.2.2.2 r hr]
    simpa only [r, Complex.ofReal_mul] using
      norm_gaussianCentralMainTerm_error_le (by omega) D hD.2.2.2 hD.1 hD.2.1 hD.2.2.1
        herror (Fin.last (n + 1))
  have htail := integral_regularNoncentral_norm_div_volume_le hmLarge D hm hD.2.2.2
    hD.2.1 hD.2.2.1 (Fin.last (n + 1)) (by simp)
  have hf : Integrable (normalizedRegularTorusIntegrand D) :=
    (continuous_normalizedRegularTorusIntegrand D).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsplit := norm_integral_div_sub_le_central_add_tail
    (normalizedRegularTorusIntegrand D) hf A (measurableSet_circleAnchorWindow _ _)
    (physicalGaussianQuotientVolume (n + 2)) (physicalGaussianQuotientVolume_pos (by omega))
    (((Real.exp (-(1 / 2 : ℝ)) *
      Real.exp ((internalInOutCount D : ℝ) / (n + 2 : ℕ)) : ℝ) : ℂ))
  change ‖(∫ x : UnitAddTorus (Fin (n + 2)), normalizedRegularTorusIntegrand D x) /
    (physicalGaussianQuotientVolume (n + 2) : ℂ) - _‖ ≤ _
  exact hsplit.trans (add_le_add hcentral htail)

theorem norm_regularTorusMainTerm_error_le {m : ℕ} (hmLarge : 256 ≤ m)
    (D : Finset (Fin m × Fin m)) (hm : Odd m)
    (hD : LegalPartialPermutationArcs D) (herror : centralGaussianError m ≤ 1) :
    ‖normalizedRegularTorusIntegral D / (regularGaussianTorusVolume m : ℂ) -
      ((Real.exp (-(1 / 2 : ℝ)) *
        Real.exp ((internalInOutCount D : ℝ) / (m : ℝ)) : ℝ) : ℂ)‖ ≤
      centralMainError m + regularNoncentralError m := by
  rcases m with _ | m
  · omega
  rcases m with _ | n
  · omega
  exact norm_regularTorusMainTerm_error_le_succ hmLarge D hm hD herror

/-- The full uniform integral main term, with no analytic or counting
hypotheses left over. The radius, all tails, and all growing-dimensional
Gaussian approximations have been proved for the actual finite model. -/
theorem uniformRegularTorusMainTerm : UniformRegularTorusMainTerm := by
  have hodd : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => show k ≤ 2 * k + 1 by omega) tendsto_id
  refine ⟨fun k => centralMainError (2 * k + 1) + regularNoncentralError (2 * k + 1), ?_,
    fun k => add_nonneg (centralMainError_nonneg _) (regularNoncentralError_nonneg _), ?_⟩
  · simpa only [Function.comp_def, add_zero] using
      (tendsto_centralMainError.add tendsto_regularNoncentralError).comp hodd
  have hsmall := (tendsto_centralGaussianError.comp hodd).eventually_lt_const
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hsmall, eventually_ge_atTop 128] with k hk hkLarge D hD
  exact norm_regularTorusMainTerm_error_le (by omega) D ⟨k, rfl⟩ hD hk.le

end FiniteModel

end
end Wormald
