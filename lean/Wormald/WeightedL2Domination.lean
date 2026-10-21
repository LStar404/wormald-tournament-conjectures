import Wormald.WeightedL2SetBound

namespace Wormald
noncomputable section
open MeasureTheory Filter

theorem integral_norm_le_sqrt_L2 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {w : Ω → ℂ} (hw : MemLp w 2 μ) :
    (∫ x, ‖w x‖ ∂μ) ≤ Real.sqrt (∫ x, ‖w x‖ ^ 2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hw.norm)
    (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_one, mul_one,
    Real.rpow_two, one_pow, integral_const, probReal_univ, smul_eq_mul, one_mul,
    ← Real.sqrt_eq_rpow, Real.sqrt_one] using h

/-- A local pointwise error bounded by K times an L² weight has an
integrable restriction and a uniform integral bound. -/
theorem norm_setIntegral_le_mul_sqrt_L2 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {w f : Ω → ℂ}
    (hw : MemLp w 2 μ) (hf : AEStronglyMeasurable f μ)
    {A : Set Ω} (hA : MeasurableSet A) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ x ∈ A, ‖f x‖ ≤ K * ‖w x‖) :
    ‖∫ x in A, f x ∂μ‖ ≤ K * Real.sqrt (∫ x, ‖w x‖ ^ 2 ∂μ) := by
  have hdom : ∀ x, ‖A.indicator f x‖ ≤ K * ‖w x‖ := by
    intro x
    by_cases hx : x ∈ A
    · simpa only [Set.indicator_of_mem hx] using hbound x hx
    · simp only [Set.indicator_of_notMem hx, norm_zero]
      exact mul_nonneg hK (norm_nonneg _)
  have hdomInt : Integrable (fun x => K * ‖w x‖) μ :=
    (hw.norm.integrable (by norm_num)).const_mul K
  have hfInt : Integrable (A.indicator f) μ :=
    hdomInt.mono' (hf.indicator hA) (Eventually.of_forall hdom)
  rw [← integral_indicator hA]
  calc
    _ ≤ ∫ x, ‖A.indicator f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, K * ‖w x‖ ∂μ := integral_mono_ae hfInt.norm hdomInt (Eventually.of_forall hdom)
    _ = K * ∫ x, ‖w x‖ ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_norm_le_sqrt_L2 hw) hK

end
end Wormald
