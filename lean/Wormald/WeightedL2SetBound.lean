import Wormald.WeightedL2Cancellation

/-! Small-set errors under a genuine measure. The L² estimate retains the
square root of the exceptional probability, uniformly in the dimension. -/

namespace Wormald
noncomputable section
open MeasureTheory Filter

theorem norm_setIntegral_le_sqrt_L2 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {w : Ω → ℂ}
    (hw : MemLp w 2 μ) (A : Set Ω) :
    ‖∫ x in A, w x ∂μ‖ ≤
      Real.sqrt (∫ x, ‖w x‖ ^ 2 ∂μ) * Real.sqrt (μ.real A) := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using (hw.restrict A).norm)
    (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 (μ.restrict A)))
  have h' : (∫ x in A, ‖w x‖ ∂μ) ≤
      Real.sqrt (∫ x in A, ‖w x‖ ^ 2 ∂μ) * Real.sqrt (μ.real A) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_one, mul_one,
      Real.rpow_two, one_pow, integral_const, smul_eq_mul, mul_one,
      measureReal_def, Measure.restrict_apply_univ, ← Real.sqrt_eq_rpow] using h
  have hsq : (∫ x in A, ‖w x‖ ^ 2 ∂μ) ≤ ∫ x, ‖w x‖ ^ 2 ∂μ :=
    integral_mono_measure μ.restrict_le_self (Eventually.of_forall fun _ => sq_nonneg _)
      ((memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).mp hw)
  exact (norm_integral_le_integral_norm _).trans (h'.trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsq) (Real.sqrt_nonneg _)))

end
end Wormald
