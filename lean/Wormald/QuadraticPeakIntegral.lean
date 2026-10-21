import Wormald.QuadraticScaling
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! A local complex Laplace integral proved by Gaussian rescaling and dominated
convergence. Its hypotheses describe local Taylor data and a quadratic bound;
they do not assume a counting limit or an integral asymptotic. -/

namespace Wormald
noncomputable section
open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def localComplexPeak (phase : E → ℂ) (δ : ℝ) (m : ℕ) (x : E) : ℂ :=
  if ‖x‖ < δ then Complex.exp ((m : ℂ) * phase x) else 0

omit [NormedSpace ℝ E] in
theorem measurable_localComplexPeak [MeasurableSpace E] [BorelSpace E]
    (phase : E → ℂ) (hphase : Measurable phase)
    (δ : ℝ) (m : ℕ) : Measurable (localComplexPeak phase δ m) := by
  exact Measurable.ite (isOpen_lt continuous_norm continuous_const).measurableSet
    (Complex.continuous_exp.measurable.comp (measurable_const.mul hphase)) measurable_const

omit [NormedSpace ℝ E] in
theorem measurable_localComplexPeak_of_continuousOn [MeasurableSpace E] [BorelSpace E]
    (phase : E → ℂ) (δ : ℝ) (hphase : ContinuousOn phase {x | ‖x‖ < δ})
    (m : ℕ) : Measurable (localComplexPeak phase δ m) := by
  exact (continuousOn_const.mul hphase).cexp.measurable_piecewise continuousOn_const
    (isOpen_lt continuous_norm continuous_const).measurableSet

theorem tendsto_rescaled_localComplexPeak (phase : E → ℂ) (Q : E → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hpoint : ∀ x, Tendsto (fun m : ℕ => (m : ℂ) *
      phase ((Real.sqrt (m : ℝ))⁻¹ • x)) atTop (𝓝 (-(Q x : ℂ)))) (x : E) :
    Tendsto (fun m : ℕ => localComplexPeak phase δ m
      ((Real.sqrt (m : ℝ))⁻¹ • x)) atTop (𝓝 (Complex.exp (-(Q x : ℂ)))) := by
  have hx := tendsto_invSqrt_smul x
  have hball : ∀ᶠ m : ℕ in atTop, ‖(Real.sqrt (m : ℝ))⁻¹ • x‖ < δ :=
    (hx.norm.eventually (gt_mem_nhds (by simpa using hδ)))
  apply (Complex.continuous_exp.tendsto _ |>.comp (hpoint x)).congr'
  filter_upwards [hball] with m hm
  simp only [localComplexPeak, ite_eq_left hm, Function.comp_apply]

theorem norm_rescaled_localComplexPeak_le (phase : E → ℂ) (δ c : ℝ)
    (hbound : ∀ y, ‖y‖ < δ → (phase y).re ≤ -c * ‖y‖ ^ 2)
    (m : ℕ) (hm : 0 < m) (x : E) :
    ‖localComplexPeak phase δ m ((Real.sqrt (m : ℝ))⁻¹ • x)‖ ≤
      Real.exp (-c * ‖x‖ ^ 2) := by
  unfold localComplexPeak
  split_ifs with hx
  · rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (hbound _ hx) (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    have he := nat_mul_norm_invSqrt_smul_sq m hm x
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    calc
      _ ≤ (m : ℝ) * (-c * ‖(Real.sqrt (m : ℝ))⁻¹ • x‖ ^ 2) := h
      _ = -c * ((m : ℝ) * ‖(Real.sqrt (m : ℝ))⁻¹ • x‖ ^ 2) := by ring
      _ = _ := by rw [he]
  · simpa only [norm_zero] using (Real.exp_pos (-c * ‖x‖ ^ 2)).le

/-- The precise local Laplace limit. The Gaussian domination is established
pointwise before the dominated-convergence theorem is applied. -/
theorem tendsto_localComplexPeak_integral (phase : E → ℂ) (Q : E → ℝ)
    [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    (δ c : ℝ) (hδ : 0 < δ) (hphase : ContinuousOn phase {x | ‖x‖ < δ})
    (hpoint : ∀ x, Tendsto (fun m : ℕ => (m : ℂ) *
      phase ((Real.sqrt (m : ℝ))⁻¹ • x)) atTop (𝓝 (-(Q x : ℂ))))
    (hbound : ∀ y, ‖y‖ < δ → (phase y).re ≤ -c * ‖y‖ ^ 2)
    (hgauss : Integrable (fun x : E => Real.exp (-c * ‖x‖ ^ 2))) :
    Tendsto (fun m : ℕ => (Real.sqrt (m : ℝ)) ^ Module.finrank ℝ E •
      ∫ y : E, localComplexPeak phase δ m y) atTop
        (𝓝 (∫ x : E, Complex.exp (-(Q x : ℂ)))) := by
  have hmeas : ∀ m : ℕ, AEStronglyMeasurable
      (fun x : E => localComplexPeak phase δ m ((Real.sqrt (m : ℝ))⁻¹ • x)) := by
    intro m
    exact ((measurable_localComplexPeak_of_continuousOn phase δ hphase m).comp
      (measurable_const.smul measurable_id)).aestronglyMeasurable
  have hb : ∀ᶠ m : ℕ in atTop, ∀ᵐ x : E,
      ‖localComplexPeak phase δ m ((Real.sqrt (m : ℝ))⁻¹ • x)‖ ≤
        Real.exp (-c * ‖x‖ ^ 2) := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    exact ae_of_all _ (norm_rescaled_localComplexPeak_le phase δ c hbound m hm)
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (fun x : E => Real.exp (-c * ‖x‖ ^ 2)) (Eventually.of_forall hmeas) hb hgauss
    (ae_of_all _ (tendsto_rescaled_localComplexPeak phase Q δ hδ hpoint))
  simpa only [Measure.integral_comp_inv_smul_of_nonneg volume _ (Real.sqrt_nonneg _)] using hlim

end
end Wormald
