import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! A uniform Cauchy--Schwarz estimate for a common real correction factor
against complex weights. Both the underlying space and its dimension may vary. -/

namespace Wormald
noncomputable section
open MeasureTheory Filter Topology

theorem norm_integral_mul_real_le_sqrt {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {w : Ω → ℂ} {e : Ω → ℝ}
    (hw : MemLp w 2 μ) (he : MemLp e 2 μ) :
    ‖∫ x, w x * (e x : ℂ) ∂μ‖ ≤
      Real.sqrt (∫ x, ‖w x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, e x ^ 2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hw.norm) (by simpa using he)
  have h' : (∫ x, ‖w x‖ * |e x| ∂μ) ≤
      Real.sqrt (∫ x, ‖w x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, e x ^ 2 ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Real.rpow_two,
      sq_abs, ← Real.sqrt_eq_rpow] using h
  calc
    _ ≤ ∫ x, ‖w x * (e x : ℂ)‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖w x‖ * |e x| ∂μ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ _ := h'

/-- The error tends to zero uniformly over every choice of weights with the
same L² bound; no compatibility between successive spaces is required. -/
theorem tendsto_integral_mul_real_of_L2 {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : (n : ℕ) → Measure (Ω n))
    (w : (n : ℕ) → Ω n → ℂ) (e : (n : ℕ) → Ω n → ℝ)
    (hw : ∀ᶠ n in atTop, MemLp (w n) 2 (μ n))
    (he : ∀ᶠ n in atTop, MemLp (e n) 2 (μ n))
    (C : ℝ) (hC : ∀ᶠ n in atTop, (∫ x, ‖w n x‖ ^ 2 ∂μ n) ≤ C)
    (he0 : Tendsto (fun n => ∫ x, e n x ^ 2 ∂μ n) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, w n x * (e n x : ℂ) ∂μ n) atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  have hlim : Tendsto (fun n => Real.sqrt C * Real.sqrt (∫ x, e n x ^ 2 ∂μ n))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero, Function.comp_apply] using
      (tendsto_const_nhds (x := Real.sqrt C)).mul
        (Real.continuous_sqrt.tendsto 0 |>.comp he0)
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    hlim
  filter_upwards [hw, he, hC] with n hwn hen hCn
  exact (norm_integral_mul_real_le_sqrt hwn hen).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hCn) (Real.sqrt_nonneg _))

end
end Wormald
