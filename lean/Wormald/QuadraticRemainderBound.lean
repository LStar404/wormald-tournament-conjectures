import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact

/-! A positive homogeneous quadratic form has a uniform positive lower bound,
and a vanishing complex quadratic remainder preserves local Gaussian decay. -/

namespace Wormald
noncomputable section
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_pos_mul_norm_sq_le (Q : E → ℝ) (hcont : Continuous Q)
    (hhom : ∀ (a : ℝ) x, Q (a • x) = a ^ 2 * Q x)
    (hpos : ∀ x, x ≠ 0 → 0 < Q x) :
    ∃ a : ℝ, 0 < a ∧ ∀ x, a * ‖x‖ ^ 2 ≤ Q x := by
  have hzero : Q 0 = 0 := by simpa using hhom 0 0
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨1, by norm_num, fun x => by simp [Subsingleton.elim x 0, hzero]⟩
  · have hK : IsCompact {x : E | ‖x‖ = 1} := by
      simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : E) 1
    obtain ⟨w, hw⟩ := exists_norm_eq E (by norm_num : (0 : ℝ) ≤ 1)
    obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn ⟨w, hw⟩ hcont.continuousOn
    have hzne : z ≠ 0 := by intro h; simp [h] at hz
    refine ⟨Q z, hpos z hzne, ?_⟩
    intro x
    by_cases hx : x = 0
    · simp [hx, hzero]
    · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hy : ‖(‖x‖)⁻¹ • x‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
          inv_mul_cancel₀ hn]
      have h := (isMinOn_iff.mp hmin) ((‖x‖)⁻¹ • x) hy
      rw [hhom] at h
      have hh := mul_le_mul_of_nonneg_left h (sq_nonneg ‖x‖)
      have he : ‖x‖ ^ 2 * ((‖x‖)⁻¹ ^ 2 * Q x) = Q x := by
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hn, one_pow, one_mul]
      rw [he] at hh
      simpa only [mul_comm] using hh

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem eventually_re_le_neg_norm_sq (phase : E → ℂ) (Q : E → ℝ) (err : E → ℂ)
    (a : ℝ) (ha : 0 < a) (hQ : ∀ y, a * ‖y‖ ^ 2 ≤ Q y)
    (herr : Tendsto err (𝓝 0) (𝓝 0))
    (hphase : ∀ᶠ y in 𝓝 0, phase y = -(Q y : ℂ) + (‖y‖ ^ 2 : ℝ) * err y) :
    ∀ᶠ y in 𝓝 0, (phase y).re ≤ -(a / 2) * ‖y‖ ^ 2 := by
  have he : ∀ᶠ y in 𝓝 (0 : E), ‖err y‖ < a / 2 :=
    herr.norm.eventually (gt_mem_nhds (by simpa using half_pos ha))
  filter_upwards [he, hphase] with y hy hpy
  have hre : (err y).re ≤ a / 2 := (Complex.re_le_norm _).trans hy.le
  have hmul := mul_le_mul_of_nonneg_left hre (sq_nonneg ‖y‖)
  rw [hpy]
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  nlinarith [hQ y]

end
end Wormald
