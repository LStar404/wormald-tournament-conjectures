import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# The exact limit of the closed carousel expression

This proves the analytic limit in Part I, Section 10, for precisely the
closed expression in Section 9. Identifying this expression with the
carousel determinant and with random-model expectations is a separate
formalization obligation. No assertion about a Hamilton extremum is made.
-/

open Filter Topology

namespace Wormald

noncomputable section

/-- The manuscript's closed formula, considered as a complex-valued
sequence. Only its odd indices at least three represent carousel bases. -/
def carouselClosedConstant (d : ℕ) : ℂ :=
  Complex.exp (1 / (d : ℂ)) *
    (((1 + 1 / (d : ℂ)) ^ d + (1 - 1 / (d : ℂ)) ^ d) /
      ((1 + Complex.I / (d : ℂ)) ^ d + (1 - Complex.I / (d : ℂ)) ^ d))

private theorem exp_I_add_exp_neg_I :
    Complex.exp Complex.I + Complex.exp (-Complex.I) =
      2 * (Real.cos 1 : ℂ) := by
  rw [Complex.ofReal_cos]
  norm_num [Complex.cos]
  ring

private theorem exp_I_add_exp_neg_I_ne_zero :
    Complex.exp Complex.I + Complex.exp (-Complex.I) ≠ 0 := by
  rw [exp_I_add_exp_neg_I]
  apply mul_ne_zero (by norm_num)
  exact_mod_cast (ne_of_gt Real.cos_one_pos)

private theorem carousel_limit_value :
    (Complex.exp 1 + Complex.exp (-1)) /
      (Complex.exp Complex.I + Complex.exp (-Complex.I)) =
      ((Real.cosh 1 / Real.cos 1 : ℝ) : ℂ) := by
  rw [Complex.ofReal_div, Complex.ofReal_cosh, Complex.ofReal_cos]
  norm_num only [Complex.ofReal_one]
  simp only [Complex.cosh, Complex.cos, one_mul, neg_one_mul]
  rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℂ) ≠ 0)]

/-- The full closed sequence converges; in particular its odd subsequence
converges to the exact constant asserted in the manuscript. -/
theorem tendsto_carouselClosedConstant :
    Tendsto carouselClosedConstant atTop
      (𝓝 ((Real.cosh 1 / Real.cos 1 : ℝ) : ℂ)) := by
  have hinvR : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (1 : ℂ) / (n : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, one_div] using (Complex.continuous_ofReal.tendsto 0).comp hinvR
  have hexp : Tendsto (fun n : ℕ => Complex.exp (1 / (n : ℂ))) atTop (𝓝 1) := by
    simpa [Function.comp_def] using (Complex.continuous_exp.tendsto 0).comp hinv
  have hnum := (Complex.tendsto_one_add_div_pow_exp 1).add
    (Complex.tendsto_one_add_div_pow_exp (-1))
  have hden := (Complex.tendsto_one_add_div_pow_exp Complex.I).add
    (Complex.tendsto_one_add_div_pow_exp (-Complex.I))
  have hlim := hexp.mul (hnum.div hden exp_I_add_exp_neg_I_ne_zero)
  change Tendsto (fun d : ℕ => carouselClosedConstant d) atTop _
  simpa [carouselClosedConstant, neg_div, sub_eq_add_neg, carousel_limit_value] using hlim

/-- The actual carousel orders are exactly `2*k+3`; the same exact limit
holds along these orders. -/
theorem tendsto_carouselClosedConstant_odd :
    Tendsto (fun k : ℕ => carouselClosedConstant (2 * k + 3)) atTop
      (𝓝 ((Real.cosh 1 / Real.cos 1 : ℝ) : ℂ)) := by
  apply tendsto_carouselClosedConstant.comp
  apply Filter.tendsto_atTop_mono (fun k : ℕ => show k ≤ 2 * k + 3 by omega)
  exact tendsto_id

#print axioms tendsto_carouselClosedConstant
#print axioms tendsto_carouselClosedConstant_odd

end

end Wormald
