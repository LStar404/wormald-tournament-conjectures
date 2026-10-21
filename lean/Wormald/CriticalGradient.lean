import Wormald.JetToCandidate

/-!
# The actual nonzero rational gradient at the critical point

These facts discharge the finite hypotheses of the analytic implicit-function
calculation. They refer to the original defining polynomial, not to a replacement
function with a Hessian prescribed by definition.
-/

namespace Wormald

noncomputable section
open MvPolynomial

theorem eval_first_pderiv_critical_rat {d : ℕ} (T : Tournament d)
    (hT : T.Regular) (hd : d ≠ 0) (j : Fin d) :
    eval (fun _ => 2 / (d : ℚ)) (pderiv j (definingPolynomial T.adjacency)) =
      -(1 - T.normalizedSign).det / 2 := by
  apply Rat.cast_injective (α := ℂ)
  rw [ratCast_eval_complex]
  simp only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_natCast]
  rw [eval_first_pderiv_critical T hT hd j, T.criticalDet_eq_ratCast]

theorem eval_first_pderiv_critical_uniform {d : ℕ} (T : Tournament d)
    (hT : T.Regular) (hd : d ≠ 0) (j k : Fin d) :
    eval (fun _ => 2 / (d : ℚ)) (pderiv j (definingPolynomial T.adjacency)) =
      eval (fun _ => 2 / (d : ℚ)) (pderiv k (definingPolynomial T.adjacency)) := by
  rw [eval_first_pderiv_critical_rat T hT hd j,
    eval_first_pderiv_critical_rat T hT hd k]

theorem eval_first_pderiv_critical_ne_zero {d : ℕ} (T : Tournament d)
    (hT : T.Regular) (hd : d ≠ 0) (j : Fin d) :
    eval (fun _ => 2 / (d : ℚ)) (pderiv j (definingPolynomial T.adjacency)) ≠ 0 := by
  rw [eval_first_pderiv_critical_rat T hT hd j]
  exact div_ne_zero (neg_ne_zero.mpr
    (det_one_sub_rational_skew_ne_zero T.normalizedSign T.normalizedSign_skew))
    (by norm_num)

end
end Wormald
