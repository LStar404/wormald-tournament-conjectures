import Mathlib.Tactic

/-! Scalar consequences of differentiating ψ(t',g(t'))=0 twice.
The hypotheses are the actual chain-rule equations, not a declaration that the
desired Hessian identity holds. The analytic derivation of these hypotheses
from Wormald's determinant is not yet formalized. -/

namespace Wormald

theorem implicit_first (d a : ℚ) (hd : d ≠ 0)
    (chain : 0 = -1 / d + (-1 / d) * a) : a = -1 := by
  field_simp at chain
  nlinarith

/-- Five terms in the second implicit chain rule; the angular substitution
contributes the minus sign in the conclusion. -/
theorem implicit_angular_second (d qjk qjp qpk qpp a b c : ℚ)
    (hd : d ≠ 0)
    (first_j : 0 = -1 / d + (-1 / d) * a)
    (first_k : 0 = -1 / d + (-1 / d) * b)
    (second : 0 = -qjk / d + (-qjp / d) * b + (-qpk / d) * a +
      (-qpp / d) * a * b + (-1 / d) * c) :
    -c = qjk - qjp - qpk + qpp := by
  have ha := implicit_first d a hd first_j
  have hb := implicit_first d b hd first_k
  subst a
  subst b
  field_simp at second
  nlinarith

end Wormald
