import Wormald.Definitions
import Wormald.Positivity

/-! The positivity estimates specialized to the actual signed tournament matrix.
Regularity is unnecessary for this estimate; it is needed elsewhere to identify
the Hessian and its constant direction. -/

open Matrix
open scoped BigOperators

namespace Wormald

noncomputable def Tournament.realNormalizedSign {n : ℕ} (T : Tournament n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (T.normalizedSign i j : ℝ)

theorem Tournament.realNormalizedSign_skew {n : ℕ} (T : Tournament n) :
    T.realNormalizedSign.transpose = -T.realNormalizedSign := by
  have hs : T.normalizedSign.transpose = -T.normalizedSign := by
    ext i j
    change T.sign j i / (n : ℚ) = -(T.sign i j / (n : ℚ))
    have hij : T.sign j i = -T.sign i j := congrFun (congrFun T.sign_skew i) j
    rw [hij, neg_div]
  ext i j
  change (T.normalizedSign j i : ℝ) = -(T.normalizedSign i j : ℝ)
  exact_mod_cast congrFun (congrFun hs i) j

theorem Tournament.realNormalizedSign_energy {n : ℕ} (T : Tournament n)
    (hn : n ≠ 0) :
    (∑ i, ∑ j, T.realNormalizedSign i j ^ 2) = ((n : ℝ) - 1) / (n : ℝ) := by
  change (∑ i, ∑ j, (T.normalizedSign i j : ℝ) ^ 2) = ((n : ℝ) - 1) / (n : ℝ)
  exact_mod_cast T.normalizedSign_energy hn

theorem Tournament.realNormalizedSign_energy_lt_one {n : ℕ} (T : Tournament n)
    (hn : n ≠ 0) :
    (∑ i, ∑ j, T.realNormalizedSign i j ^ 2) < 1 := by
  rw [T.realNormalizedSign_energy hn]
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  apply (div_lt_one hnR).mpr
  linarith

/-- Positivity now follows for the normalized sign matrix of every nonempty
finite tournament; this no longer assumes a spectral or norm bound. -/
theorem Tournament.posDef_one_add_realNormalizedSign_square {n : ℕ}
    (T : Tournament n) (hn : n ≠ 0) :
    (1 + T.realNormalizedSign * T.realNormalizedSign).PosDef :=
  posDef_one_add_square_of_frobenius T.realNormalizedSign
    T.realNormalizedSign_skew (T.realNormalizedSign_energy_lt_one hn)

/-- The exact rational core is positive for an actual tournament matrix.
Inverse equations are explicit; correspondence with the analytic Hessian is a
separate obligation. -/
theorem Tournament.posDef_realNormalizedSign_resolvent {n : ℕ}
    (T : Tournament n) (hn : n ≠ 0)
    (U V W : Matrix (Fin n) (Fin n) ℝ)
    (hU : U * (1 - T.realNormalizedSign) = 1)
    (hUr : (1 - T.realNormalizedSign) * U = 1)
    (hV : V * (1 + T.realNormalizedSign) = 1)
    (hVr : (1 + T.realNormalizedSign) * V = 1)
    (hW : (1 - T.realNormalizedSign * T.realNormalizedSign) * W = 1) :
    ((1 + T.realNormalizedSign * T.realNormalizedSign) * W).PosDef :=
  posDef_resolvent_of_frobenius T.realNormalizedSign U V W
    T.realNormalizedSign_skew (T.realNormalizedSign_energy_lt_one hn)
    hU hUr hV hVr hW

/-- Unconditional finite positivity for the actual normalized tournament matrix.
The analytic Hessian identification remains a distinct theorem to establish. -/
theorem Tournament.posDef_realNormalizedSign_core {n : ℕ}
    (T : Tournament n) (hn : n ≠ 0) :
    ((1 + T.realNormalizedSign * T.realNormalizedSign) *
      (1 - T.realNormalizedSign * T.realNormalizedSign)⁻¹).PosDef :=
  posDef_resolvent T.realNormalizedSign T.realNormalizedSign_skew
    (T.realNormalizedSign_energy_lt_one hn)

end Wormald

