import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Wormald.MatrixCore

/-! Positivity for the finite matrix expression in Part I, Sections 2 and 7.
The Euclidean squared norm is written as a dot product, so no choice of
norm on the function type is implicit. -/

open Matrix
open scoped BigOperators

namespace Wormald

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The skew square has quadratic form `-‖Cx‖₂²`. -/
theorem skew_square_quadratic (C : Matrix n n ℝ) (hC : C.transpose = -C)
    (x : n → ℝ) :
    x ⬝ᵥ ((C * C) *ᵥ x) = -((C *ᵥ x) ⬝ᵥ (C *ᵥ x)) := by
  have hvec : x ᵥ* C = -(C *ᵥ x) := by
    rw [← Matrix.mulVec_transpose, hC, Matrix.neg_mulVec]
  rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, hvec, neg_dotProduct]

/-- Strict Euclidean contraction makes `I+C²` positive definite. -/
theorem posDef_one_add_square_of_contraction (C : Matrix n n ℝ)
    (hC : C.transpose = -C)
    (hcontract : ∀ x : n → ℝ, x ≠ 0 →
      (C *ᵥ x) ⬝ᵥ (C *ᵥ x) < x ⬝ᵥ x) :
    (1 + C * C).PosDef := by
  have hsym : (1 + C * C).IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    change (1 + C * C).transpose = 1 + C * C
    simp [Matrix.transpose_mul, hC]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hsym
  intro x hx
  simp only [star_trivial, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add]
  rw [skew_square_quadratic C hC x]
  exact sub_pos.mpr (hcontract x hx)

omit [DecidableEq n] in
/-- Cauchy–Schwarz bounds the Euclidean operator square by the entry-square sum. -/
theorem mulVec_square_le_frobenius (C : Matrix n n ℝ) (x : n → ℝ) :
    (C *ᵥ x) ⬝ᵥ (C *ᵥ x) ≤
      (∑ i, ∑ j, C i j ^ 2) * (x ⬝ᵥ x) := by
  calc
    (C *ᵥ x) ⬝ᵥ (C *ᵥ x) = ∑ i, (∑ j, C i j * x j) ^ 2 := by
      simp [dotProduct, Matrix.mulVec, pow_two]
    _ ≤ ∑ i, (∑ j, C i j ^ 2) * (∑ j, x j ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (C i) x
    _ = (∑ i, ∑ j, C i j ^ 2) * (x ⬝ᵥ x) := by
      rw [Finset.sum_mul]
      simp only [dotProduct, pow_two]

/-- The simple Frobenius bound below one already suffices for positivity. -/
theorem posDef_one_add_square_of_frobenius (C : Matrix n n ℝ)
    (hC : C.transpose = -C) (hF : (∑ i, ∑ j, C i j ^ 2) < 1) :
    (1 + C * C).PosDef := by
  apply posDef_one_add_square_of_contraction C hC
  intro x hx
  have hxpos : 0 < x ⬝ᵥ x := by
    have hnonneg : 0 ≤ x ⬝ᵥ x := by
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
    exact lt_of_le_of_ne hnonneg (Ne.symm (fun hz => hx (dotProduct_self_eq_zero.mp hz)))
  exact (mulVec_square_le_frobenius C x).trans_lt (by nlinarith)

/-- The rational core is a congruence of `I+C²` by the inverse of `I-C`.
The displayed equations expose every inverse used in the argument. -/
theorem resolvent_eq_congruence (C U V W : Matrix n n ℝ)
    (hC : C.transpose = -C)
    (hU : U * (1 - C) = 1) (hUr : (1 - C) * U = 1)
    (hV : V * (1 + C) = 1) (hVr : (1 + C) * V = 1)
    (hW : (1 - C * C) * W = 1) :
    (1 + C * C) * W = U.transpose * (1 + C * C) * U := by
  have hUT : U.transpose = V := by
    have ht : (1 + C) * U.transpose = 1 := by
      simpa [Matrix.transpose_mul, hC] using congrArg Matrix.transpose hU
    calc
      U.transpose = (V * (1 + C)) * U.transpose := by rw [hV, one_mul]
      _ = V := by rw [mul_assoc, ht, mul_one]
  have hCU : C * U = U - 1 := by
    apply eq_sub_iff_add_eq.mpr
    have hh : U - C * U = 1 := by simpa [sub_mul] using hUr
    simpa [add_comm] using (sub_eq_iff_eq_add.mp hh).symm
  have hVC : V * C = 1 - V := by
    apply eq_sub_iff_add_eq.mpr
    simpa [mul_add, add_comm] using hV
  have hCV : C * V = 1 - V := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_mul, add_comm] using hVr
  rw [hUT]
  symm
  calc
    V * (1 + C * C) * U = V * U + (V * C) * (C * U) := by noncomm_ring
    _ = U + V - 1 := by rw [hVC, hCU]; noncomm_ring
    _ = 1 + C * U - C * V := by rw [hCU, hCV]; noncomm_ring
    _ = (1 + C * C) * W := resolvent_identity C U V W hU hV hW

/-- Positivity of the exact rational matrix, from the entry-square bound and
explicit inverse witnesses. This is the finite positivity step of conjecture 6. -/
theorem posDef_resolvent_of_frobenius (C U V W : Matrix n n ℝ)
    (hC : C.transpose = -C) (hF : (∑ i, ∑ j, C i j ^ 2) < 1)
    (hU : U * (1 - C) = 1) (hUr : (1 - C) * U = 1)
    (hV : V * (1 + C) = 1) (hVr : (1 + C) * V = 1)
    (hW : (1 - C * C) * W = 1) :
    ((1 + C * C) * W).PosDef := by
  rw [resolvent_eq_congruence C U V W hC hU hUr hV hVr hW]
  have hinj : Function.Injective U.mulVec := by
    apply Function.LeftInverse.injective (g := (1 - C).mulVec)
    intro x
    rw [Matrix.mulVec_mulVec, hUr, Matrix.one_mulVec]
  simpa using (posDef_one_add_square_of_frobenius C hC hF).conjTranspose_mul_mul_same hinj

/-- For every real skew matrix, `I-C²=I+CᵀC` is positive definite. -/
theorem posDef_one_sub_square (C : Matrix n n ℝ) (hC : C.transpose = -C) :
    (1 - C * C).PosDef := by
  have hh := Matrix.PosDef.one.add_posSemidef
    (Matrix.posSemidef_conjTranspose_mul_self C)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hC, neg_mul,
    sub_eq_add_neg] using hh

/-- No inverse witnesses are required: their existence follows from skewness.
This is positivity of the actual rational matrix used in the manuscript. -/
theorem posDef_resolvent (C : Matrix n n ℝ) (hC : C.transpose = -C)
    (hF : (∑ i, ∑ j, C i j ^ 2) < 1) :
    ((1 + C * C) * (1 - C * C)⁻¹).PosDef := by
  have hminus : (1 - C * C).PosDef := posDef_one_sub_square C hC
  have hdetplus : (1 + C).det ≠ 0 := by
    intro hz
    have hp := hminus.det_pos
    rw [det_one_sub_square C hC, hz] at hp
    norm_num at hp
  have hdetminus : (1 - C).det ≠ 0 := by
    rw [det_one_sub_eq_det_one_add C hC]
    exact hdetplus
  have huplus : IsUnit (1 + C).det := isUnit_iff_ne_zero.mpr hdetplus
  have huminus : IsUnit (1 - C).det := isUnit_iff_ne_zero.mpr hdetminus
  have husquare : IsUnit (1 - C * C).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hminus.isUnit
  exact posDef_resolvent_of_frobenius C (1 - C)⁻¹ (1 + C)⁻¹ (1 - C * C)⁻¹
    hC hF (Matrix.nonsing_inv_mul _ huminus) (Matrix.mul_nonsing_inv _ huminus)
    (Matrix.nonsing_inv_mul _ huplus) (Matrix.mul_nonsing_inv _ huplus)
    (Matrix.mul_nonsing_inv _ husquare)

end Wormald







