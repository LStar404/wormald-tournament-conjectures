import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

/-!
The objects here use the manuscript's adjacency convention: A i j = 1 means i → j.
The polynomial K is Wormald's actual defining determinant, not a free Hessian.
`angularHessianJet` is the implicit second-derivative formula. Its correspondence
with the actual logarithmic angular Hessian is proved in `AnalyticJetBridge` and
`ConjectureSixProof`; no theorem below silently assumes that correspondence.
-/

namespace Wormald

noncomputable section

open Matrix MvPolynomial

structure Tournament (n : ℕ) where
  adjacency : Matrix (Fin n) (Fin n) ℚ
  diagonal : ∀ i, adjacency i i = 0
  zero_or_one : ∀ i j, adjacency i j = 0 ∨ adjacency i j = 1
  orientation : ∀ i j, i ≠ j → adjacency i j + adjacency j i = 1

def Tournament.Regular {n : ℕ} (T : Tournament n) : Prop :=
  ∀ i, ∑ j, T.adjacency i j = ((n : ℚ) - 1) / 2

def Tournament.sign {n : ℕ} (T : Tournament n) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => 2 * T.adjacency i j + (if i = j then 1 else 0) - 1

theorem Tournament.sign_skew {n : ℕ} (T : Tournament n) :
    T.sign.transpose = -T.sign := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [Tournament.sign, T.diagonal]
  · have ho := T.orientation i j h
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Tournament.sign,
      ite_eq_right h, ite_eq_right (Ne.symm h)]
    linarith

theorem Tournament.sign_row_sum {n : ℕ} (T : Tournament n) (hT : T.Regular)
    (i : Fin n) : ∑ j, T.sign i j = 0 := by
  simp only [Tournament.sign, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  simp [hT i]
  ring

theorem Tournament.sign_entry_square {n : ℕ} (T : Tournament n) (i j : Fin n) :
    T.sign i j ^ 2 = 1 - (if i = j then 1 else 0) := by
  by_cases h : i = j
  · subst j
    simp [Tournament.sign, T.diagonal]
  · rcases T.zero_or_one i j with hzero | hone
    · norm_num [Tournament.sign, h, hzero]
    · norm_num [Tournament.sign, h, hone]

theorem Tournament.sign_row_energy {n : ℕ} (T : Tournament n) (i : Fin n) :
    ∑ j, T.sign i j ^ 2 = (n : ℚ) - 1 := by
  simp only [T.sign_entry_square, Finset.sum_sub_distrib]
  simp

def Tournament.normalizedSign {n : ℕ} (T : Tournament n) :
    Matrix (Fin n) (Fin n) ℚ := fun i j => T.sign i j / (n : ℚ)

/-- This estimate does not require regularity. -/
theorem Tournament.normalizedSign_energy {n : ℕ} (T : Tournament n) (hn : n ≠ 0) :
    ∑ i, ∑ j, T.normalizedSign i j ^ 2 = ((n : ℚ) - 1) / (n : ℚ) := by
  simp only [Tournament.normalizedSign, div_pow, ← Finset.sum_div,
    T.sign_row_energy, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  field_simp

def definingMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) ℚ) :=
  fun i j => (if i = j then 1 else 0) -
    C (A i j + if i = j then (1 / 2 : ℚ) else 0) * X j

def definingPolynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    MvPolynomial (Fin n) ℚ := (definingMatrix A).det

def firstLogJet {n : ℕ} (K : MvPolynomial (Fin n) ℚ) (z : ℚ) (j : Fin n) : ℚ :=
  z * eval (fun _ => z) (pderiv j K)

def secondLogJet {n : ℕ} (K : MvPolynomial (Fin n) ℚ) (z : ℚ)
    (j k : Fin n) : ℚ :=
  z ^ 2 * eval (fun _ => z) (pderiv k (pderiv j K)) +
    (if j = k then firstLogJet K z j else 0)

/-- The implicit second jet, in logarithmic variables, with pivot coordinate p.
It is intended only when K(z,…,z)=0 and all first log jets equal a nonzero value.
Those conditions are explicit in applications; division is total in Lean. -/
def angularHessianJet {n : ℕ} (K : MvPolynomial (Fin n) ℚ) (z : ℚ)
    (p j k : Fin n) : ℚ :=
  (secondLogJet K z j k - secondLogJet K z j p -
    secondLogJet K z p k + secondLogJet K z p p) / firstLogJet K z p

end
end Wormald
