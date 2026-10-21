import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

/-! Exact polynomial restriction to two coordinate directions, including equal
directions. Partial derivatives commute with this affine substitution. -/

namespace Wormald

open MvPolynomial

noncomputable section

variable {σ R S : Type*} [DecidableEq σ] [CommRing R] [CommRing S]

def twoCoordinateSubstitution (z : σ → S) (j k : σ) (i : σ) :
    MvPolynomial (Fin 2) S :=
  C (z i) + (if i = j then X 0 else 0) + (if i = k then X 1 else 0)

theorem twoCoordinateSubstitution_pderiv_zero (z : σ → S) (j k i : σ) :
    pderiv 0 (twoCoordinateSubstitution z j k i) = if i = j then 1 else 0 := by
  unfold twoCoordinateSubstitution
  split_ifs <;> simp

theorem twoCoordinateSubstitution_pderiv_one (z : σ → S) (j k i : σ) :
    pderiv 1 (twoCoordinateSubstitution z j k i) = if i = k then 1 else 0 := by
  unfold twoCoordinateSubstitution
  split_ifs <;> simp

theorem pderiv_zero_twoCoordinate_eval₂ (f : R →+* S) (z : σ → S) (j k : σ)
    (K : MvPolynomial σ R) :
    pderiv 0 (eval₂ (C.comp f) (twoCoordinateSubstitution z j k) K) =
      eval₂ (C.comp f) (twoCoordinateSubstitution z j k) (pderiv j K) := by
  induction K using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    by_cases h : i = j <;>
      simp [hp, twoCoordinateSubstitution_pderiv_zero, pderiv_X, h]

theorem pderiv_one_twoCoordinate_eval₂ (f : R →+* S) (z : σ → S) (j k : σ)
    (K : MvPolynomial σ R) :
    pderiv 1 (eval₂ (C.comp f) (twoCoordinateSubstitution z j k) K) =
      eval₂ (C.comp f) (twoCoordinateSubstitution z j k) (pderiv k K) := by
  induction K using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    by_cases h : i = k <;>
      simp [hp, twoCoordinateSubstitution_pderiv_one, pderiv_X, h]

theorem eval_zero_twoCoordinate_eval₂ (f : R →+* S) (z : σ → S) (j k : σ)
    (K : MvPolynomial σ R) :
    eval (fun _ => 0) (eval₂ (C.comp f) (twoCoordinateSubstitution z j k) K) =
      eval₂ f z K := by
  induction K using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [eval₂_add, map_add, hp, hq]
  | mul_X p i hp =>
    simp only [eval₂_mul, eval₂_X, map_mul, hp]
    congr 1
    unfold twoCoordinateSubstitution
    split_ifs <;> simp

/-- Mixed partials of the full defining polynomial are exactly the mixed
coefficients of its two-variable affine restriction. -/
theorem eval_mixed_twoCoordinate_eval₂ (f : R →+* S) (z : σ → S) (j k : σ)
    (K : MvPolynomial σ R) :
    eval (fun _ => 0)
      (pderiv 1 (pderiv 0 (eval₂ (C.comp f) (twoCoordinateSubstitution z j k) K))) =
      eval₂ f z (pderiv k (pderiv j K)) := by
  rw [pderiv_zero_twoCoordinate_eval₂, pderiv_one_twoCoordinate_eval₂,
    eval_zero_twoCoordinate_eval₂]

end
end Wormald
