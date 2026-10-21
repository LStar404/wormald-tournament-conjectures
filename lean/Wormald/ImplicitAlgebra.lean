import Wormald.AnalyticTarget
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-! Finite coordinate sums in the genuine implicit second derivative. -/

namespace Wormald
open scoped BigOperators
open Matrix

theorem implicit_first_tangent_sum {n : ℕ} (z : ℂ) (j : Fin n)
    (f : Fin (n + 1) → ℂ) :
    (∑ a, f a * appendLast (fun b => if b = j then Complex.I * z else 0)
      (-Complex.I * z) a) =
      Complex.I * z * (f j.castSucc - f (Fin.last n)) := by
  rw [Fin.sum_univ_castSucc]
  simp [appendLast, mul_ite]
  ring

theorem implicit_second_tangent_sum {n : ℕ} (z : ℂ) (j k : Fin n)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (∑ a, (∑ b, M a b *
        appendLast (fun c => if c = k then Complex.I * z else 0) (-Complex.I * z) b) *
      appendLast (fun c => if c = j then Complex.I * z else 0) (-Complex.I * z) a) =
      -z ^ 2 * (M j.castSucc k.castSucc - M j.castSucc (Fin.last n) -
        M (Fin.last n) k.castSucc + M (Fin.last n) (Fin.last n)) := by
  simp only [implicit_first_tangent_sum]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem implicit_acceleration_sum {n : ℕ} (r z u : ℂ) (j k : Fin n) :
    (∑ a, r * appendLast (fun b => if b = j ∧ b = k then -z else 0) u a) =
      r * (u - if j = k then z else 0) := by
  rw [Fin.sum_univ_castSucc]
  by_cases h : j = k
  · subst k
    simp [appendLast, mul_ite]
    ring
  · have hempty (b : Fin n) : ¬(b = j ∧ b = k) := by
      rintro ⟨rfl, rfl⟩
      exact h rfl
    simp [appendLast, hempty, h]

end Wormald
