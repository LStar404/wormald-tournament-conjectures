import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Iterated midpoint domination for a finite Boolean cube. The only analytic
input is the actual one-coordinate midpoint inequality on the unit cube. -/

open scoped BigOperators

namespace Wormald

noncomputable section

private def centeredCubePoint {K : Type*} [DecidableEq K]
    (S : Finset K) (b : K → Bool) : K → ℝ :=
  fun k => if k ∈ S then 1 / 2 else if b k then 1 else 0

private def boolCubeFlip {K : Type*} [DecidableEq K] (k : K) (b : K → Bool) : K → Bool :=
  Function.update b k (!b k)

private theorem boolCubeFlip_involutive {K : Type*} [DecidableEq K] (k : K) :
    Function.Involutive (boolCubeFlip k) := by
  intro b
  funext a
  by_cases h : a = k
  · subst a
    simp [boolCubeFlip]
  · simp [boolCubeFlip, h]

private theorem centeredCubePoint_mem {K : Type*} [DecidableEq K]
    (S : Finset K) (b : K → Bool) :
    ∀ k, 0 ≤ centeredCubePoint S b k ∧ centeredCubePoint S b k ≤ 1 := by
  intro k
  by_cases h : k ∈ S <;> cases hb : b k <;> norm_num [centeredCubePoint, h, hb]

private theorem centeredCubePoint_update {K : Type*} [DecidableEq K]
    (S : Finset K) (k : K) (hk : k ∉ S) (b : K → Bool) (a : Bool) :
    centeredCubePoint S (Function.update b k a) =
      Function.update (centeredCubePoint S b) k (if a then 1 else 0) := by
  funext j
  by_cases hj : j = k
  · subst j
    simp [centeredCubePoint, hk]
  · simp [centeredCubePoint, hj]

private theorem centeredCubePoint_insert {K : Type*} [DecidableEq K]
    (S : Finset K) (k : K) (_hk : k ∉ S) (b : K → Bool) :
    centeredCubePoint (insert k S) b =
      Function.update (centeredCubePoint S b) k (1 / 2) := by
  funext j
  by_cases hj : j = k
  · subst j
    simp [centeredCubePoint]
  · simp [centeredCubePoint, hj]

private theorem centeredCube_sum_step {K : Type*} [Fintype K] [DecidableEq K]
    (F : (K → ℝ) → ℝ)
    (hF : ∀ p : K → ℝ, (∀ a, 0 ≤ p a ∧ p a ≤ 1) → ∀ k : K,
      (F (Function.update p k 0) + F (Function.update p k 1)) / 2 ≤
        F (Function.update p k (1 / 2)))
    (S : Finset K) (k : K) (hk : k ∉ S) :
    (∑ b : K → Bool, F (centeredCubePoint S b)) ≤
      ∑ b : K → Bool, F (centeredCubePoint (insert k S) b) := by
  have hpair (b : K → Bool) :
      F (centeredCubePoint S b) + F (centeredCubePoint S (boolCubeFlip k b)) ≤
        2 * F (centeredCubePoint (insert k S) b) := by
    have hm := hF (centeredCubePoint S b) (centeredCubePoint_mem S b) k
    have hzero : centeredCubePoint S (Function.update b k false) =
        Function.update (centeredCubePoint S b) k 0 := by
      simpa only [ite_eq_right (by decide : (false : Bool) ≠ true)] using
        centeredCubePoint_update S k hk b false
    have hone : centeredCubePoint S (Function.update b k true) =
        Function.update (centeredCubePoint S b) k 1 := by
      simpa only [↓reduceIte] using centeredCubePoint_update S k hk b true
    rw [← hzero, ← hone, ← centeredCubePoint_insert S k hk b] at hm
    have hself : Function.update b k (b k) = b := Function.update_eq_self k b
    cases hb : b k
    · rw [hb] at hself
      simp only [hself] at hm
      have hflip : boolCubeFlip k b = Function.update b k true := by simp [boolCubeFlip, hb]
      rw [hflip]
      linarith
    · rw [hb] at hself
      simp only [hself] at hm
      have hflip : boolCubeFlip k b = Function.update b k false := by simp [boolCubeFlip, hb]
      rw [hflip]
      linarith
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hpair b)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hflipSum :
      (∑ b : K → Bool, F (centeredCubePoint S (boolCubeFlip k b))) =
        ∑ b : K → Bool, F (centeredCubePoint S b) := by
    simpa only [Function.Involutive.coe_toPerm] using
      Equiv.sum_comp (Function.Involutive.toPerm (boolCubeFlip k) (boolCubeFlip_involutive k))
        (fun b => F (centeredCubePoint S b))
  rw [hflipSum] at hsum
  linarith

/-- The finite-sum form of separate midpoint domination. This proof performs
one coordinate-centering step at a time and retains the true cube hypotheses. -/
theorem boolCube_sum_le_card_midpoint {K : Type*} [Fintype K] [DecidableEq K]
    (F : (K → ℝ) → ℝ)
    (hF : ∀ p : K → ℝ, (∀ a, 0 ≤ p a ∧ p a ≤ 1) → ∀ k : K,
      (F (Function.update p k 0) + F (Function.update p k 1)) / 2 ≤
        F (Function.update p k (1 / 2))) :
    (∑ b : K → Bool, F (fun k => if b k then 1 else 0)) ≤
      (Fintype.card (K → Bool) : ℝ) * F (fun _ => 1 / 2) := by
  have hcenter (S : Finset K) :
      (∑ b : K → Bool, F (centeredCubePoint ∅ b)) ≤
        ∑ b : K → Bool, F (centeredCubePoint S b) := by
    induction S using Finset.induction_on with
    | empty => exact le_refl _
    | @insert k S hk ih => exact ih.trans (centeredCube_sum_step F hF S k hk)
  have hempty (b : K → Bool) : centeredCubePoint ∅ b =
      (fun k => if b k then 1 else 0) := by
    funext k
    simp [centeredCubePoint]
  have huniv (b : K → Bool) : centeredCubePoint Finset.univ b = (fun _ => 1 / 2) := by
    funext k
    simp [centeredCubePoint]
  simpa only [hempty, huniv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    hcenter Finset.univ

/-- The actual uniform Boolean-cube average is at most the all-midpoint value. -/
theorem boolCube_average_le_midpoint {K : Type*} [Fintype K] [DecidableEq K]
    (F : (K → ℝ) → ℝ)
    (hF : ∀ p : K → ℝ, (∀ a, 0 ≤ p a ∧ p a ≤ 1) → ∀ k : K,
      (F (Function.update p k 0) + F (Function.update p k 1)) / 2 ≤
        F (Function.update p k (1 / 2))) :
    (∑ b : K → Bool, F (fun k => if b k then 1 else 0)) /
      (Fintype.card (K → Bool) : ℝ) ≤ F (fun _ => 1 / 2) := by
  have hcard : (0 : ℝ) < Fintype.card (K → Bool) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (K → Bool))
  apply (div_le_iff₀ hcard).mpr
  simpa only [mul_comm] using boolCube_sum_le_card_midpoint F hF

end
end Wormald
