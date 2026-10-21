import Wormald.HoldingFlags
import Mathlib.Analysis.SpecialFunctions.Exp

namespace Wormald

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def finiteTailMass {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) (a : ℝ) : ℝ :=
  ∑ ω, if a ≤ X ω then w ω else 0

def finiteAbsTailMass {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) (a : ℝ) : ℝ :=
  ∑ ω, if a ≤ |X ω| then w ω else 0

/-- Chernoff's bound as a pointwise exponential comparison and a finite sum.
No measure-theoretic or independence assumption enters this inequality. -/
theorem finiteTailMass_chernoff {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (a t : ℝ) (ht : 0 ≤ t) :
    finiteTailMass w X a ≤ Real.exp (-t * a) * ∑ ω, w ω * Real.exp (t * X ω) := by
  have hpoint (ω : Ω) : (if a ≤ X ω then w ω else 0) ≤
      Real.exp (-t * a) * (w ω * Real.exp (t * X ω)) := by
    by_cases h : a ≤ X ω
    · simp only [ite_eq_left h]
      have he : 1 ≤ Real.exp (t * (X ω - a)) :=
        Real.one_le_exp_iff.mpr (mul_nonneg ht (sub_nonneg.mpr h))
      calc
        _ = w ω * 1 := by ring
        _ ≤ w ω * Real.exp (t * (X ω - a)) := mul_le_mul_of_nonneg_left he (hw ω)
        _ = _ := by rw [show t * (X ω - a) = -t * a + t * X ω by ring, Real.exp_add]; ring
    · simp only [ite_eq_right h]
      exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (hw ω) (Real.exp_nonneg _))
  exact (Finset.sum_le_sum (fun ω _ => hpoint ω)).trans_eq (Finset.mul_sum ..).symm

theorem finiteAbsTailMass_le_sum {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (a : ℝ) :
    finiteAbsTailMass w X a ≤ finiteTailMass w X a + finiteTailMass w (fun ω => -X ω) a := by
  unfold finiteAbsTailMass finiteTailMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  have hp : 0 ≤ if a ≤ X ω then w ω else 0 := by split_ifs <;> linarith [hw ω]
  have hn : 0 ≤ if a ≤ -X ω then w ω else 0 := by split_ifs <;> linarith [hw ω]
  by_cases ha : a ≤ |X ω|
  · simp only [ite_eq_left ha]
    rcases le_total 0 (X ω) with hX | hX
    · have h : a ≤ X ω := by simpa only [abs_of_nonneg hX] using ha
      simp only [ite_eq_left h]
      linarith
    · have h : a ≤ -X ω := by simpa only [abs_of_nonpos hX] using ha
      simp only [ite_eq_left h]
      linarith
  · simp only [ite_eq_right ha]
    exact add_nonneg hp hn

theorem finiteTailMass_antitone {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (a b : ℝ) (hab : a ≤ b) :
    finiteTailMass w X b ≤ finiteTailMass w X a := by
  apply Finset.sum_le_sum
  intro ω _
  by_cases hb : b ≤ X ω
  · simp only [ite_eq_left hb, ite_eq_left (hab.trans hb)]
    rfl
  · simp only [ite_eq_right hb]
    split_ifs <;> linarith [hw ω]

end
end Wormald
