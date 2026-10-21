import Wormald.CyclicTripleConcentration

namespace Wormald

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def balancedTripleTailMass {n L : ℕ} (T : Tournament n) (m : ℕ) (ε : ℝ) : ℝ :=
  ∑ f : Fin L → Fin n,
    if FiniteModel.BalancedBaseWord m f ∧
      ε * (L : ℝ) ≤ |(cyclicTripleCount f : ℝ) - (L : ℝ) * (1 / (n : ℝ)) ^ 2|
    then FiniteModel.cyclicWordWeight T.realCriticalTransition f else 0

theorem Tournament.cyclicTriple_tail_le_of_three_le {n L : ℕ} (T : Tournament n)
    (hn : n ≠ 0) (hT : T.Regular) (hL : 3 ≤ L) (ε : ℝ) (hε : 0 ≤ ε)
    (hscale : 4 ≤ ε * (L : ℝ)) :
    (∑ f : Fin L → Fin n,
      if ε * (L : ℝ) ≤ |(cyclicTripleCount f : ℝ) - (L : ℝ) * (1 / (n : ℝ)) ^ 2|
      then FiniteModel.cyclicWordWeight T.realCriticalTransition f else 0) ≤
        8 * Real.exp (-ε ^ 2 * ((L - 2 : ℕ) : ℝ) / 8) := by
  obtain ⟨N, hN⟩ := Nat.exists_eq_add_of_le hL
  rcases (show L = N + 3 by omega) with rfl
  have hh := T.cyclicTriple_tail_le (N := N) hn hT ε hε hscale
  simpa only [show N + 3 - 2 = N + 1 by omega] using hh

/-- Restricting to balanced words can only decrease the nonnegative bad mass.
The denominator for conditioning is deliberately kept separate and explicit. -/
theorem Tournament.balancedTripleTailMass_le {n L : ℕ} (T : Tournament n)
    (hn : n ≠ 0) (hT : T.Regular) (hL : 3 ≤ L) (m : ℕ)
    (ε : ℝ) (hε : 0 ≤ ε) (hscale : 4 ≤ ε * (L : ℝ)) :
    balancedTripleTailMass (L := L) T m ε ≤ 8 * Real.exp (-ε ^ 2 * ((L - 2 : ℕ) : ℝ) / 8) := by
  apply le_trans _ (T.cyclicTriple_tail_le_of_three_le hn hT hL ε hε hscale)
  apply Finset.sum_le_sum
  intro f _
  have hw : 0 ≤ FiniteModel.cyclicWordWeight T.realCriticalTransition f :=
    Finset.prod_nonneg (fun _ _ => T.realCriticalTransition_nonneg _ _)
  by_cases hb : FiniteModel.BalancedBaseWord m f
  · simp only [hb, true_and]
    rfl
  · simp only [hb, false_and, ite_false]
    split_ifs <;> linarith

theorem Tournament.balancedTripleTailFraction_le {n L : ℕ} (T : Tournament n)
    (hn : n ≠ 0) (hT : T.Regular) (hL : 3 ≤ L) (m : ℕ)
    (ε : ℝ) (hε : 0 ≤ ε) (hscale : 4 ≤ ε * (L : ℝ))
    (hden : 0 < FiniteModel.balancedCycleWordSum (N := L) T.realCriticalTransition m) :
    balancedTripleTailMass (L := L) T m ε /
        FiniteModel.balancedCycleWordSum (N := L) T.realCriticalTransition m ≤
      (8 * Real.exp (-ε ^ 2 * ((L - 2 : ℕ) : ℝ) / 8)) /
        FiniteModel.balancedCycleWordSum (N := L) T.realCriticalTransition m :=
  div_le_div_of_nonneg_right (T.balancedTripleTailMass_le hn hT hL m ε hε hscale) hden.le

end
end Wormald
