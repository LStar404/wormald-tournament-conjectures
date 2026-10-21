import Wormald.CyclicTripleBasics

namespace Wormald

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Closing a path changes only two triples. The closing-edge weight is at
most `2/n`, so the exact weighted cyclic tail is at most twice the uniform
initial open-path tail. -/
theorem Tournament.cyclicTriple_tail_le {n N : ℕ} (T : Tournament n)
    (hn : n ≠ 0) (hT : T.Regular) (ε : ℝ) (hε : 0 ≤ ε)
    (hscale : 4 ≤ ε * ((N + 3 : ℕ) : ℝ)) :
    (∑ f : Fin (N + 3) → Fin n,
      if ε * ((N + 3 : ℕ) : ℝ) ≤
        |(cyclicTripleCount f : ℝ) - ((N + 3 : ℕ) : ℝ) * (1 / (n : ℝ)) ^ 2|
      then FiniteModel.cyclicWordWeight T.realCriticalTransition f else 0) ≤
        8 * Real.exp (-ε ^ 2 * ((N + 1 : ℕ) : ℝ) / 8) := by
  let p : ℝ := 1 / (n : ℝ)
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hp1 : p ≤ 1 := (div_le_one (lt_of_lt_of_le zero_lt_one hnR)).mpr hnR
  have hweight (s : Fin n) (w : Fin (N + 2) → Fin n) :
      0 ≤ linearPathWeight T.realCriticalTransition s w :=
    Finset.prod_nonneg (fun _ _ => T.realCriticalTransition_nonneg _ _)
  have hcut (s : Fin n) (w : Fin (N + 2) → Fin n)
      (hbad : ε * ((N + 3 : ℕ) : ℝ) ≤
        |(cyclicTripleCount (Fin.cons s w) : ℝ) - ((N + 3 : ℕ) : ℝ) * p ^ 2|) :
      (ε / 2) * ((N + 2 : ℕ) : ℝ) ≤ |adjacentCenteredValue p (linearHoldingPattern s w)| := by
    have herr := cyclicTriple_centered_cut_error (Fin.cons s w) p hp0 hp1
    have hlin : ((linearTripleCount (Fin.cons s w) : ℝ) - ((N + 1 : ℕ) : ℝ) * p ^ 2) =
        adjacentCenteredValue p (linearHoldingPattern s w) := by
      simp [linearTripleCount, adjacentCenteredValue]
    rw [hlin] at herr
    have htri : |(cyclicTripleCount (Fin.cons s w) : ℝ) - ((N + 3 : ℕ) : ℝ) * p ^ 2| ≤
        2 + |adjacentCenteredValue p (linearHoldingPattern s w)| := by
      have hh := abs_sub_le ((cyclicTripleCount (Fin.cons s w) : ℝ) -
        ((N + 3 : ℕ) : ℝ) * p ^ 2) (adjacentCenteredValue p (linearHoldingPattern s w)) 0
      simp only [sub_zero] at hh
      linarith
    push_cast at hscale hbad htri ⊢
    nlinarith
  have hpoint (s : Fin n) (w : Fin (N + 2) → Fin n) :
      (if ε * ((N + 3 : ℕ) : ℝ) ≤
        |(cyclicTripleCount (Fin.cons s w) : ℝ) - ((N + 3 : ℕ) : ℝ) * p ^ 2|
      then FiniteModel.cyclicWordWeight T.realCriticalTransition (Fin.cons s w) else 0) ≤
      (2 / (n : ℝ)) *
        (if (ε / 2) * ((N + 2 : ℕ) : ℝ) ≤ |adjacentCenteredValue p (linearHoldingPattern s w)|
        then linearPathWeight T.realCriticalTransition s w else 0) := by
    by_cases hb : ε * ((N + 3 : ℕ) : ℝ) ≤
        |(cyclicTripleCount (Fin.cons s w) : ℝ) - ((N + 3 : ℕ) : ℝ) * p ^ 2|
    · rw [ite_eq_left hb, ite_eq_left (hcut s w hb)]
      exact T.cyclicWordWeight_cons_le s w
    · rw [ite_eq_right hb]
      apply mul_nonneg (by positivity)
      split_ifs <;> linarith [hweight s w]
  have hseed (s : Fin n) :
      (∑ w : Fin (N + 2) → Fin n,
        if ε * ((N + 3 : ℕ) : ℝ) ≤
          |(cyclicTripleCount (Fin.cons s w) : ℝ) - ((N + 3 : ℕ) : ℝ) * p ^ 2|
        then FiniteModel.cyclicWordWeight T.realCriticalTransition (Fin.cons s w) else 0) ≤
      (2 / (n : ℝ)) * (4 * Real.exp (-(ε / 2) ^ 2 * ((N + 1 : ℕ) : ℝ) / 2)) := by
    calc
      _ ≤ ∑ w : Fin (N + 2) → Fin n, (2 / (n : ℝ)) *
          (if (ε / 2) * ((N + 2 : ℕ) : ℝ) ≤ |adjacentCenteredValue p (linearHoldingPattern s w)|
          then linearPathWeight T.realCriticalTransition s w else 0) :=
        Finset.sum_le_sum (fun w _ => hpoint s w)
      _ = (2 / (n : ℝ)) * ∑ w : Fin (N + 2) → Fin n,
          (if (ε / 2) * ((N + 2 : ℕ) : ℝ) ≤ |adjacentCenteredValue p (linearHoldingPattern s w)|
          then linearPathWeight T.realCriticalTransition s w else 0) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (T.holding_adjacent_tail_le hn hT (N + 1) s (ε / 2) (by positivity)) (by positivity)
  calc
    _ = ∑ s : Fin n, ∑ w : Fin (N + 2) → Fin n,
        if ε * ((N + 3 : ℕ) : ℝ) ≤
          |(cyclicTripleCount (Fin.cons s w) : ℝ) - ((N + 3 : ℕ) : ℝ) * p ^ 2|
        then FiniteModel.cyclicWordWeight T.realCriticalTransition (Fin.cons s w) else 0 :=
      sum_fin_succ_function _
    _ ≤ ∑ _s : Fin n,
        (2 / (n : ℝ)) * (4 * Real.exp (-(ε / 2) ^ 2 * ((N + 1 : ℕ) : ℝ) / 2)) :=
      Finset.sum_le_sum (fun s _ => hseed s)
    _ = _ := by
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have he : -(ε / 2) ^ 2 * ((N + 1 : ℕ) : ℝ) / 2 =
          -ε ^ 2 * ((N + 1 : ℕ) : ℝ) / 8 := by ring
      rw [he]
      field_simp
      ring

end
end Wormald
